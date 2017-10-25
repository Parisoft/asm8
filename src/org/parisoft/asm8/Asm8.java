package org.parisoft.asm8;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.BiConsumer;
import java.util.regex.Pattern;

import static org.parisoft.asm8.Asm8.Label.Type.EQUATE;
import static org.parisoft.asm8.Asm8.Label.Type.LABEL;
import static org.parisoft.asm8.Asm8.Label.Type.MACRO;
import static org.parisoft.asm8.Asm8.Label.Type.RESERVED;
import static org.parisoft.asm8.Asm8.Label.Type.VALUE;
import static org.parisoft.asm8.Asm8.OpTypes.ABS;
import static org.parisoft.asm8.Asm8.OpTypes.ABSX;
import static org.parisoft.asm8.Asm8.OpTypes.ABSY;
import static org.parisoft.asm8.Asm8.OpTypes.ACC;
import static org.parisoft.asm8.Asm8.OpTypes.IMM;
import static org.parisoft.asm8.Asm8.OpTypes.IMP;
import static org.parisoft.asm8.Asm8.OpTypes.IND;
import static org.parisoft.asm8.Asm8.OpTypes.INDX;
import static org.parisoft.asm8.Asm8.OpTypes.INDY;
import static org.parisoft.asm8.Asm8.OpTypes.REL;
import static org.parisoft.asm8.Asm8.OpTypes.ZP;
import static org.parisoft.asm8.Asm8.OpTypes.ZPX;
import static org.parisoft.asm8.Asm8.OpTypes.ZPY;
import static org.parisoft.asm8.Asm8.Operator.Precedence.ANDANDP;
import static org.parisoft.asm8.Asm8.Operator.Precedence.ANDP;
import static org.parisoft.asm8.Asm8.Operator.Precedence.COMPARE;
import static org.parisoft.asm8.Asm8.Operator.Precedence.EQCOMPARE;
import static org.parisoft.asm8.Asm8.Operator.Precedence.MULDIV;
import static org.parisoft.asm8.Asm8.Operator.Precedence.ORORP;
import static org.parisoft.asm8.Asm8.Operator.Precedence.ORP;
import static org.parisoft.asm8.Asm8.Operator.Precedence.PLUSMINUS;
import static org.parisoft.asm8.Asm8.Operator.Precedence.SHIFT;
import static org.parisoft.asm8.Asm8.Operator.Precedence.UNARY;
import static org.parisoft.asm8.Asm8.Operator.Precedence.WHOLEEXP;
import static org.parisoft.asm8.Asm8.Operator.Precedence.XORP;

public class Asm8 {

    private static final String VERSION = "1.0";

    private static final int NOORIGIN = -0x40000000;//nice even number so aligning works before origin is defined
    private static final int INITLISTSIZE = 128;//initial label list size
    private static final int BUFFSIZE = 8192;//file buffer (inputbuff, outputbuff) size
    private static final int WORDMAX = 128;     //used with getword()
    private static final int LINEMAX = 2048;//plenty of room for nested equates
    private static final int MAXPASSES = 7;//# of tries before giving up
    private static final int IFNESTS = 32;//max nested IF levels
    private static final int DEFAULTFILLER = 0; //default fill value
    private static final int LOCALCHAR = '@';
    private static final List<Character> whiteSpaceChars = Arrays.asList(' ', '\t', '\r', '\n', ':');
    private static final Pattern whiteSpaceRegex = Pattern.compile("\\s|:");
    private static final Pattern mathRegex = Pattern.compile("!|^|&|\\||\\+|-|\\*|/|%|\\(|\\)|<|>|=|,");

    enum OpTypes {
        ACC(0, (char)0, "A"),
        IMM(1, '#', ""),
        IND(2, '(', ")"),
        INDX(1, '(', ",X)"),
        INDY(1, '(', "),Y"),
        ZPX,
        ZPY,
        ABSX,
        ABSY,
        ZP,
        ABS,
        REL,
        IMP;
        int size;
        char head;
        String tail;

        OpTypes(int size, char head, String tail) {
            this.size = size;
            this.head = head;
            this.tail = tail;
        }
    }

    private static final int[] opSize =    {0,   1,   2,    1,    1,     1,     1,    2,    2,   1, 2, 1, 0};
    private static final char[] opHead =   {0,  '#', '(', '(',  '(',     0,     0,    0,    0,   0, 0, 0, 0};
    private static final String[] opTail = {"A", "", ")", ",X)", "),Y", ",X", ",Y", ",X", ",Y", "", "", "", ""};

    enum Operator {
        NOOP(WHOLEEXP),
        EQUAL(EQCOMPARE),
        NOTEQUAL(EQCOMPARE),
        GREATER(COMPARE),
        GREATEREQ(COMPARE),
        LESS(COMPARE),
        LESSEQ(COMPARE),
        PLUS(PLUSMINUS),
        MINUS(PLUSMINUS),
        MUL(MULDIV),
        DIV(MULDIV),
        MOD(MULDIV),
        AND(ANDP),
        XOR(XORP),
        OR(ORP),
        ANDAND(ANDANDP),
        OROR(ORORP),
        LEFTSHIFT(SHIFT),
        RIGHTSHIFT(SHIFT);

        enum Precedence {WHOLEEXP, ORORP, ANDANDP, ORP, XORP, ANDP, EQCOMPARE, COMPARE, SHIFT, PLUSMINUS, MULDIV, UNARY}

        Precedence precedence;

        Operator(Precedence precedence) {
            this.precedence = precedence;
        }
    }

    static class Label {

        enum Type {
            LABEL, VALUE, EQUATE, MACRO, RESERVED
        }

        public Label(String name, Object value, Object line, Type type) {
            this.name = name;
            this.value = value;
            this.line = line;
            this.type = type;
        }

        public Label(String name, Object value, Type type) {
            this.name = name;
            this.value = value;
            this.type = type;
        }

        String name;
        Object value;
        Object line;
        Type type;
        boolean used = false;
        int pass = 0;
        int scope = 0;
    }

    private final BiConsumer<Label, StringBuilder> directiveNothing = this::nothing;
    private final BiConsumer<Label, StringBuilder> directiveIf = this::_if;
    private final BiConsumer<Label, StringBuilder> directiveElseIf = this::elseif;
    private final BiConsumer<Label, StringBuilder> directiveElse = this::_else;
    private final BiConsumer<Label, StringBuilder> directiveEndIf = this::endif;
    private final BiConsumer<Label, StringBuilder> directiveIfDef = this::ifdef;
    private final BiConsumer<Label, StringBuilder> directiveIfNDef = this::ifndef;
    private final BiConsumer<Label, StringBuilder> directiveEqual = this::equal;
    private final BiConsumer<Label, StringBuilder> directiveEqu = this::equ;
    private final BiConsumer<Label, StringBuilder> directiveOrg = this::org;
    private final BiConsumer<Label, StringBuilder> directiveBase = this::base;
    private final BiConsumer<Label, StringBuilder> directivePad = this::pad;
    private final BiConsumer<Label, StringBuilder> directiveInclude = this::include;
    private final BiConsumer<Label, StringBuilder> directiveIncBin = this::incbin;
    private final BiConsumer<Label, StringBuilder> directiveHex = this::hex;
    private final BiConsumer<Label, StringBuilder> directiveDw = this::dw;
    private final BiConsumer<Label, StringBuilder> directiveDb = this::db;
    private final BiConsumer<Label, StringBuilder> directiveDsw = this::dsw;
    private final BiConsumer<Label, StringBuilder> directiveDsb = this::dsb;
    private final BiConsumer<Label, StringBuilder> directiveAlign = this::align;
    private final BiConsumer<Label, StringBuilder> directiveMacro = this::macro;
    private final BiConsumer<Label, StringBuilder> directiveRept = this::rept;
    private final BiConsumer<Label, StringBuilder> directiveEndM = this::endm;
    private final BiConsumer<Label, StringBuilder> directiveEndR = this::endr;
    private final BiConsumer<Label, StringBuilder> directiveEnum = this::_enum;
    private final BiConsumer<Label, StringBuilder> directiveEndE = this::ende;
    private final BiConsumer<Label, StringBuilder> directiveFillValue = this::fillval;
    private final BiConsumer<Label, StringBuilder> directiveDl = this::dl;
    private final BiConsumer<Label, StringBuilder> directiveDh = this::dh;
    private final BiConsumer<Label, StringBuilder> directiveError = this::makeError;

    private int pass = 0;
    private int scope = 0;
    private int nextScope;
    private boolean lastChance = false;
    private boolean needAnotherPass = false;
    private boolean[] skipLine = new boolean[IFNESTS];
    private int defaultFiller;
    private final Map<String, List<Label>> labelMap = new HashMap<>();
    private Label firstLabel = new Label("$", 0, Boolean.TRUE, VALUE);
    private Label lastLabel;
    private Label labelHere;
    private int nestedIncludes = 0;
    private int ifLevel = 0;
    private int reptCount = 0;
    private Object makeMacro = null;
    private boolean noOutput = false;
    private int insideMacro = 0;
    private boolean verboseListing = false;
    private String listFileName;
    private String inputFileName;
    private String outputFileName;
    private boolean verbose = true;
    private int dependant;

    public static void main(String[] args) {
        if (args.length < 1) {
            showHelp();
            System.exit(1);
        }

        Asm8 asm8 = new Asm8();
        asm8.initLabels();

        int notOption = 0;

        for (int i = 0; i < args.length; i++) {
            if (args[i].startsWith("-") || args[i].startsWith("/")) {
                switch (args[i].charAt(1)) {
                    case 'h':
                    case '?':
                        showHelp();
                        System.exit(0);
                    case 'L':
                        asm8.verboseListing = true;
                    case 'l':
                        asm8.listFileName = "";
                        break;
                    case 'q':
                        asm8.verbose = false;
                        break;
                    default:
                        System.err.println("Error: unknown option: " + args[i]);
                        System.exit(0);
                }
            } else {
                if (notOption == 0) {
                    asm8.inputFileName = args[i];
                } else if (notOption == 1) {
                    asm8.outputFileName = args[i];
                } else if (notOption == 2) {
                    asm8.listFileName = args[i];
                } else {
                    System.err.println("Error: unused argument: " + args[i]);
                    System.exit(0);
                }
            }
        }

        if (asm8.inputFileName == null) {
            System.err.println("Error: No source file specified.");
            System.exit(0);
        }

        if (asm8.outputFileName == null) {
            asm8.outputFileName = asm8.inputFileName.substring(0, asm8.inputFileName.lastIndexOf('.')).concat(".bin");
        }

        if (asm8.listFileName != null && asm8.listFileName.isEmpty()) {
            asm8.listFileName = asm8.inputFileName.substring(0, asm8.inputFileName.lastIndexOf('.')).concat(".lst");
        }

        try {
            asm8.compile();
        } catch (Exception e) {
            System.err.println(e.getMessage());
        }
    }

    private static void showHelp() {
        System.out.println();
        System.out.println("asm8 " + VERSION);
        System.out.println("Usage:  asm8 [-options] sourcefile [outputfile] [listfile]");
        System.out.println("    -?          show this help");
        System.out.println("    -l          create listing");
        System.out.println("    -L          create verbose listing (expand REPT, MACRO)");
        System.out.println("    -d<name>    define symbol");
        System.out.println("    -q          quiet mode (no output unless error)");
        System.out.println("See README.TXT for more info.");
    }

    public void compile() {
        initLabels();

        Label currLabel = null;

        do {
            pass++;

            if (pass == MAXPASSES || (currLabel != null && currLabel.equals(lastLabel))) {
                lastChance = true;
                System.out.println("last try..");
            } else {
                System.out.printf("pass %s..\n", pass);
            }

            needAnotherPass = false;
            skipLine[0] = false;
            scope = 1;
            nextScope = 2;
            defaultFiller = DEFAULTFILLER;
            firstLabel.value = NOORIGIN;
            currLabel = lastLabel;

            include(null, new StringBuilder(inputFileName));
        }
        while (!lastChance && needAnotherPass);
    }

    private void initLabels() {
        BiConsumer<Label, StringBuilder> opcode = (o, o2) -> opcode(o, o2);
        labelMap.computeIfAbsent("BRK", s -> new ArrayList<>()).add(new Label("BRK", opcode, new Object[]{0x00, IMM, 0x00, ZP, 0x00, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("PHP", s -> new ArrayList<>()).add(new Label("PHP", opcode, new Object[]{0x08, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BPL", s -> new ArrayList<>()).add(new Label("BPL", opcode, new Object[]{0x10, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("CLC", s -> new ArrayList<>()).add(new Label("CLC", opcode, new Object[]{0x18, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("JSR", s -> new ArrayList<>()).add(new Label("JSR", opcode, new Object[]{0x20, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("BIT", s -> new ArrayList<>()).add(new Label("BIT", opcode, new Object[]{0x24, ZP, 0x2c, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("PLP", s -> new ArrayList<>()).add(new Label("PLP", opcode, new Object[]{0x28, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BMI", s -> new ArrayList<>()).add(new Label("BMI", opcode, new Object[]{0x30, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("SEC", s -> new ArrayList<>()).add(new Label("SEC", opcode, new Object[]{0x38, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("RTI", s -> new ArrayList<>()).add(new Label("RTI", opcode, new Object[]{0x40, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("PHA", s -> new ArrayList<>()).add(new Label("PHA", opcode, new Object[]{0x48, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("JMP", s -> new ArrayList<>()).add(new Label("JMP", opcode, new Object[]{0x6c, IND, 0x4c, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("BVC", s -> new ArrayList<>()).add(new Label("BVC", opcode, new Object[]{0x50, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("CLI", s -> new ArrayList<>()).add(new Label("CLI", opcode, new Object[]{0x58, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("RTS", s -> new ArrayList<>()).add(new Label("RTS", opcode, new Object[]{0x60, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("PLA", s -> new ArrayList<>()).add(new Label("PLA", opcode, new Object[]{0x68, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BVS", s -> new ArrayList<>()).add(new Label("BVS", opcode, new Object[]{0x70, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("SEI", s -> new ArrayList<>()).add(new Label("SEI", opcode, new Object[]{0x78, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("STY", s -> new ArrayList<>()).add(new Label("STY", opcode, new Object[]{0x94, ZPX, 0x84, ZP, 0x8c, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("STX", s -> new ArrayList<>()).add(new Label("STX", opcode, new Object[]{0x96, ZPY, 0x86, ZP, 0x8e, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("DEY", s -> new ArrayList<>()).add(new Label("DEY", opcode, new Object[]{0x88, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("TXA", s -> new ArrayList<>()).add(new Label("TXA", opcode, new Object[]{0x8a, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BCC", s -> new ArrayList<>()).add(new Label("BCC", opcode, new Object[]{0x90, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("TYA", s -> new ArrayList<>()).add(new Label("TYA", opcode, new Object[]{0x98, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("TXS", s -> new ArrayList<>()).add(new Label("TXS", opcode, new Object[]{0x9a, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("TAY", s -> new ArrayList<>()).add(new Label("TAY", opcode, new Object[]{0xa8, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("TAX", s -> new ArrayList<>()).add(new Label("TAX", opcode, new Object[]{0xaa, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BCS", s -> new ArrayList<>()).add(new Label("BCS", opcode, new Object[]{0xb0, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("CLV", s -> new ArrayList<>()).add(new Label("CLV", opcode, new Object[]{0xb8, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("TSX", s -> new ArrayList<>()).add(new Label("TSX", opcode, new Object[]{0xba, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("CPY", s -> new ArrayList<>()).add(new Label("CPY", opcode, new Object[]{0xc0, IMM, 0xc4, ZP, 0xcc, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("DEC", s -> new ArrayList<>()).add(new Label("DEC", opcode, new Object[]{0xd6, ZPX, 0xde, ABSX, 0xc6, ZP, 0xce, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("INY", s -> new ArrayList<>()).add(new Label("INY", opcode, new Object[]{0xc8, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("DEX", s -> new ArrayList<>()).add(new Label("DEX", opcode, new Object[]{0xca, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BNE", s -> new ArrayList<>()).add(new Label("BNE", opcode, new Object[]{0xd0, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("CLD", s -> new ArrayList<>()).add(new Label("CLD", opcode, new Object[]{0xd8, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("CPX", s -> new ArrayList<>()).add(new Label("CPX", opcode, new Object[]{0xe0, IMM, 0xe4, ZP, 0xec, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("INC", s -> new ArrayList<>()).add(new Label("INC", opcode, new Object[]{0xf6, ZPX, 0xfe, ABSX, 0xe6, ZP, 0xee, ABS, -1}, RESERVED));
        labelMap.computeIfAbsent("INX", s -> new ArrayList<>()).add(new Label("INX", opcode, new Object[]{0xe8, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("NOP", s -> new ArrayList<>()).add(new Label("NOP", opcode, new Object[]{0xea, IMP, -1}, RESERVED));
        labelMap.computeIfAbsent("BEQ", s -> new ArrayList<>()).add(new Label("BEQ", opcode, new Object[]{0xf0, REL, -1}, RESERVED));
        labelMap.computeIfAbsent("LDY", s -> new ArrayList<>()).add(new Label("LDY",
                                                                              opcode,
                                                                              new Object[]{0xa0, IMM, 0xb4, ZPX, 0xbc, ABSX, 0xa4, ZP, 0xac, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("LDX", s -> new ArrayList<>()).add(new Label("LDX",
                                                                              opcode,
                                                                              new Object[]{0xa2, IMM, 0xb6, ZPY, 0xbe, ABSY, 0xa6, ZP, 0xae, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("ORA", s -> new ArrayList<>()).add(new Label("ORA",
                                                                              opcode,
                                                                              new Object[]{0x09, IMM, 0x01, INDX, 0x11, INDY, 0x15, ZPX, 0x1d, ABSX, 0x19, ABSY, 0x05, ZP, 0x0d, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("ASL", s -> new ArrayList<>()).add(new Label("ASL",
                                                                              opcode,
                                                                              new Object[]{0x0a, ACC, 0x16, ZPX, 0x1e, ABSX, 0x06, ZP, 0x0e, ABS, 0x0a, IMP, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("AND", s -> new ArrayList<>()).add(new Label("AND",
                                                                              opcode,
                                                                              new Object[]{0x29, IMM, 0x21, INDX, 0x31, INDY, 0x35, ZPX, 0x3d, ABSX, 0x39, ABSY, 0x25, ZP, 0x2d, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("ROL", s -> new ArrayList<>()).add(new Label("ROL",
                                                                              opcode,
                                                                              new Object[]{0x2a, ACC, 0x36, ZPX, 0x3e, ABSX, 0x26, ZP, 0x2e, ABS, 0x2a, IMP, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("EOR", s -> new ArrayList<>()).add(new Label("EOR",
                                                                              opcode,
                                                                              new Object[]{0x49, IMM, 0x41, INDX, 0x51, INDY, 0x55, ZPX, 0x5d, ABSX, 0x59, ABSY, 0x45, ZP, 0x4d, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("LSR", s -> new ArrayList<>()).add(new Label("LSR",
                                                                              opcode,
                                                                              new Object[]{0x4a, ACC, 0x56, ZPX, 0x5e, ABSX, 0x46, ZP, 0x4e, ABS, 0x4a, IMP, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("ADC", s -> new ArrayList<>()).add(new Label("ADC",
                                                                              opcode,
                                                                              new Object[]{0x69, IMM, 0x61, INDX, 0x71, INDY, 0x75, ZPX, 0x7d, ABSX, 0x79, ABSY, 0x65, ZP, 0x6d, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("ROR", s -> new ArrayList<>()).add(new Label("ROR",
                                                                              opcode,
                                                                              new Object[]{0x6a, ACC, 0x76, ZPX, 0x7e, ABSX, 0x66, ZP, 0x6e, ABS, 0x6a, IMP, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("STA", s -> new ArrayList<>()).add(new Label("STA",
                                                                              opcode,
                                                                              new Object[]{0x81, INDX, 0x91, INDY, 0x95, ZPX, 0x9d, ABSX, 0x99, ABSY, 0x85, ZP, 0x8d, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("LDA", s -> new ArrayList<>()).add(new Label("LDA",
                                                                              opcode,
                                                                              new Object[]{0xa9, IMM, 0xa1, INDX, 0xb1, INDY, 0xb5, ZPX, 0xbd, ABSX, 0xb9, ABSY, 0xa5, ZP, 0xad, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("CMP", s -> new ArrayList<>()).add(new Label("CMP",
                                                                              opcode,
                                                                              new Object[]{0xc9, IMM, 0xc1, INDX, 0xd1, INDY, 0xd5, ZPX, 0xdd, ABSX, 0xd9, ABSY, 0xc5, ZP, 0xcd, ABS, -1},
                                                                              RESERVED));
        labelMap.computeIfAbsent("SBC", s -> new ArrayList<>()).add(new Label("SBC",
                                                                              opcode,
                                                                              new Object[]{0xe9, IMM, 0xe1, INDX, 0xf1, INDY, 0xf5, ZPX, 0xfd, ABSX, 0xf9, ABSY, 0xe5, ZP, 0xed, ABS, -1},
                                                                              RESERVED));

        labelMap.computeIfAbsent("", s -> new ArrayList<>()).add(new Label("", directiveNothing, RESERVED));
        labelMap.computeIfAbsent("IF", s -> new ArrayList<>()).add(new Label("IF", directiveIf, RESERVED));
        labelMap.computeIfAbsent("ELSEIF", s -> new ArrayList<>()).add(new Label("ELSEIF", directiveElseIf, RESERVED));
        labelMap.computeIfAbsent("ELSE", s -> new ArrayList<>()).add(new Label("ELSE", directiveElse, RESERVED));
        labelMap.computeIfAbsent("ENDIF", s -> new ArrayList<>()).add(new Label("ENDIF", directiveEndIf, RESERVED));
        labelMap.computeIfAbsent("IFDEF", s -> new ArrayList<>()).add(new Label("IFDEF", directiveIfDef, RESERVED));
        labelMap.computeIfAbsent("IFNDEF", s -> new ArrayList<>()).add(new Label("IFNDEF", directiveIfNDef, RESERVED));
        labelMap.computeIfAbsent("=", s -> new ArrayList<>()).add(new Label("=", directiveEqual, RESERVED));
        labelMap.computeIfAbsent("EQU", s -> new ArrayList<>()).add(new Label("EQU", directiveEqu, RESERVED));
        labelMap.computeIfAbsent("ORG", s -> new ArrayList<>()).add(new Label("ORG", directiveOrg, RESERVED));
        labelMap.computeIfAbsent("BASE", s -> new ArrayList<>()).add(new Label("BASE", directiveBase, RESERVED));
        labelMap.computeIfAbsent("PAD", s -> new ArrayList<>()).add(new Label("PAD", directivePad, RESERVED));
        labelMap.computeIfAbsent("INCLUDE", s -> new ArrayList<>()).add(new Label("INCLUDE", directiveInclude, RESERVED));
        labelMap.computeIfAbsent("INCSRC", s -> new ArrayList<>()).add(new Label("INCSRC", directiveInclude, RESERVED));
        labelMap.computeIfAbsent("INCBIN", s -> new ArrayList<>()).add(new Label("INCBIN", directiveIncBin, RESERVED));
        labelMap.computeIfAbsent("BIN", s -> new ArrayList<>()).add(new Label("BIN", directiveIncBin, RESERVED));
        labelMap.computeIfAbsent("HEX", s -> new ArrayList<>()).add(new Label("HEX", directiveHex, RESERVED));
        labelMap.computeIfAbsent("WORD", s -> new ArrayList<>()).add(new Label("WORD", directiveDw, RESERVED));
        labelMap.computeIfAbsent("DW", s -> new ArrayList<>()).add(new Label("DW", directiveDw, RESERVED));
        labelMap.computeIfAbsent("DCW", s -> new ArrayList<>()).add(new Label("DCW", directiveDw, RESERVED));
        labelMap.computeIfAbsent("DC.W", s -> new ArrayList<>()).add(new Label("DC.W", directiveDw, RESERVED));
        labelMap.computeIfAbsent("BYTE", s -> new ArrayList<>()).add(new Label("BYTE", directiveDb, RESERVED));
        labelMap.computeIfAbsent("DB", s -> new ArrayList<>()).add(new Label("DB", directiveDb, RESERVED));
        labelMap.computeIfAbsent("DCB", s -> new ArrayList<>()).add(new Label("DCB", directiveDb, RESERVED));
        labelMap.computeIfAbsent("DC.B", s -> new ArrayList<>()).add(new Label("DC.B", directiveDb, RESERVED));
        labelMap.computeIfAbsent("DSW", s -> new ArrayList<>()).add(new Label("DSW", directiveDsw, RESERVED));
        labelMap.computeIfAbsent("DS.W", s -> new ArrayList<>()).add(new Label("DS.W", directiveDsw, RESERVED));
        labelMap.computeIfAbsent("DSB", s -> new ArrayList<>()).add(new Label("DSB", directiveDsb, RESERVED));
        labelMap.computeIfAbsent("DS.B", s -> new ArrayList<>()).add(new Label("DS.B", directiveDsb, RESERVED));
        labelMap.computeIfAbsent("ALIGN", s -> new ArrayList<>()).add(new Label("ALIGN", directiveAlign, RESERVED));
        labelMap.computeIfAbsent("MACRO", s -> new ArrayList<>()).add(new Label("MACRO", directiveMacro, RESERVED));
        labelMap.computeIfAbsent("REPT", s -> new ArrayList<>()).add(new Label("REPT", directiveRept, RESERVED));
        labelMap.computeIfAbsent("ENDM", s -> new ArrayList<>()).add(new Label("ENDM", directiveEndM, RESERVED));
        labelMap.computeIfAbsent("ENDR", s -> new ArrayList<>()).add(new Label("ENDR", directiveEndR, RESERVED));
        labelMap.computeIfAbsent("ENUM", s -> new ArrayList<>()).add(new Label("ENUM", directiveEnum, RESERVED));
        labelMap.computeIfAbsent("ENDE", s -> new ArrayList<>()).add(new Label("ENDE", directiveEndE, RESERVED));
        labelMap.computeIfAbsent("FILLVALUE", s -> new ArrayList<>()).add(new Label("FILLVALUE", directiveFillValue, RESERVED));
        labelMap.computeIfAbsent("DL", s -> new ArrayList<>()).add(new Label("DL", directiveDl, RESERVED));
        labelMap.computeIfAbsent("DH", s -> new ArrayList<>()).add(new Label("DH", directiveDh, RESERVED));
        labelMap.computeIfAbsent("ERROR", s -> new ArrayList<>()).add(new Label("ERROR", directiveError, RESERVED));
    }

    private void processFile(File file) {
        int nline = 0;
        nestedIncludes++;

        try {
            for (String line : Files.readAllLines(file.toPath())) {
                processLine(line, file.getName(), ++nline);
            }

            nestedIncludes--;

            if (nestedIncludes == 0) {
                if (ifLevel != 0) {
                    throwError("Missing ENDIF.", file.getName(), nline);
                }

                if (reptCount != 0) {
                    throwError("Missing ENDR.", file.getName(), nline);
                }

                if (makeMacro != null) {
                    throwError("Missing ENDM.", file.getName(), nline);
                }

                if (noOutput) {
                    throwError("Missing ENDE.", file.getName(), nline);
                }
            }
        } catch (IOException e) {
            throwError("Can't open or read file - " + e.getMessage(), file.getName(), nline);
        } catch (Exception e) {
            throwError(e, file.getName(), nline);
        }
    }

    @SuppressWarnings("unchecked")
    private void processLine(String src, String filename, int nline) {
        StringBuilder line = new StringBuilder();
        String comment = expandLine(src, line);

        if (insideMacro == 0 || verboseListing) {
            listLine(line.toString(), comment);
        }

        StringBuilder s = new StringBuilder(line.toString());

        if (makeMacro != null) {

        }

        if (reptCount > 0) {

        }

        labelHere = null;
        StringBuilder s2 = new StringBuilder(s);
        Label label;

        try {
            label = getReserved(s);
        } catch (Asm8Exception ignored) {
            label = null;
        }

        if (skipLine[ifLevel]) {
            if (label == null) {
                label = getReserved(s);
            }

            if (label == null
                    || (!label.value.equals(directiveElse) && !label.value.equals(directiveElseIf) && !label.value.equals(directiveEndIf)
                    && !label.value.equals(directiveIf) && !label.value.equals(directiveIfDef) && !label.value.equals(directiveIfNDef))) {
                return;
            }
        }

        if (label == null) {
            addLabel(getLabel(s2), insideMacro != 0);
            label = getReserved(s);
        }

        if (label != null) {
            if (label.type == MACRO) {
                expandMarco(label, s, nline, filename);
            } else {
                ((BiConsumer<Label, StringBuilder>) label.value).accept(label, s);
            }
        }

        eatLeadingWhiteSpace(s);

        if (s.length() > 0) {
            throw new Asm8Exception("Extra characters on line.");
        }
    }

    private String expandLine(String src, StringBuilder dst) {
        int i = 0;
        char c;
        char c2;
        boolean skipDef = false;
        String start;

        while (true) {
            try {
                c = src.charAt(i);

                if (c == '$' || (c >= '0' && c <= '9')) {
                    do {
                        dst.append(c);
                        c = src.charAt(++i);
                    }
                    while ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'H') || (c >= 'a' && c <= 'h'));
                } else if (c == '"' || c == '\'') {
                    dst.append(c);
                    i++;

                    do {
                        c2 = src.charAt(i);
                        dst.append(c2);

                        if (c2 == '\\') {
                            dst.append(src.charAt(++i));
                        }

                        i++;
                    }
                    while (c2 != 0 && c2 != c);
                } else if (c == '_' || c == '.' || c == LOCALCHAR || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) {
                    int i0 = c == '.' ? i + 1 : i;

                    do {
                        c = src.charAt(++i);
                    }
                    while (c == '_' || c == '.' || c == LOCALCHAR || (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'));

                    start = src.substring(i0, i);
                    Label label = null;

                    if (!skipDef) {
                        if ("IFDEF".equalsIgnoreCase(start) || "IFNDEF".equalsIgnoreCase(start)) {
                            skipDef = true;
                        } else {
                            label = findLabel(start);
                        }
                    }

                    if (label != null) {
                        if (label.type != EQUATE || label.pass != pass) {
                            label = null;
                        } else if (label.used) {
                            throw new RecurseEquException();
                        }
                    }

                    if (label != null) {
                        label.used = true;
                        expandLine((String) label.line, dst);
                        label.used = false;
                    } else {
                        dst.append(start);
                    }
                } else if (c == ';') {
                    return src.substring(i);
                } else {
                    dst.append(c);
                    i++;
                }
            } catch (StringIndexOutOfBoundsException e) {
                return null;
            }
        }
    }

    private void listLine(String src, String comment) {

    }

    private Label findLabel(String name) {
        List<Label> labelList = labelMap.get(name);

        if (labelList == null) {
            return null;
        }

        boolean nonFwdLabel = !"+".equals(name);

        Label local = labelList.stream()
                .filter(label -> nonFwdLabel || label.pass != pass)
                .filter(label -> label.scope == scope)
                .findFirst()
                .orElse(null);

        if (local != null) {
            return local;
        }

        return labelList.stream()
                .filter(label -> nonFwdLabel || label.pass != pass)
                .filter(label -> label.scope == 0)
                .reduce((label, label2) -> label2)
                .orElse(null);
    }

    private String getLabel(StringBuilder src) {
        StringBuilder dst = new StringBuilder();

        getWord(src, dst, true);

        if (dst.charAt(0) == '$' && dst.length() == 1) {
            return dst.toString();
        }

        StringBuilder s = new StringBuilder(dst);
        char c = s.charAt(0);

        if (c == '+' || c == '-') {
            try {
                do {
                    s.deleteCharAt(0);
                } while (s.charAt(0) == c);
            } catch (StringIndexOutOfBoundsException e) {
                return dst.toString();
            }
        }

        c = s.charAt(0);

        if (c == LOCALCHAR || c == '_' || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) {
            return dst.toString();
        } else {
            throw new IllegalException();
        }
    }

    private void addLabel(String word, boolean local) {
        Label label = findLabel(word);

        if (label != null && local && label.scope == 0 && label.type != VALUE) {
            label = null;
        }

        char c = word.charAt(0);

        if (c != LOCALCHAR && !local) {
            scope = nextScope++;
        }

        if (label == null) {
            labelHere = new Label(word, firstLabel.value, LABEL);
            labelHere.pass = pass;
            labelHere.line = ((int) firstLabel.value) >= 0 ? Boolean.TRUE : null;
            labelHere.used = false;

            if (c == LOCALCHAR || local) {
                labelHere.scope = scope;
            } else {
                labelHere.scope = 0;
            }

            labelMap.computeIfAbsent(word, s -> new ArrayList<>()).add(0, labelHere);

            lastLabel = labelHere;
        } else {
            labelHere = label;

            if (label.pass == pass && c != '-') {
                if (label.type != VALUE) {
                    throw new LabelDefinedException();
                }
            } else {
                label.pass = pass;

                if (label.type == LABEL) {
                    if (!Objects.equals(label.value, firstLabel.value) && c != '-') {
                        needAnotherPass = true;

                        if (lastChance) {
                            throw new BadAddrException();
                        }
                    }

                    label.value = firstLabel.value;
                    label.line = ((int) firstLabel.value) >= 0 ? Boolean.TRUE : null;

                    if (lastChance && ((int) firstLabel.value) < 0) {
                        throw new BadAddrException();
                    }
                }
            }
        }
    }

    private Label getReserved(StringBuilder src) {
        StringBuilder dst = new StringBuilder();
        String upp;

        eatLeadingWhiteSpace(src);

        if (src.length() > 0 && src.charAt(0) == '=') {
            upp = "=";
            src.deleteCharAt(0);
        } else {
            if (src.length() > 0 && src.charAt(0) == '.') {
                src.deleteCharAt(0);
            }

            getWord(src, dst, true);
            upp = dst.toString().toUpperCase();
        }

        Label label = findLabel(upp);

        if (label == null) {
            label = findLabel(dst.toString());
        }

        if (label != null) {
            if ((label.type == MACRO && label.pass != pass) || label.type != RESERVED) {
                label = null;
            }
        }

        if (label == null) {
            throw new IllegalException();
        }

        return label;
    }

    private void getWord(StringBuilder src, StringBuilder dst, boolean mcheck) {
        eatLeadingWhiteSpace(src);
        String s = whiteSpaceRegex.split(src.toString())[0];

        if (mcheck) {
            s = mathRegex.split(s)[0];
        }

        src.delete(0, s.length());

        if (src.length() > 0 && src.charAt(0) == ':') {
            src.deleteCharAt(0);
        }

        dst.setLength(0);
        dst.append(s);
    }

    private int getValue(StringBuilder str) {
        StringBuilder gvline = new StringBuilder();

        getWord(str, gvline, true);

        if (gvline.length() == 0) {
            throw new MissingOperandException();
        }

        StringBuilder s = new StringBuilder(gvline);

        int ret = 0;
        char c = s.length() > 0 ? s.charAt(0) : 0;

        if (c == '$') {
            s.deleteCharAt(0);

            if (s.length() == 0) {
                ret = (int) firstLabel.value;
            } else {
                int chars = 0;

                do {
                    ret = (ret << 4) | hexify(s.charAt(0));
                    chars++;
                    s.deleteCharAt(0);
                }
                while (s.length() > 0);

                if (chars > 8) {
                    throw new OutOfRangeException();
                }
            }
        } else if (c == '%') {
            s.deleteCharAt(0);
            int chars = 0;

            do {
                int j = s.charAt(0) - '0';

                if (j > 1) {
                    throw new NotANumberException();
                }

                ret = (ret << 1) | j;
                chars++;
                s.deleteCharAt(0);
            }
            while (s.length() > 0);

            if (chars > 32) {
                throw new OutOfRangeException();
            }
        } else if (c == '\'') {
            if (s.deleteCharAt(0).charAt(0) == '\\') {
                s.deleteCharAt(0);
            }

            ret = s.charAt(0);

            if (s.deleteCharAt(0).charAt(0) != '\'') {
                throw new NotANumberException();
            }
        } else if (c == '"') {
            if (s.deleteCharAt(0).charAt(0) == '\\') {
                s.deleteCharAt(0);
            }
            ret = s.charAt(0);

            if (s.deleteCharAt(0).charAt(0) != '"') {
                throw new NotANumberException();
            }
        } else if (s.charAt(0) >= '0' && s.charAt(0) <= '9') {
            try {
                ret = Integer.parseInt(s.toString());
            } catch (NumberFormatException e) {
                char end = s.charAt(s.length() - 1);

                if (end == 'b' || end == 'B') {
                    //TODO goto bin
                } else if (end == 'h' || end == 'H') {
                    //TODO goto hexi
                } else {
                    throw new NotANumberException();
                }
            }
        } else {
            Label label = findLabel(gvline.toString());

            if (label == null) {
                needAnotherPass = true;
                dependant = 1;

                if (lastChance) {
                    throw new UnknownLabelException();
                }
            } else {
                dependant |= (((int) label.line) == 0 ? 1 : 0);
                needAnotherPass |= (((int) label.line) == 0);

                if (label.type == LABEL || label.type == VALUE) {
                    ret = (int) label.value;
                } else if (label.type == MACRO) {
                    throw new Asm8Exception("Can't use macro in expression.");
                } else {
                    throw new UnknownLabelException();
                }
            }
        }

        return ret;
    }

    private Operator getOperator(StringBuilder str) {
        eatLeadingWhiteSpace(str);

        if (str.length() > 0) {
            char c = str.charAt(0);
            str.deleteCharAt(0);

            switch (c) {
                case '&':
                    if (str.length() > 0 && str.charAt(0) == '&') {
                        str.deleteCharAt(0);
                        return Operator.ANDAND;
                    } else {
                        return Operator.AND;
                    }
                case '|':
                    if (str.length() > 0 && str.charAt(0) == '|') {
                        str.deleteCharAt(0);
                        return Operator.OROR;
                    } else {
                        return Operator.OR;
                    }
                case '^':
                    return Operator.XOR;
                case '+':
                    return Operator.PLUS;
                case '-':
                    return Operator.MINUS;
                case '*':
                    return Operator.MUL;
                case '%':
                    return Operator.MOD;
                case '/':
                    return Operator.DIV;
                case '=':
                    if (str.length() > 0 && str.charAt(0) == '=') {
                        str.deleteCharAt(0);
                    }

                    return Operator.EQUAL;
                case '>':
                    if (str.length() > 0) {
                        if (str.charAt(0) == '=') {
                            str.deleteCharAt(0);
                            return Operator.GREATEREQ;
                        } else if (str.charAt(0) == '>') {
                            str.deleteCharAt(0);
                            return Operator.RIGHTSHIFT;
                        }
                    }

                    return Operator.GREATER;
                case '<':
                    if (str.length() > 0) {
                        if (str.charAt(0) == '=') {
                            str.deleteCharAt(0);
                            return Operator.LESSEQ;
                        } else if (str.charAt(0) == '>') {
                            str.deleteCharAt(0);
                            return Operator.NOTEQUAL;
                        } else if (str.charAt(0) == '<') {
                            str.deleteCharAt(0);
                            return Operator.LEFTSHIFT;
                        }
                    }

                    return Operator.LESS;
                case '!':
                    if (str.length() > 0 && str.charAt(0) == '=') {
                        str.deleteCharAt(0);
                        return Operator.NOTEQUAL;
                    }
                default:
                    str.insert(0, c);
                    return Operator.NOOP;
            }
        }

        return Operator.NOOP;
    }

    private void expandMarco(Label id, StringBuilder next, int nline, String src) {

    }

    private int eval(StringBuilder str, Operator.Precedence precedence) {
        int ret;
        Operator op;

        StringBuilder s = new StringBuilder(str);
        eatLeadingWhiteSpace(s);

        char unary = s.length() > 0 ? s.charAt(0) : 0;

        switch (unary) {
            case '(':
                ret = eval(s.deleteCharAt(0), WHOLEEXP);

                eatLeadingWhiteSpace(s);

                if (s.length() > 0 && s.charAt(0) == ')') {
                    s.deleteCharAt(0);
                } else {
                    throw new IncompleteException();
                }
                break;
            case '#':
                ret = eval(s.deleteCharAt(0), WHOLEEXP);
                break;
            case '~':
                ret = ~eval(s.deleteCharAt(0), UNARY);
                break;
            case '!':
                ret = eval(s.deleteCharAt(0), UNARY) == 0 ? 1 : 0;
                break;
            case '<':
                ret = eval(s.deleteCharAt(0), UNARY) & 0xFF;
                break;
            case '>':
                ret = (eval(s.deleteCharAt(0), UNARY) >> 8) & 0xFF;
                break;
            case '+':
            case '-':
                StringBuilder s2 = new StringBuilder(s);
                s.deleteCharAt(0);
                op = Operator.values()[dependant];
                boolean val2 = needAnotherPass;
                dependant = 0;
                try {
                    ret = getValue(s2);
                } catch (UnknownLabelException e) {
                    ret = 0;
                }

                if (dependant == 0 || s2.toString().equals(s.toString())) {
                    s.setLength(0);
                    s.append(s2);
                    s2 = null;
                    dependant |= op.ordinal();
                } else {
                    dependant = op.ordinal();
                    needAnotherPass = val2;
                }

                if (s2 != null) {
                    ret = eval(s, UNARY);

                    if (unary == '-') {
                        ret = -ret;
                    }
                }
                break;
            default:
                ret = getValue(s);
        }

        do {
            str.setLength(0);
            str.append(s);
            op = getOperator(s);

            if (precedence.ordinal() < op.precedence.ordinal()) {
                int val2 = eval(s, op.precedence);

                if (dependant == 0) {
                    switch (op) {
                        case NOOP:
                            break;
                        case EQUAL:
                            ret = (ret == val2) ? 1 : 0;
                            break;
                        case NOTEQUAL:
                            ret = (ret != val2) ? 1 : 0;
                            break;
                        case GREATER:
                            ret = (ret > val2) ? 1 : 0;
                            break;
                        case GREATEREQ:
                            ret = (ret >= val2) ? 1 : 0;
                            break;
                        case LESS:
                            ret = (ret < val2) ? 1 : 0;
                            break;
                        case LESSEQ:
                            ret = (ret <= val2) ? 1 : 0;
                            break;
                        case PLUS:
                            ret += val2;
                            break;
                        case MINUS:
                            ret -= val2;
                            break;
                        case MUL:
                            ret *= val2;
                            break;
                        case DIV:
                            if (val2 == 0) {
                                throw new DivideByZeroException();
                            }

                            ret /= val2;
                            break;
                        case MOD:
                            if (val2 == 0) {
                                throw new DivideByZeroException();
                            }

                            ret %= val2;
                            break;
                        case AND:
                            ret &= val2;
                            break;
                        case XOR:
                            ret ^= val2;
                            break;
                        case OR:
                            ret |= val2;
                            break;
                        case ANDAND:
                            ret = ((ret != 0) && (val2 != 0)) ? 1 : 0;
                            break;
                        case OROR:
                            ret = ((ret != 0) || (val2 != 0)) ? 1 : 0;
                            break;
                        case LEFTSHIFT:
                            ret <<= val2;
                            break;
                        case RIGHTSHIFT:
                            ret >>= val2;
                            break;
                    }
                } else {
                    ret = 0;
                }
            }
        }
        while (precedence.ordinal() < op.precedence.ordinal());

        return ret;
    }

    private boolean eatChar(StringBuilder str, char c) {
        if (c != 0) {
            eatLeadingWhiteSpace(str);

            if (str.length() > 0 && str.charAt(0) == c) {
                str.deleteCharAt(0);
            } else {
                return false;
            }
        }

        return true;
    }

    private void eatLeadingWhiteSpace(StringBuilder src) {
        while (src.length() > 0 && whiteSpaceChars.contains(src.charAt(0))) {
            src.deleteCharAt(0);
        }
    }

    private void eatTrailingWhiteSpace(StringBuilder src) {
        while (src.length() > 0 && whiteSpaceChars.contains(src.charAt(src.length() - 1))) {
            src.deleteCharAt(src.length() - 1);
        }
    }

    private int hexify(char c) {
        if (c >= '0' && c <= '9') {
            return c - '0';
        } else if (c >= 'a' && c <= 'f') {
            return c - ('a' - 10);
        } else if (c >= 'A' && c <= 'F') {
            return c - ('A' - 10);
        } else {
            throw new NotANumberException();
        }
    }

    private void throwError(Throwable t, String filename, int line) {
        throw new RuntimeException(String.format("%s(%s): %s", filename, line, t.getMessage()));
    }

    private void throwError(String message, String filename, int line) {
        throw new RuntimeException(String.format("%s(%s): %s", filename, line, message));
    }

    //------------------------------------------
    // Opcodes and Directives
    //------------------------------------------

    private void opcode(Label id, StringBuilder next) {

    }

    private void nothing(Label id, StringBuilder next) {

    }

    private void _if(Label id, StringBuilder next) {

    }

    private void elseif(Label id, StringBuilder next) {

    }

    private void _else(Label id, StringBuilder next) {

    }

    private void endif(Label id, StringBuilder next) {

    }

    private void ifdef(Label id, StringBuilder next) {

    }

    private void ifndef(Label id, StringBuilder next) {

    }

    private void equal(Label id, StringBuilder next) {
        System.out.println(next);
    }

    private void equ(Label id, StringBuilder next) {

    }

    private void org(Label id, StringBuilder next) {

    }

    private void base(Label id, StringBuilder next) {

    }

    private void pad(Label id, StringBuilder next) {

    }

    private void include(Label id, StringBuilder next) {
        processFile(new File(next.toString().trim()));
    }

    private void incbin(Label id, StringBuilder next) {

    }

    private void hex(Label id, StringBuilder next) {

    }

    private void dw(Label id, StringBuilder next) {

    }

    private void db(Label id, StringBuilder next) {

    }

    private void dsw(Label id, StringBuilder next) {

    }

    private void dsb(Label id, StringBuilder next) {

    }

    private void align(Label id, StringBuilder next) {

    }

    private void macro(Label id, StringBuilder next) {

    }

    private void rept(Label id, StringBuilder next) {

    }

    private void endm(Label id, StringBuilder next) {

    }

    private void endr(Label id, StringBuilder next) {

    }

    private void _enum(Label id, StringBuilder next) {

    }

    private void ende(Label id, StringBuilder next) {

    }

    private void fillval(Label id, StringBuilder next) {

    }

    private void dl(Label id, StringBuilder next) {

    }

    private void dh(Label id, StringBuilder next) {

    }

    private void makeError(Label id, StringBuilder next) {

    }

    class Asm8Exception extends RuntimeException {

        public Asm8Exception(String message) {
            super(message);
        }
    }

    class OutOfRangeException extends Asm8Exception {

        public OutOfRangeException() {
            super("Value out of range.");
        }
    }

    class SeeKOutOfRangeException extends Asm8Exception {

        public SeeKOutOfRangeException() {
            super("Seek position out of range.");
        }
    }

    class BadIncbinSizeException extends Asm8Exception {

        public BadIncbinSizeException() {
            super("INCBIN size is out of range.");
        }
    }

    class NotANumberException extends Asm8Exception {

        public NotANumberException() {
            super("Not a number.");
        }
    }

    class UnknownLabelException extends Asm8Exception {

        public UnknownLabelException() {
            super("Unknown label.");
        }
    }

    class IllegalException extends Asm8Exception {

        public IllegalException() {
            super("Illegal instruction.");
        }
    }

    class IncompleteException extends Asm8Exception {

        public IncompleteException() {
            super("Incomplete expression.");
        }
    }

    class LabelDefinedException extends Asm8Exception {

        public LabelDefinedException() {
            super("Label already defined.");
        }
    }

    class MissingOperandException extends Asm8Exception {

        public MissingOperandException() {
            super("Missing operand.");
        }
    }

    class DivideByZeroException extends Asm8Exception {

        public DivideByZeroException() {
            super("Divide by zero.");
        }
    }

    class BadAddrException extends Asm8Exception {

        public BadAddrException() {
            super("Can't determine address.");
        }
    }

    class NeedNameException extends Asm8Exception {

        public NeedNameException() {
            super("Need a name.");
        }
    }

    class CantOpenException extends Asm8Exception {

        public CantOpenException() {
            super("Can't open file.");
        }
    }

    class ExtraEndMException extends Asm8Exception {

        public ExtraEndMException() {
            super("ENDM without MACRO.");
        }
    }

    class ExtraEndRException extends Asm8Exception {

        public ExtraEndRException() {
            super("ENDR without REPT.");
        }
    }

    class ExtraEndEException extends Asm8Exception {

        public ExtraEndEException() {
            super("ENDE without ENUM.");
        }
    }

    class RecurseMacroException extends Asm8Exception {

        public RecurseMacroException() {
            super("Recursive MACRO not allowed.");
        }
    }

    class RecurseEquException extends Asm8Exception {

        public RecurseEquException() {
            super("Recursive EQU not allowed.");
        }
    }

    class MissingEndifException extends Asm8Exception {

        public MissingEndifException() {
            super("Missing ENDIF.");
        }
    }

    class MissingEndMException extends Asm8Exception {

        public MissingEndMException() {
            super("Missing ENDM.");
        }
    }

    class MissingEndRException extends Asm8Exception {

        public MissingEndRException() {
            super("Missing ENDR.");
        }
    }

    class MissingEndEException extends Asm8Exception {

        public MissingEndEException() {
            super("Missing ENDE.");
        }
    }

    class IfNestLimitException extends Asm8Exception {

        public IfNestLimitException() {
            super("Too many nested IFs.");
        }
    }

    class UndefinedPCException extends Asm8Exception {

        public UndefinedPCException() {
            super("PC is undefined (use ORG first)");
        }
    }
}
