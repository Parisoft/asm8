import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.function.BiConsumer;
import java.util.regex.Pattern;

import static java.nio.file.Files.deleteIfExists;

public class Asm8 {

    private static final String VERSION = "1.6.1";

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
    private static final List<Character> whiteSpaceChars2 = Arrays.asList(' ', '\t', '\r', '\n', '\"');
    private static final Pattern whiteSpaceRegex = Pattern.compile("\\s|:");
    private static final Pattern mathRegex = Pattern.compile("!|^|&|\\||\\+|-|\\*|/|%|\\(|\\)|<|>|=|,");

    enum OpType {
        ACC(0, (char) 0, "A"),
        IMM(1, '#', ""),
        IND(2, '(', ")"),
        INDX(1, '(', ",X)"),
        INDY(1, '(', "),Y"),
        ZPX(1, (char) 0, ",X"),
        ZPY(1, (char) 0, ",Y"),
        ABSX(2, (char) 0, ",X"),
        ABSY(2, (char) 0, ",Y"),
        ZP(1, (char) 0, ""),
        ABS(2, (char) 0, ""),
        REL(1, (char) 0, ""),
        IMP(0, (char) 0, "");

        int size;
        char head;
        String tail;

        OpType(int size, char head, String tail) {
            this.size = size;
            this.head = head;
            this.tail = tail;
        }
    }

    enum Operator {
        NOOP(Precedence.WHOLEEXP),
        EQUAL(Precedence.EQCOMPARE),
        NOTEQUAL(Precedence.EQCOMPARE),
        GREATER(Precedence.COMPARE),
        GREATEREQ(Precedence.COMPARE),
        LESS(Precedence.COMPARE),
        LESSEQ(Precedence.COMPARE),
        PLUS(Precedence.PLUSMINUS),
        MINUS(Precedence.PLUSMINUS),
        MUL(Precedence.MULDIV),
        DIV(Precedence.MULDIV),
        MOD(Precedence.MULDIV),
        AND(Precedence.ANDP),
        XOR(Precedence.XORP),
        OR(Precedence.ORP),
        ANDAND(Precedence.ANDANDP),
        OROR(Precedence.ORORP),
        LEFTSHIFT(Precedence.SHIFT),
        RIGHTSHIFT(Precedence.SHIFT);

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

    private int oldPass = 0;
    private int pass = 0;
    private int scope = 0;
    private int nextScope;
    private boolean lastChance = false;
    private boolean needAnotherPass = false;
    private boolean[] ifDone = new boolean[IFNESTS];
    private boolean[] skipLine = new boolean[IFNESTS];
    private int defaultFiller;
    private final Map<String, List<Label>> labelMap = new HashMap<>();
    private Label firstLabel = new Label("$", 0, Boolean.TRUE, Label.Type.VALUE);
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
    private OutputStream outputStream;
    private boolean verbose = true;
    private int dependant;
    private int enumSaveAddr;

    public void setVerboseListing(boolean verboseListing) {
        this.verboseListing = verboseListing;
    }

    public void setListFileName(String listFileName) {
        this.listFileName = listFileName;
    }

    public void setInputFileName(String inputFileName) {
        this.inputFileName = inputFileName;
    }

    public void setOutputFileName(String outputFileName) {
        this.outputFileName = outputFileName;
    }

    public void setVerbose(boolean verbose) {
        this.verbose = verbose;
    }

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
                    case 'd':
                        System.err.println("Error: option not implemented yet: " + args[i]);
                        System.exit(0);
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

                notOption++;
            }
        }

        if (asm8.inputFileName == null) {
            System.err.println("Error: No source file specified.");
            System.exit(0);
        }

        if (asm8.outputFileName == null) {
            asm8.outputFileName = asm8.inputFileName.substring(0, asm8.inputFileName.lastIndexOf('.')).concat(".bin");
        }

        try {
            deleteIfExists(Paths.get(asm8.outputFileName));
        } catch (IOException e) {
            System.err.println("Can't delete old output file");
            System.exit(0);
        }

        if (asm8.listFileName != null) {
            if (asm8.listFileName.isEmpty()) {
                asm8.listFileName = asm8.inputFileName.substring(0, asm8.inputFileName.lastIndexOf('.')).concat(".lst");
            }

            try {
                deleteIfExists(Paths.get(asm8.listFileName));
            } catch (IOException e) {
                System.err.println("Can't delete old list file");
                System.exit(0);
            }
        }

        try {
            asm8.compile();
        } catch (Exception e) {
            System.err.println(e.getMessage());
            System.exit(0);
        }
    }

    private static void showHelp() {
        System.out.println();
        System.out.println("asm8 " + VERSION);
        System.out.println();
        System.out.println("Usage:  asm8 [-options] sourcefile [outputfile] [listfile]");
        System.out.println("    -?          show this help");
        System.out.println("    -l          create listing");
        System.out.println("    -L          create verbose listing (expand REPT, MACRO)");
        System.out.println("    -d<name>    define symbol");
        System.out.println("    -q          quiet mode (no output unless error)");
        System.out.println();
        System.out.println("See README.TXT for more info.");
    }

    public void compile() {
        initLabels();

        Label currLabel = null;

        try {
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
        } catch (Asm8Exception e) {
            try {
                deleteIfExists(Paths.get(outputFileName));
            } catch (IOException ignored) {
            }

            throw e;
        }

        if (outputStream != null) {
            try {
                outputStream.flush();
                outputStream.close();
                System.out.printf("%s written (%d bytes).\n", outputFileName, new File(outputFileName).length());
            } catch (IOException e) {
                throw new Asm8Exception("Write error.");
            }
        }
    }

    private void initLabels() {
        BiConsumer<Label, StringBuilder> opcode = (o, o2) -> opcode(o, o2);
        labelMap.computeIfAbsent("BRK", s -> new ArrayList<>()).add(new Label("BRK",
                                                                              opcode,
                                                                              opMap(0x00, OpType.IMM, 0x00, OpType.ZP, 0x00, OpType.IMP),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("PHP", s -> new ArrayList<>()).add(new Label("PHP", opcode, opMap(0x08, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BPL", s -> new ArrayList<>()).add(new Label("BPL", opcode, opMap(0x10, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("CLC", s -> new ArrayList<>()).add(new Label("CLC", opcode, opMap(0x18, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("JSR", s -> new ArrayList<>()).add(new Label("JSR", opcode, opMap(0x20, OpType.ABS), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BIT", s -> new ArrayList<>()).add(new Label("BIT", opcode, opMap(0x24, OpType.ZP, 0x2c, OpType.ABS), Label.Type.RESERVED));
        labelMap.computeIfAbsent("PLP", s -> new ArrayList<>()).add(new Label("PLP", opcode, opMap(0x28, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BMI", s -> new ArrayList<>()).add(new Label("BMI", opcode, opMap(0x30, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("SEC", s -> new ArrayList<>()).add(new Label("SEC", opcode, opMap(0x38, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("RTI", s -> new ArrayList<>()).add(new Label("RTI", opcode, opMap(0x40, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("PHA", s -> new ArrayList<>()).add(new Label("PHA", opcode, opMap(0x48, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("JMP", s -> new ArrayList<>()).add(new Label("JMP", opcode, opMap(0x6c, OpType.IND, 0x4c, OpType.ABS), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BVC", s -> new ArrayList<>()).add(new Label("BVC", opcode, opMap(0x50, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("CLI", s -> new ArrayList<>()).add(new Label("CLI", opcode, opMap(0x58, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("RTS", s -> new ArrayList<>()).add(new Label("RTS", opcode, opMap(0x60, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("PLA", s -> new ArrayList<>()).add(new Label("PLA", opcode, opMap(0x68, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BVS", s -> new ArrayList<>()).add(new Label("BVS", opcode, opMap(0x70, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("SEI", s -> new ArrayList<>()).add(new Label("SEI", opcode, opMap(0x78, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("STY", s -> new ArrayList<>()).add(new Label("STY",
                                                                              opcode,
                                                                              opMap(0x94, OpType.ZPX, 0x84, OpType.ZP, 0x8c, OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("STX", s -> new ArrayList<>()).add(new Label("STX",
                                                                              opcode,
                                                                              opMap(0x96, OpType.ZPY, 0x86, OpType.ZP, 0x8e, OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("DEY", s -> new ArrayList<>()).add(new Label("DEY", opcode, opMap(0x88, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("TXA", s -> new ArrayList<>()).add(new Label("TXA", opcode, opMap(0x8a, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BCC", s -> new ArrayList<>()).add(new Label("BCC", opcode, opMap(0x90, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("TYA", s -> new ArrayList<>()).add(new Label("TYA", opcode, opMap(0x98, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("TXS", s -> new ArrayList<>()).add(new Label("TXS", opcode, opMap(0x9a, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("TAY", s -> new ArrayList<>()).add(new Label("TAY", opcode, opMap(0xa8, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("TAX", s -> new ArrayList<>()).add(new Label("TAX", opcode, opMap(0xaa, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BCS", s -> new ArrayList<>()).add(new Label("BCS", opcode, opMap(0xb0, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("CLV", s -> new ArrayList<>()).add(new Label("CLV", opcode, opMap(0xb8, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("TSX", s -> new ArrayList<>()).add(new Label("TSX", opcode, opMap(0xba, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("CPY", s -> new ArrayList<>()).add(new Label("CPY",
                                                                              opcode,
                                                                              opMap(0xc0, OpType.IMM, 0xc4, OpType.ZP, 0xcc, OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("DEC", s -> new ArrayList<>()).add(new Label("DEC",
                                                                              opcode,
                                                                              opMap(0xd6, OpType.ZPX, 0xde, OpType.ABSX, 0xc6, OpType.ZP, 0xce, OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("INY", s -> new ArrayList<>()).add(new Label("INY", opcode, opMap(0xc8, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("DEX", s -> new ArrayList<>()).add(new Label("DEX", opcode, opMap(0xca, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BNE", s -> new ArrayList<>()).add(new Label("BNE", opcode, opMap(0xd0, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("CLD", s -> new ArrayList<>()).add(new Label("CLD", opcode, opMap(0xd8, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("CPX", s -> new ArrayList<>()).add(new Label("CPX",
                                                                              opcode,
                                                                              opMap(0xe0, OpType.IMM, 0xe4, OpType.ZP, 0xec, OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("INC", s -> new ArrayList<>()).add(new Label("INC",
                                                                              opcode,
                                                                              opMap(0xf6, OpType.ZPX, 0xfe, OpType.ABSX, 0xe6, OpType.ZP, 0xee, OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("INX", s -> new ArrayList<>()).add(new Label("INX", opcode, opMap(0xe8, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("NOP", s -> new ArrayList<>()).add(new Label("NOP", opcode, opMap(0xea, OpType.IMP), Label.Type.RESERVED));
        labelMap.computeIfAbsent("BEQ", s -> new ArrayList<>()).add(new Label("BEQ", opcode, opMap(0xf0, OpType.REL), Label.Type.RESERVED));
        labelMap.computeIfAbsent("LDY", s -> new ArrayList<>()).add(new Label("LDY",
                                                                              opcode,
                                                                              opMap(0xa0,
                                                                                    OpType.IMM,
                                                                                    0xb4,
                                                                                    OpType.ZPX,
                                                                                    0xbc,
                                                                                    OpType.ABSX,
                                                                                    0xa4,
                                                                                    OpType.ZP,
                                                                                    0xac,
                                                                                    OpType.ABS),
                                                                              Label.Type.RESERVED));
        labelMap.computeIfAbsent("LDX", s -> new ArrayList<>()).add(new Label("LDX",
                                                                              opcode,
                                                                              opMap(0xa2,
                                                                                    OpType.IMM,
                                                                                    0xb6,
                                                                                    OpType.ZPY,
                                                                                    0xbe,
                                                                                    OpType.ABSY,
                                                                                    0xa6,
                                                                                    OpType.ZP,
                                                                                    0xae,
                                                                                    OpType.ABS),
                                                                              Label.Type.RESERVED));
        Map<OpType, Byte> oraMap = opMap(0x09,
                                         OpType.IMM,
                                         0x01,
                                         OpType.INDX,
                                         0x11,
                                         OpType.INDY,
                                         0x15,
                                         OpType.ZPX,
                                         0x1d,
                                         OpType.ABSX,
                                         0x19,
                                         OpType.ABSY,
                                         0x05,
                                         OpType.ZP,
                                         0x0d,
                                         OpType.ABS);
        Map<OpType, Byte> aslMap = opMap(0x0a, OpType.ACC, 0x16, OpType.ZPX, 0x1e, OpType.ABSX, 0x06, OpType.ZP, 0x0e, OpType.ABS, 0x0a, OpType.IMP);
        Map<OpType, Byte> andMap = opMap(0x29,
                                         OpType.IMM,
                                         0x21,
                                         OpType.INDX,
                                         0x31,
                                         OpType.INDY,
                                         0x35,
                                         OpType.ZPX,
                                         0x3d,
                                         OpType.ABSX,
                                         0x39,
                                         OpType.ABSY,
                                         0x25,
                                         OpType.ZP,
                                         0x2d,
                                         OpType.ABS);
        Map<OpType, Byte> rolMap = opMap(0x2a, OpType.ACC, 0x36, OpType.ZPX, 0x3e, OpType.ABSX, 0x26, OpType.ZP, 0x2e, OpType.ABS, 0x2a, OpType.IMP);
        Map<OpType, Byte> eorMap = opMap(0x49,
                                         OpType.IMM,
                                         0x41,
                                         OpType.INDX,
                                         0x51,
                                         OpType.INDY,
                                         0x55,
                                         OpType.ZPX,
                                         0x5d,
                                         OpType.ABSX,
                                         0x59,
                                         OpType.ABSY,
                                         0x45,
                                         OpType.ZP,
                                         0x4d,
                                         OpType.ABS);
        Map<OpType, Byte> lsrMap = opMap(0x4a, OpType.ACC, 0x56, OpType.ZPX, 0x5e, OpType.ABSX, 0x46, OpType.ZP, 0x4e, OpType.ABS, 0x4a, OpType.IMP);
        Map<OpType, Byte> adcMap = opMap(0x69,
                                         OpType.IMM,
                                         0x61,
                                         OpType.INDX,
                                         0x71,
                                         OpType.INDY,
                                         0x75,
                                         OpType.ZPX,
                                         0x7d,
                                         OpType.ABSX,
                                         0x79,
                                         OpType.ABSY,
                                         0x65,
                                         OpType.ZP,
                                         0x6d,
                                         OpType.ABS);
        Map<OpType, Byte> rorMap = opMap(0x6a, OpType.ACC, 0x76, OpType.ZPX, 0x7e, OpType.ABSX, 0x66, OpType.ZP, 0x6e, OpType.ABS, 0x6a, OpType.IMP);
        Map<OpType, Byte> staMap = opMap(0x81, OpType.INDX, 0x91, OpType.INDY, 0x95, OpType.ZPX, 0x9d, OpType.ABSX, 0x99, OpType.ABSY, 0x85, OpType.ZP, 0x8d, OpType.ABS);
        Map<OpType, Byte> ldaMap = opMap(0xa9,
                                         OpType.IMM,
                                         0xa1,
                                         OpType.INDX,
                                         0xb1,
                                         OpType.INDY,
                                         0xb5,
                                         OpType.ZPX,
                                         0xbd,
                                         OpType.ABSX,
                                         0xb9,
                                         OpType.ABSY,
                                         0xa5,
                                         OpType.ZP,
                                         0xad,
                                         OpType.ABS);
        Map<OpType, Byte> cmpMap = opMap(0xc9,
                                         OpType.IMM,
                                         0xc1,
                                         OpType.INDX,
                                         0xd1,
                                         OpType.INDY,
                                         0xd5,
                                         OpType.ZPX,
                                         0xdd,
                                         OpType.ABSX,
                                         0xd9,
                                         OpType.ABSY,
                                         0xc5,
                                         OpType.ZP,
                                         0xcd,
                                         OpType.ABS);
        Map<OpType, Byte> sbcMap = opMap(0xe9,
                                         OpType.IMM,
                                         0xe1,
                                         OpType.INDX,
                                         0xf1,
                                         OpType.INDY,
                                         0xf5,
                                         OpType.ZPX,
                                         0xfd,
                                         OpType.ABSX,
                                         0xf9,
                                         OpType.ABSY,
                                         0xe5,
                                         OpType.ZP,
                                         0xed,
                                         OpType.ABS);
        labelMap.computeIfAbsent("ORA", s -> new ArrayList<>()).add(new Label("ORA", opcode, oraMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ASL", s -> new ArrayList<>()).add(new Label("ASL", opcode, aslMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("AND", s -> new ArrayList<>()).add(new Label("AND", opcode, andMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ROL", s -> new ArrayList<>()).add(new Label("ROL", opcode, rolMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("EOR", s -> new ArrayList<>()).add(new Label("EOR", opcode, eorMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("LSR", s -> new ArrayList<>()).add(new Label("LSR", opcode, lsrMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ADC", s -> new ArrayList<>()).add(new Label("ADC", opcode, adcMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ROR", s -> new ArrayList<>()).add(new Label("ROR", opcode, rorMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("STA", s -> new ArrayList<>()).add(new Label("STA", opcode, staMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("LDA", s -> new ArrayList<>()).add(new Label("LDA", opcode, ldaMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("CMP", s -> new ArrayList<>()).add(new Label("CMP", opcode, cmpMap, Label.Type.RESERVED));
        labelMap.computeIfAbsent("SBC", s -> new ArrayList<>()).add(new Label("SBC", opcode, sbcMap, Label.Type.RESERVED));

        labelMap.computeIfAbsent("", s -> new ArrayList<>()).add(new Label("", directiveNothing, Label.Type.RESERVED));
        labelMap.computeIfAbsent("IF", s -> new ArrayList<>()).add(new Label("IF", directiveIf, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ELSEIF", s -> new ArrayList<>()).add(new Label("ELSEIF", directiveElseIf, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ELSE", s -> new ArrayList<>()).add(new Label("ELSE", directiveElse, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ENDIF", s -> new ArrayList<>()).add(new Label("ENDIF", directiveEndIf, Label.Type.RESERVED));
        labelMap.computeIfAbsent("IFDEF", s -> new ArrayList<>()).add(new Label("IFDEF", directiveIfDef, Label.Type.RESERVED));
        labelMap.computeIfAbsent("IFNDEF", s -> new ArrayList<>()).add(new Label("IFNDEF", directiveIfNDef, Label.Type.RESERVED));
        labelMap.computeIfAbsent("=", s -> new ArrayList<>()).add(new Label("=", directiveEqual, Label.Type.RESERVED));
        labelMap.computeIfAbsent("EQU", s -> new ArrayList<>()).add(new Label("EQU", directiveEqu, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ORG", s -> new ArrayList<>()).add(new Label("ORG", directiveOrg, Label.Type.RESERVED));
        labelMap.computeIfAbsent("BASE", s -> new ArrayList<>()).add(new Label("BASE", directiveBase, Label.Type.RESERVED));
        labelMap.computeIfAbsent("PAD", s -> new ArrayList<>()).add(new Label("PAD", directivePad, Label.Type.RESERVED));
        labelMap.computeIfAbsent("INCLUDE", s -> new ArrayList<>()).add(new Label("INCLUDE", directiveInclude, Label.Type.RESERVED));
        labelMap.computeIfAbsent("INCSRC", s -> new ArrayList<>()).add(new Label("INCSRC", directiveInclude, Label.Type.RESERVED));
        labelMap.computeIfAbsent("INCBIN", s -> new ArrayList<>()).add(new Label("INCBIN", directiveIncBin, Label.Type.RESERVED));
        labelMap.computeIfAbsent("BIN", s -> new ArrayList<>()).add(new Label("BIN", directiveIncBin, Label.Type.RESERVED));
        labelMap.computeIfAbsent("HEX", s -> new ArrayList<>()).add(new Label("HEX", directiveHex, Label.Type.RESERVED));
        labelMap.computeIfAbsent("WORD", s -> new ArrayList<>()).add(new Label("WORD", directiveDw, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DW", s -> new ArrayList<>()).add(new Label("DW", directiveDw, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DCW", s -> new ArrayList<>()).add(new Label("DCW", directiveDw, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DC.W", s -> new ArrayList<>()).add(new Label("DC.W", directiveDw, Label.Type.RESERVED));
        labelMap.computeIfAbsent("BYTE", s -> new ArrayList<>()).add(new Label("BYTE", directiveDb, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DB", s -> new ArrayList<>()).add(new Label("DB", directiveDb, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DCB", s -> new ArrayList<>()).add(new Label("DCB", directiveDb, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DC.B", s -> new ArrayList<>()).add(new Label("DC.B", directiveDb, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DSW", s -> new ArrayList<>()).add(new Label("DSW", directiveDsw, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DS.W", s -> new ArrayList<>()).add(new Label("DS.W", directiveDsw, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DSB", s -> new ArrayList<>()).add(new Label("DSB", directiveDsb, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DS.B", s -> new ArrayList<>()).add(new Label("DS.B", directiveDsb, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ALIGN", s -> new ArrayList<>()).add(new Label("ALIGN", directiveAlign, Label.Type.RESERVED));
        labelMap.computeIfAbsent("MACRO", s -> new ArrayList<>()).add(new Label("MACRO", directiveMacro, Label.Type.RESERVED));
        labelMap.computeIfAbsent("REPT", s -> new ArrayList<>()).add(new Label("REPT", directiveRept, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ENDM", s -> new ArrayList<>()).add(new Label("ENDM", directiveEndM, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ENDR", s -> new ArrayList<>()).add(new Label("ENDR", directiveEndR, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ENUM", s -> new ArrayList<>()).add(new Label("ENUM", directiveEnum, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ENDE", s -> new ArrayList<>()).add(new Label("ENDE", directiveEndE, Label.Type.RESERVED));
        labelMap.computeIfAbsent("FILLVALUE", s -> new ArrayList<>()).add(new Label("FILLVALUE", directiveFillValue, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DL", s -> new ArrayList<>()).add(new Label("DL", directiveDl, Label.Type.RESERVED));
        labelMap.computeIfAbsent("DH", s -> new ArrayList<>()).add(new Label("DH", directiveDh, Label.Type.RESERVED));
        labelMap.computeIfAbsent("ERROR", s -> new ArrayList<>()).add(new Label("ERROR", directiveError, Label.Type.RESERVED));
    }

    private void processFile(File file) {
        int nline = 0;
        nestedIncludes++;

        try {
            for (String line : Files.readAllLines(file.toPath())) {
                processLine(new StringBuilder(line), file.getName(), ++nline);
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
    private void processLine(StringBuilder src, String filename, int nline) {
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
            if (label.type == Label.Type.MACRO) {
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

    private String expandLine(StringBuilder src, StringBuilder dst) {
        char c;
        char c2;
        boolean skipDef = false;
        StringBuilder start;
        String comment = null;

        do {
            c = src.length() > 0 ? src.charAt(0) : 0;

            if (c == '$' || (c >= '0' && c <= '9')) {
                do {
                    dst.append(c);
                    src.deleteCharAt(0);
                    c = src.length() > 0 ? src.charAt(0) : 0;
                }
                while ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'H') || (c >= 'a' && c <= 'h'));
            } else if (c == '"' || c == '\'') {
                dst.append(c);
                src.deleteCharAt(0);

                do {
                    if (src.length() > 0) {
                        c2 = src.charAt(0);
                        dst.append(c2);
                    } else {
                        c2 = 0;
                    }

                    if (c2 == '\\') {
                        if (src.deleteCharAt(0).length() > 0) {
                            dst.append(src.charAt(0));
                        }
                    }

                    if (src.length() > 0) {
                        src.deleteCharAt(0);
                    }
                }
                while (c2 != 0 && c2 != c);
            } else if (c == '_' || c == '.' || c == LOCALCHAR || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) {
                start = new StringBuilder();

                do {
                    start.append(c);
                    c = src.deleteCharAt(0).length() > 0
                        ? src.charAt(0)
                        : 0;
                }
                while (c == '_' || c == '.' || c == LOCALCHAR || (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'));

                Label label = null;

                if (!skipDef) {
                    String directive = start.toString().startsWith(".") ? start.substring(1) : start.toString();

                    if ("IFDEF".equalsIgnoreCase(directive) || "IFNDEF".equalsIgnoreCase(directive)) {
                        skipDef = true;
                    } else {
                        label = findLabel(start.toString());
                    }
                }

                if (label != null) {
                    if (label.type != Asm8.Label.Type.EQUATE || label.pass != pass) {
                        label = null;
                    } else if (label.used) {
                        throw new RecurseEquException();
                    }
                }

                if (label != null) {
                    label.used = true;
                    expandLine(new StringBuilder((String) label.line), dst);
                    label.used = false;
                } else {
                    dst.append(start);
                }
            } else if (c == ';') {
                comment = src.toString();
                c = 0;
            } else {
                if (c != 0) {
                    dst.append(c);
                }

                if (src.length() > 0) {
                    src.deleteCharAt(0);
                }
            }
        }
        while (c != 0);

        return comment;
    }

    private void listLine(String src, String comment) {

    }

    private Label findLabel(String name) {
        List<Label> labelList = labelMap.get(name);

        if (labelList == null) {
            return null;
        }

        boolean nonFwdLabel = !name.startsWith("+");

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

        if (label != null && local && label.scope == 0 && label.type != Label.Type.VALUE) {
            label = null;
        }

        char c = word.charAt(0);

        if (c != LOCALCHAR && !local) {
            scope = nextScope++;
        }

        if (label == null) {
            labelHere = new Label(word, firstLabel.value, Label.Type.LABEL);
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
                if (label.type != Label.Type.VALUE) {
                    throw new LabelDefinedException();
                }
            } else {
                label.pass = pass;

                if (label.type == Label.Type.LABEL) {
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
            if ((label.type == Label.Type.MACRO && label.pass != pass) || label.type != Label.Type.RESERVED) {
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
                ret = getHexValue(s, ret);
            }
        } else if (c == '%') {
            s.deleteCharAt(0);
            ret = getBinValue(s, ret);
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
                    ret = getBinValue(s, ret);
                } else if (end == 'h' || end == 'H') {
                    ret = getHexValue(s, ret);
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
                dependant |= (label.line == null ? 1 : 0);
                needAnotherPass |= (label.line == null);

                if (label.type == Label.Type.LABEL || label.type == Label.Type.VALUE) {
                    ret = (int) label.value;
                } else if (label.type == Label.Type.MACRO) {
                    throw new Asm8Exception("Can't use macro in expression.");
                } else {
                    throw new UnknownLabelException();
                }
            }
        }

        return ret;
    }

    private int getHexValue(StringBuilder s, int ret) {
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

        return ret;
    }

    private int getBinValue(StringBuilder s, int ret) {
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
                ret = eval(s.deleteCharAt(0), Operator.Precedence.WHOLEEXP);

                eatLeadingWhiteSpace(s);

                if (s.length() > 0 && s.charAt(0) == ')') {
                    s.deleteCharAt(0);
                } else {
                    throw new IncompleteException();
                }
                break;
            case '#':
                ret = eval(s.deleteCharAt(0), Operator.Precedence.WHOLEEXP);
                break;
            case '~':
                ret = ~eval(s.deleteCharAt(0), Operator.Precedence.UNARY);
                break;
            case '!':
                ret = eval(s.deleteCharAt(0), Operator.Precedence.UNARY) == 0 ? 1 : 0;
                break;
            case '<':
                ret = eval(s.deleteCharAt(0), Operator.Precedence.UNARY) & 0xFF;
                break;
            case '>':
                ret = (eval(s.deleteCharAt(0), Operator.Precedence.UNARY) >> 8) & 0xFF;
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
                    ret = eval(s, Operator.Precedence.UNARY);

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

            if (precedence.compareTo(op.precedence) < 0) {
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
        while (precedence.compareTo(op.precedence) < 0);

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

    private void eatLeadingWhiteSpaceForFilename(StringBuilder src) {
        while (src.length() > 0 && whiteSpaceChars2.contains(src.charAt(0))) {
            src.deleteCharAt(0);
        }
    }

    private void eatTrailingWhiteSpaceForFilename(StringBuilder src) {
        while (src.length() > 0 && whiteSpaceChars2.contains(src.charAt(src.length() - 1))) {
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

    private void outputLE(int n, int size) {
        if (size == 0) {
            output();
        } else if (size == 1) {
            output((byte) n);
        } else {
            output((byte) n, (byte) (n >> 8));
        }
    }

    private void output(byte... bytes) {
        firstLabel.value = ((int) firstLabel.value) + bytes.length;

        if (noOutput) {
            return;
        }

        if (oldPass != pass) {
            oldPass = pass;

            try {
                outputStream = new BufferedOutputStream(new FileOutputStream(outputFileName, false));
            } catch (FileNotFoundException e) {
                throw new Asm8Exception("Can't create output file.");
            }
        }

        try {
            outputStream.write(bytes);
        } catch (IOException e) {
            throw new Asm8Exception("Write error.");
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

    @SuppressWarnings("unchecked")
    private void opcode(Label id, StringBuilder next) {
        boolean oldState = needAnotherPass;
        boolean forceRel = false;

        Map<OpType, Byte> line = (Map<OpType, Byte>) id.line;

        for (Entry<OpType, Byte> entry : line.entrySet()) {
            OpType type = entry.getKey();
            byte op = entry.getValue();
            int val = 0;
            needAnotherPass = oldState;
            dependant = 0;
            StringBuilder s = new StringBuilder(next);

            if (type != OpType.IMP && type != OpType.ACC) {
                try {
                    if (!eatChar(s, type.head)) {
                        continue;
                    }

                    val = eval(s, Operator.Precedence.WHOLEEXP);

                    if (type == OpType.REL) {
                        if (dependant == 0) {
                            val -= (int) firstLabel.value + 2;

                            if (val > Byte.MAX_VALUE || val < Byte.MIN_VALUE) {
                                needAnotherPass = true;

                                if (lastChance) {
                                    forceRel = true;
                                    throw new Asm8Exception("Branch out of range.");
                                }
                            }
                        }
                    } else {
                        if (type.size == 1) {
                            if (dependant == 0) {
                                if (val > 255 || val < Byte.MIN_VALUE) {
                                    throw new OutOfRangeException();
                                }
                            } else if (type != OpType.IMM) {
                                continue;
                            }
                        } else if ((val < 0 || val > 0xFFFF) && dependant == 0) {
                            throw new OutOfRangeException();
                        }
                    }
                } catch (Asm8Exception e) {
                    if (dependant == 0 && !forceRel) {
                        continue;
                    }

                    throw e;
                }
            }

            eatLeadingWhiteSpace(s);

            if (whiteSpaceRegex.matcher(s).replaceAll("").toUpperCase().startsWith(type.tail)) {
                if ((int) firstLabel.value > 0xFFFF) {
                    throw new Asm8Exception("PC out of range.");
                }

                output(op);
                outputLE(val, type.size);
                next.setLength(0);

                return;
            }
        }
    }

    private void nothing(Label id, StringBuilder next) {

    }

    private void _if(Label id, StringBuilder next) {
        if (ifLevel > IFNESTS - 1) {
            throw new IfNestLimitException();
        } else {
            ifLevel++;
        }

        dependant = 0;

        int val = eval(next, Operator.Precedence.WHOLEEXP);

        if (dependant != 0) {
            ifDone[ifLevel] = true;
            skipLine[ifLevel] = true;
        } else {
            skipLine[ifLevel] = val == 0 || skipLine[ifLevel - 1];
            ifDone[ifLevel] = !skipLine[ifLevel];
        }
    }

    private void elseif(Label id, StringBuilder next) {
        if (ifLevel != 0) {
            dependant = 0;
            int val = eval(next, Operator.Precedence.WHOLEEXP);

            if (!ifDone[ifLevel]) {
                if (dependant != 0) {
                    ifDone[ifLevel] = true;
                    skipLine[ifLevel] = true;
                } else {
                    skipLine[ifLevel] = val == 0 || skipLine[ifLevel - 1];
                    ifDone[ifLevel] = !skipLine[ifLevel];
                }
            } else {
                skipLine[ifLevel] = true;
            }
        } else {
            throw new Asm8Exception("ELSEIF without IF.");
        }
    }

    private void _else(Label id, StringBuilder next) {
        if (ifLevel != 0) {
            skipLine[ifLevel] = ifDone[ifLevel] || skipLine[ifLevel - 1];
        } else {
            throw new Asm8Exception("ELSE without IF.");
        }
    }

    private void endif(Label id, StringBuilder next) {
        if (ifLevel != 0) {
            ifLevel--;
        } else {
            throw new Asm8Exception("ENDIF without IF.");
        }
    }

    private void ifdef(Label id, StringBuilder next) {
        if (ifLevel >= IFNESTS - 1) {
            throw new IfNestLimitException();
        } else {
            ifLevel++;
        }

        String s = getLabel(next);
        skipLine[ifLevel] = findLabel(s) == null || skipLine[ifLevel - 1];
        ifDone[ifLevel] = !skipLine[ifLevel];
    }

    private void ifndef(Label id, StringBuilder next) {
        if (ifLevel >= IFNESTS - 1) {
            throw new IfNestLimitException();
        } else {
            ifLevel++;
        }

        String s = getLabel(next);
        skipLine[ifLevel] = findLabel(s) != null || skipLine[ifLevel - 1];
        ifDone[ifLevel] = !skipLine[ifLevel];
    }

    private void equal(Label id, StringBuilder next) {
        if (labelHere == null) {
            throw new NeedNameException();
        }

        dependant = 0;

        labelHere.type = Label.Type.VALUE;
        labelHere.value = eval(next, Operator.Precedence.WHOLEEXP);
        labelHere.line = dependant == 0 ? Boolean.TRUE : null;
    }

    private void equ(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void org(Label id, StringBuilder next) {
        if ((int) firstLabel.value < 0) {
            base(id, next);
        } else {
            pad(id, next);
        }
    }

    private void base(Label id, StringBuilder next) {
        dependant = 0;
        int val = eval(next, Operator.Precedence.WHOLEEXP);

        if (dependant == 0) {
            firstLabel.value = val;
        } else {
            firstLabel.value = NOORIGIN;
        }
    }

    private void pad(Label id, StringBuilder next) {
        if ((int) firstLabel.value < 0) {
            throw new UndefinedPCException();
        }

        dependant = 0;
        int count = eval(next, Operator.Precedence.WHOLEEXP) - (int) firstLabel.value;
        filler(count, next);
    }

    private void include(Label id, StringBuilder next) {
        eatLeadingWhiteSpaceForFilename(next);
        eatTrailingWhiteSpaceForFilename(next);

        processFile(new File(next.toString()));

        next.setLength(0);
    }

    private void incbin(Label id, StringBuilder next) {
        eatLeadingWhiteSpace(next);
        String filename;

        if (next.toString().startsWith("\"")) {
            int end = next.indexOf("\"", 1);

            if (end < 0) {
                end = next.length();
            }

            filename = next.substring(1, end);
            next.delete(0, end + 1);
        } else {
            StringBuilder tmp = new StringBuilder();
            getWord(next, tmp, false);
            filename = tmp.toString();
        }

        try (RandomAccessFile file = new RandomAccessFile(filename, "r")) {
            long fileSize = file.length();
            int seekPos = eatChar(next, ',')
                          ? eval(next, Operator.Precedence.WHOLEEXP)
                          : 0;
            if (dependant == 0 && (seekPos < 0 || seekPos > fileSize)) {
                throw new SeeKOutOfRangeException();
            }

            int bytesToRead = eatChar(next, ',')
                              ? eval(next, Operator.Precedence.WHOLEEXP)
                              : (int) (fileSize - seekPos);

            if (dependant == 0 && (bytesToRead < 0 || bytesToRead > fileSize - seekPos)) {
                throw new BadIncbinSizeException();
            }

            byte[] bytes = new byte[bytesToRead];

            if (seekPos > 0) {
                file.seek(seekPos);
                file.read(bytes);
            } else {
                file.readFully(bytes);
            }

            output(bytes);
        } catch (IOException e) {
            throw new CantOpenException();
        }
    }

    private void hex(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void dw(Label id, StringBuilder next) {
        do {
            int val = eval(next, Operator.Precedence.WHOLEEXP);

            if (val > 65535 || val < -65536) {
                throw new OutOfRangeException();
            }

            outputLE(val, 2);
        }
        while (eatChar(next, ','));
    }

    private void db(Label id, StringBuilder next) {
        do {
            eatLeadingWhiteSpace(next);
            char quote = next.length() > 0 ? next.charAt(0) : 0;

            if (quote == '"' || quote == '\'') {
                try {
                    while (next.deleteCharAt(0).charAt(0) != quote) {
                        if (next.charAt(0) != '\'') {
                            outputLE(next.charAt(0), 1);
                        }
                    }
                } catch (Exception e) {
                    throw new IncompleteException();
                }

                next.deleteCharAt(0);
            } else {
                int val = eval(next, Operator.Precedence.WHOLEEXP);

                if (val > 255 || val < Byte.MIN_VALUE) {
                    throw new OutOfRangeException();
                }

                outputLE(val, 1);
            }
        }
        while (eatChar(next, ','));
    }

    private void dsw(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void dsb(Label id, StringBuilder next) {
        dependant = 0;
        int count = eval(next, Operator.Precedence.WHOLEEXP);
        filler(count, next);
    }

    private void align(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void macro(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void rept(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void endm(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void endr(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void _enum(Label id, StringBuilder next) {
        dependant = 0;
        int val = eval(next, Operator.Precedence.WHOLEEXP);

        if (!noOutput) {
            enumSaveAddr = (int) firstLabel.value;
        }

        firstLabel.value = val;
        noOutput = true;
    }

    private void ende(Label id, StringBuilder next) {
        if (noOutput) {
            firstLabel.value = enumSaveAddr;
            noOutput = false;
        } else {
            throw new ExtraEndEException();
        }
    }

    private void fillval(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void dl(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void dh(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void makeError(Label id, StringBuilder next) {
        throw new Asm8Exception("Not implemented yet.");
    }

    private void filler(int count, StringBuilder next) {
        if (dependant != 0 || (count < 0 && needAnotherPass)) {
            count = 0;
        }

        int val = eatChar(next, ',')
                  ? eval(next, Operator.Precedence.WHOLEEXP)
                  : defaultFiller;

        if (dependant == 0 && (val > 255 || val < -128 || count < 0 || count > 0x100000)) {
            throw new OutOfRangeException();
        }

        while (count-- > 0) {
            outputLE(val, 1);
        }
    }

    public static class Asm8Exception extends RuntimeException {

        public Asm8Exception(String message) {
            super(message);
        }
    }

    public static class OutOfRangeException extends Asm8Exception {

        public OutOfRangeException() {
            super("Value out of range.");
        }
    }

    public static class SeeKOutOfRangeException extends Asm8Exception {

        public SeeKOutOfRangeException() {
            super("Seek position out of range.");
        }
    }

    public static class BadIncbinSizeException extends Asm8Exception {

        public BadIncbinSizeException() {
            super("INCBIN size is out of range.");
        }
    }

    public static class NotANumberException extends Asm8Exception {

        public NotANumberException() {
            super("Not a number.");
        }
    }

    public static class UnknownLabelException extends Asm8Exception {

        public UnknownLabelException() {
            super("Unknown label.");
        }
    }

    public static class IllegalException extends Asm8Exception {

        public IllegalException() {
            super("Illegal instruction.");
        }
    }

    public static class IncompleteException extends Asm8Exception {

        public IncompleteException() {
            super("Incomplete expression.");
        }
    }

    public static class LabelDefinedException extends Asm8Exception {

        public LabelDefinedException() {
            super("Label already defined.");
        }
    }

    public static class MissingOperandException extends Asm8Exception {

        public MissingOperandException() {
            super("Missing operand.");
        }
    }

    public static class DivideByZeroException extends Asm8Exception {

        public DivideByZeroException() {
            super("Divide by zero.");
        }
    }

    public static class BadAddrException extends Asm8Exception {

        public BadAddrException() {
            super("Can't determine address.");
        }
    }

    public static class NeedNameException extends Asm8Exception {

        public NeedNameException() {
            super("Need a name.");
        }
    }

    public static class CantOpenException extends Asm8Exception {

        public CantOpenException() {
            super("Can't open file.");
        }
    }

    public static class ExtraEndMException extends Asm8Exception {

        public ExtraEndMException() {
            super("ENDM without MACRO.");
        }
    }

    public static class ExtraEndRException extends Asm8Exception {

        public ExtraEndRException() {
            super("ENDR without REPT.");
        }
    }

    public static class ExtraEndEException extends Asm8Exception {

        public ExtraEndEException() {
            super("ENDE without ENUM.");
        }
    }

    public static class RecurseMacroException extends Asm8Exception {

        public RecurseMacroException() {
            super("Recursive MACRO not allowed.");
        }
    }

    public static class RecurseEquException extends Asm8Exception {

        public RecurseEquException() {
            super("Recursive EQU not allowed.");
        }
    }

    public static class MissingEndifException extends Asm8Exception {

        public MissingEndifException() {
            super("Missing ENDIF.");
        }
    }

    public static class MissingEndMException extends Asm8Exception {

        public MissingEndMException() {
            super("Missing ENDM.");
        }
    }

    public static class MissingEndRException extends Asm8Exception {

        public MissingEndRException() {
            super("Missing ENDR.");
        }
    }

    public static class MissingEndEException extends Asm8Exception {

        public MissingEndEException() {
            super("Missing ENDE.");
        }
    }

    public static class IfNestLimitException extends Asm8Exception {

        public IfNestLimitException() {
            super("Too many nested IFs.");
        }
    }

    public static class UndefinedPCException extends Asm8Exception {

        public UndefinedPCException() {
            super("PC is undefined (use ORG first)");
        }
    }

    private static Map<OpType, Byte> opMap(Object... objects) {
        Map<OpType, Byte> map = new LinkedHashMap<>();

        for (int i = 0; i < objects.length; i += 2) {
            map.put((OpType) objects[i + 1], ((Integer) objects[i]).byteValue());
        }

        return map;
    }
}
