package org.parisoft.asm8;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;

import static org.parisoft.asm8.Asm8.Label.Type.RESERVED;
import static org.parisoft.asm8.Asm8.optypes.ABS;
import static org.parisoft.asm8.Asm8.optypes.ABSX;
import static org.parisoft.asm8.Asm8.optypes.ABSY;
import static org.parisoft.asm8.Asm8.optypes.ACC;
import static org.parisoft.asm8.Asm8.optypes.IMM;
import static org.parisoft.asm8.Asm8.optypes.IMP;
import static org.parisoft.asm8.Asm8.optypes.IND;
import static org.parisoft.asm8.Asm8.optypes.INDX;
import static org.parisoft.asm8.Asm8.optypes.INDY;
import static org.parisoft.asm8.Asm8.optypes.REL;
import static org.parisoft.asm8.Asm8.optypes.ZP;
import static org.parisoft.asm8.Asm8.optypes.ZPX;
import static org.parisoft.asm8.Asm8.optypes.ZPY;

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

    enum optypes {ACC, IMM, IND, INDX, INDY, ZPX, ZPY, ABSX, ABSY, ZP, ABS, REL, IMP}

    private static final int[] opsize = {0, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 0};
    private static final char[] ophead = {0, '#', '(', '(', '(', 0, 0, 0, 0, 0, 0, 0, 0};
    private static final String[] optail = {"A", "", ")", ",X)", "),Y", ",X", ",Y", ",X", ",Y", "", "", "", ""};

    static class Label {

        enum Type {
            LABEL, VALUE, EQUATE, MACRO, RESERVED
        }

        public Label(String name, Type type) {
            this.name = name;
            this.type = type;
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
        int used = 0;
        int pass = 0;
        int scope = 0;
    }

    private int pass = 0;
    private int scope = 0;
    private int nextScope;
    private boolean lastChance = false;
    private boolean needAnotherPass = false;
    private boolean[] skipline = new boolean[IFNESTS];
    private int defaultFiller;
    private final Map<String, List<Label>> labelList = new HashMap<>();
    private Label firstLabel = new Label("$", Label.Type.VALUE);
    private Label lastLabel;
    private int nestedIncludes = 0;
    private int ifLevel = 0;
    private int reptCount = 0;
    private Object makeMacro = null;
    private boolean noOutput = false;

    public static void main(String[] args) {
        if (args.length < 1) {
            System.out.println();
            System.out.println("asm8 " + VERSION);
            System.out.println("Usage:  asm8 [-options] sourcefile [outputfile] [listfile]");
            System.out.println("    -?          show this help");
            System.out.println("    -l          create listing");
            System.out.println("    -L          create verbose listing (expand REPT, MACRO)");
            System.out.println("    -d<name>    define symbol");
            System.out.println("    -q          quiet mode (no output unless error)");
            System.out.println("See README.TXT for more info.");
            System.exit(1);
        }

        try {
            new Asm8().compile(args[1]);
        } catch (Exception e) {
            System.err.println(e.getMessage());
        }
    }

    public void compile(String filename) {
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
            skipline[0] = false;
            scope = 1;
            nextScope = 2;
            defaultFiller = DEFAULTFILLER;
            firstLabel.value = NOORIGIN;
            currLabel = lastLabel;

            include(null, filename);
        }
        while (!lastChance && needAnotherPass);
    }

    private void initLabels() {
        BiConsumer<Label, String> opcode = (o, o2) -> opcode(o, o2);
        labelList.putIfAbsent("BRK", new ArrayList<>()).add(new Label("BRK", opcode, new Object[]{0x00, IMM, 0x00, ZP, 0x00, IMP, -1}, RESERVED));
        labelList.putIfAbsent("CLC", new ArrayList<>()).add(new Label("CLC", opcode, new Object[]{0x08, IMP, -1}, RESERVED));
        labelList.putIfAbsent("JSR", new ArrayList<>()).add(new Label("JSR", opcode, new Object[]{0x10, REL, -1}, RESERVED));
        labelList.putIfAbsent("PLP", new ArrayList<>()).add(new Label("PLP", opcode, new Object[]{0x18, IMP, -1}, RESERVED));
        labelList.putIfAbsent("BMI", new ArrayList<>()).add(new Label("BMI", opcode, new Object[]{0x20, ABS, -1}, RESERVED));
        labelList.putIfAbsent("RTI", new ArrayList<>()).add(new Label("RTI", opcode, new Object[]{0x24, ZP, 0x2c, ABS, -1}, RESERVED));
        labelList.putIfAbsent("BVC", new ArrayList<>()).add(new Label("BVC", opcode, new Object[]{0x28, IMP, -1}, RESERVED));
        labelList.putIfAbsent("CLI", new ArrayList<>()).add(new Label("CLI", opcode, new Object[]{0x30, REL, -1}, RESERVED));
        labelList.putIfAbsent("RTS", new ArrayList<>()).add(new Label("RTS", opcode, new Object[]{0x38, IMP, -1}, RESERVED));
        labelList.putIfAbsent("PLA", new ArrayList<>()).add(new Label("PLA", opcode, new Object[]{0x40, IMP, -1}, RESERVED));
        labelList.putIfAbsent("DEY", new ArrayList<>()).add(new Label("DEY", opcode, new Object[]{0x48, IMP, -1}, RESERVED));
        labelList.putIfAbsent("BCC", new ArrayList<>()).add(new Label("BCC", opcode, new Object[]{0x6c, IND, 0x4c, ABS, -1}, RESERVED));
        labelList.putIfAbsent("TYA", new ArrayList<>()).add(new Label("TYA", opcode, new Object[]{0x50, REL, -1}, RESERVED));
        labelList.putIfAbsent("LDY", new ArrayList<>()).add(new Label("LDY", opcode, new Object[]{0x58, IMP, -1}, RESERVED));
        labelList.putIfAbsent("TAY", new ArrayList<>()).add(new Label("TAY", opcode, new Object[]{0x60, IMP, -1}, RESERVED));
        labelList.putIfAbsent("CPY", new ArrayList<>()).add(new Label("CPY", opcode, new Object[]{0x68, IMP, -1}, RESERVED));
        labelList.putIfAbsent("INY", new ArrayList<>()).add(new Label("INY", opcode, new Object[]{0x70, REL, -1}, RESERVED));
        labelList.putIfAbsent("BNE", new ArrayList<>()).add(new Label("BNE", opcode, new Object[]{0x78, IMP, -1}, RESERVED));
        labelList.putIfAbsent("CPX", new ArrayList<>()).add(new Label("CPX", opcode, new Object[]{0x94, ZPX, 0x84, ZP, 0x8c, ABS, -1}, RESERVED));
        labelList.putIfAbsent("INX", new ArrayList<>()).add(new Label("INX", opcode, new Object[]{0x96, ZPY, 0x86, ZP, 0x8e, ABS, -1}, RESERVED));
        labelList.putIfAbsent("BEQ", new ArrayList<>()).add(new Label("BEQ", opcode, new Object[]{0x88, IMP, -1}, RESERVED));
        labelList.putIfAbsent("SED", new ArrayList<>()).add(new Label("SED", opcode, new Object[]{0x8a, IMP, -1}, RESERVED));
        labelList.putIfAbsent("ORA", new ArrayList<>()).add(new Label("ORA", opcode, new Object[]{0x90, REL, -1}, RESERVED));
        labelList.putIfAbsent("AND", new ArrayList<>()).add(new Label("AND", opcode, new Object[]{0x98, IMP, -1}, RESERVED));
        labelList.putIfAbsent("EOR", new ArrayList<>()).add(new Label("EOR", opcode, new Object[]{0x9a, IMP, -1}, RESERVED));
        labelList.putIfAbsent("ADC", new ArrayList<>()).add(new Label("ADC", opcode, new Object[]{0xa0, IMM, 0xb4, ZPX, 0xbc, ABSX, 0xa4, ZP, 0xac, ABS, -1}, RESERVED));
        labelList.putIfAbsent("LDA", new ArrayList<>()).add(new Label("LDA", opcode, new Object[]{0xa2, IMM, 0xb6, ZPY, 0xbe, ABSY, 0xa6, ZP, 0xae, ABS, -1}, RESERVED));
        labelList.putIfAbsent("CMP", new ArrayList<>()).add(new Label("CMP", opcode, new Object[]{0xa8, IMP, -1}, RESERVED));
        labelList.putIfAbsent("SBC", new ArrayList<>()).add(new Label("SBC", opcode, new Object[]{0xaa, IMP, -1}, RESERVED));
        labelList.putIfAbsent("ASL", new ArrayList<>()).add(new Label("ASL", opcode, new Object[]{0xb0, REL, -1}, RESERVED));
        labelList.putIfAbsent("ROL", new ArrayList<>()).add(new Label("ROL", opcode, new Object[]{0xb8, IMP, -1}, RESERVED));
        labelList.putIfAbsent("LSR", new ArrayList<>()).add(new Label("LSR", opcode, new Object[]{0xba, IMP, -1}, RESERVED));
        labelList.putIfAbsent("ROR", new ArrayList<>()).add(new Label("ROR", opcode, new Object[]{0xc0, IMM, 0xc4, ZP, 0xcc, ABS, -1}, RESERVED));
        labelList.putIfAbsent("TXS", new ArrayList<>()).add(new Label("TXS", opcode, new Object[]{0xd6, ZPX, 0xde, ABSX, 0xc6, ZP, 0xce, ABS, -1}, RESERVED));
        labelList.putIfAbsent("LDX", new ArrayList<>()).add(new Label("LDX", opcode, new Object[]{0xc8, IMP, -1}, RESERVED));
        labelList.putIfAbsent("TAX", new ArrayList<>()).add(new Label("TAX", opcode, new Object[]{0xca, IMP, -1}, RESERVED));
        labelList.putIfAbsent("TSX", new ArrayList<>()).add(new Label("TSX", opcode, new Object[]{0xd0, REL, -1}, RESERVED));
        labelList.putIfAbsent("DEX", new ArrayList<>()).add(new Label("DEX", opcode, new Object[]{0xd8, IMP, -1}, RESERVED));
        labelList.putIfAbsent("NOP", new ArrayList<>()).add(new Label("NOP", opcode, new Object[]{0xe0, IMM, 0xe4, ZP, 0xec, ABS, -1}, RESERVED));
        labelList.putIfAbsent("JMP", new ArrayList<>()).add(new Label("JMP", opcode, new Object[]{0xf6, ZPX, 0xfe, ABSX, 0xe6, ZP, 0xee, ABS, -1}, RESERVED));
        labelList.putIfAbsent("STY", new ArrayList<>()).add(new Label("STY", opcode, new Object[]{0xe8, IMP, -1}, RESERVED));
        labelList.putIfAbsent("STX", new ArrayList<>()).add(new Label("STX", opcode, new Object[]{0xea, IMP, -1}, RESERVED));
        labelList.putIfAbsent("DEC", new ArrayList<>()).add(new Label("DEC", opcode, new Object[]{0xf0, REL, -1}, RESERVED));
        labelList.putIfAbsent("INC", new ArrayList<>()).add(new Label("INC", opcode, new Object[]{0xf8, IMP, -1}, RESERVED));
        labelList.putIfAbsent("PHP", new ArrayList<>()).add(new Label("PHP",
                                                                      opcode,
                                                                      new Object[]{0x09, IMM, 0x01, INDX, 0x11, INDY, 0x15, ZPX, 0x1d, ABSX, 0x19, ABSY, 0x05, ZP, 0x0d, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("BPL", new ArrayList<>()).add(new Label("BPL",
                                                                      opcode,
                                                                      new Object[]{0x0a, ACC, 0x16, ZPX, 0x1e, ABSX, 0x06, ZP, 0x0e, ABS, 0x0a, IMP, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("SEC", new ArrayList<>()).add(new Label("SEC",
                                                                      opcode,
                                                                      new Object[]{0x29, IMM, 0x21, INDX, 0x31, INDY, 0x35, ZPX, 0x3d, ABSX, 0x39, ABSY, 0x25, ZP, 0x2d, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("PHA", new ArrayList<>()).add(new Label("PHA",
                                                                      opcode,
                                                                      new Object[]{0x2a, ACC, 0x36, ZPX, 0x3e, ABSX, 0x26, ZP, 0x2e, ABS, 0x2a, IMP, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("BVS", new ArrayList<>()).add(new Label("BVS",
                                                                      opcode,
                                                                      new Object[]{0x49, IMM, 0x41, INDX, 0x51, INDY, 0x55, ZPX, 0x5d, ABSX, 0x59, ABSY, 0x45, ZP, 0x4d, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("SEI", new ArrayList<>()).add(new Label("SEI",
                                                                      opcode,
                                                                      new Object[]{0x4a, ACC, 0x56, ZPX, 0x5e, ABSX, 0x46, ZP, 0x4e, ABS, 0x4a, IMP, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("BCS", new ArrayList<>()).add(new Label("BCS",
                                                                      opcode,
                                                                      new Object[]{0x69, IMM, 0x61, INDX, 0x71, INDY, 0x75, ZPX, 0x7d, ABSX, 0x79, ABSY, 0x65, ZP, 0x6d, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("CLV", new ArrayList<>()).add(new Label("CLV",
                                                                      opcode,
                                                                      new Object[]{0x6a, ACC, 0x76, ZPX, 0x7e, ABSX, 0x66, ZP, 0x6e, ABS, 0x6a, IMP, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("CLD", new ArrayList<>()).add(new Label("CLD",
                                                                      opcode,
                                                                      new Object[]{0x81, INDX, 0x91, INDY, 0x95, ZPX, 0x9d, ABSX, 0x99, ABSY, 0x85, ZP, 0x8d, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("STA", new ArrayList<>()).add(new Label("STA",
                                                                      opcode,
                                                                      new Object[]{0xa9, IMM, 0xa1, INDX, 0xb1, INDY, 0xb5, ZPX, 0xbd, ABSX, 0xb9, ABSY, 0xa5, ZP, 0xad, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("TXA", new ArrayList<>()).add(new Label("TXA",
                                                                      opcode,
                                                                      new Object[]{0xc9, IMM, 0xc1, INDX, 0xd1, INDY, 0xd5, ZPX, 0xdd, ABSX, 0xd9, ABSY, 0xc5, ZP, 0xcd, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("BIT", new ArrayList<>()).add(new Label("BIT",
                                                                      opcode,
                                                                      new Object[]{0xe9, IMM, 0xe1, INDX, 0xf1, INDY, 0xf5, ZPX, 0xfd, ABSX, 0xf9, ABSY, 0xe5, ZP, 0xed, ABS, -1},
                                                                      RESERVED));
        labelList.putIfAbsent("", new ArrayList<>()).add(new Label("", (BiConsumer<Label, String>) this::nothing, RESERVED));
        labelList.putIfAbsent("IF", new ArrayList<>()).add(new Label("IF", (BiConsumer<Label, String>) this::_if, RESERVED));
        labelList.putIfAbsent("ELSEIF", new ArrayList<>()).add(new Label("ELSEIF", (BiConsumer<Label, String>) this::elseif, RESERVED));
        labelList.putIfAbsent("ELSE", new ArrayList<>()).add(new Label("ELSE", (BiConsumer<Label, String>) this::_else, RESERVED));
        labelList.putIfAbsent("ENDIF", new ArrayList<>()).add(new Label("ENDIF", (BiConsumer<Label, String>) this::endif, RESERVED));
        labelList.putIfAbsent("IFDEF", new ArrayList<>()).add(new Label("IFDEF", (BiConsumer<Label, String>) this::ifdef, RESERVED));
        labelList.putIfAbsent("IFNDEF", new ArrayList<>()).add(new Label("IFNDEF", (BiConsumer<Label, String>) this::ifndef, RESERVED));
        labelList.putIfAbsent("=", new ArrayList<>()).add(new Label("=", (BiConsumer<Label, String>) this::equal, RESERVED));
        labelList.putIfAbsent("EQU", new ArrayList<>()).add(new Label("EQU", (BiConsumer<Label, String>) this::equ, RESERVED));
        labelList.putIfAbsent("ORG", new ArrayList<>()).add(new Label("ORG", (BiConsumer<Label, String>) this::org, RESERVED));
        labelList.putIfAbsent("BASE", new ArrayList<>()).add(new Label("BASE", (BiConsumer<Label, String>) this::base, RESERVED));
        labelList.putIfAbsent("PAD", new ArrayList<>()).add(new Label("PAD", (BiConsumer<Label, String>) this::pad, RESERVED));
        labelList.putIfAbsent("INCLUDE", new ArrayList<>()).add(new Label("INCLUDE", (BiConsumer<Label, String>) this::include, RESERVED));
        labelList.putIfAbsent("INCSRC", new ArrayList<>()).add(new Label("INCSRC", (BiConsumer<Label, String>) this::include, RESERVED));
        labelList.putIfAbsent("INCBIN", new ArrayList<>()).add(new Label("INCBIN", (BiConsumer<Label, String>) this::incbin, RESERVED));
        labelList.putIfAbsent("BIN", new ArrayList<>()).add(new Label("BIN", (BiConsumer<Label, String>) this::incbin, RESERVED));
        labelList.putIfAbsent("HEX", new ArrayList<>()).add(new Label("HEX", (BiConsumer<Label, String>) this::hex, RESERVED));
        labelList.putIfAbsent("WORD", new ArrayList<>()).add(new Label("WORD", (BiConsumer<Label, String>) this::dw, RESERVED));
        labelList.putIfAbsent("DW", new ArrayList<>()).add(new Label("DW", (BiConsumer<Label, String>) this::dw, RESERVED));
        labelList.putIfAbsent("DCW", new ArrayList<>()).add(new Label("DCW", (BiConsumer<Label, String>) this::dw, RESERVED));
        labelList.putIfAbsent("DC.W", new ArrayList<>()).add(new Label("DC.W", (BiConsumer<Label, String>) this::dw, RESERVED));
        labelList.putIfAbsent("BYTE", new ArrayList<>()).add(new Label("BYTE", (BiConsumer<Label, String>) this::db, RESERVED));
        labelList.putIfAbsent("DB", new ArrayList<>()).add(new Label("DB", (BiConsumer<Label, String>) this::db, RESERVED));
        labelList.putIfAbsent("DCB", new ArrayList<>()).add(new Label("DCB", (BiConsumer<Label, String>) this::db, RESERVED));
        labelList.putIfAbsent("DC.B", new ArrayList<>()).add(new Label("DC.B", (BiConsumer<Label, String>) this::db, RESERVED));
        labelList.putIfAbsent("DSW", new ArrayList<>()).add(new Label("DSW", (BiConsumer<Label, String>) this::dsw, RESERVED));
        labelList.putIfAbsent("DS.W", new ArrayList<>()).add(new Label("DS.W", (BiConsumer<Label, String>) this::dsw, RESERVED));
        labelList.putIfAbsent("DSB", new ArrayList<>()).add(new Label("DSB", (BiConsumer<Label, String>) this::dsb, RESERVED));
        labelList.putIfAbsent("DS.B", new ArrayList<>()).add(new Label("DS.B", (BiConsumer<Label, String>) this::dsb, RESERVED));
        labelList.putIfAbsent("ALIGN", new ArrayList<>()).add(new Label("ALIGN", (BiConsumer<Label, String>) this::align, RESERVED));
        labelList.putIfAbsent("MACRO", new ArrayList<>()).add(new Label("MACRO", (BiConsumer<Label, String>) this::macro, RESERVED));
        labelList.putIfAbsent("REPT", new ArrayList<>()).add(new Label("REPT", (BiConsumer<Label, String>) this::rept, RESERVED));
        labelList.putIfAbsent("ENDM", new ArrayList<>()).add(new Label("ENDM", (BiConsumer<Label, String>) this::endm, RESERVED));
        labelList.putIfAbsent("ENDR", new ArrayList<>()).add(new Label("ENDR", (BiConsumer<Label, String>) this::endr, RESERVED));
        labelList.putIfAbsent("ENUM", new ArrayList<>()).add(new Label("ENUM", (BiConsumer<Label, String>) this::_enum, RESERVED));
        labelList.putIfAbsent("ENDE", new ArrayList<>()).add(new Label("ENDE", (BiConsumer<Label, String>) this::ende, RESERVED));
        labelList.putIfAbsent("FILLVALUE", new ArrayList<>()).add(new Label("FILLVALUE", (BiConsumer<Label, String>) this::fillval, RESERVED));
        labelList.putIfAbsent("DL", new ArrayList<>()).add(new Label("DL", (BiConsumer<Label, String>) this::dl, RESERVED));
        labelList.putIfAbsent("DH", new ArrayList<>()).add(new Label("DH", (BiConsumer<Label, String>) this::dh, RESERVED));
        labelList.putIfAbsent("ERROR", new ArrayList<>()).add(new Label("ERROR", (BiConsumer<Label, String>) this::makeError, RESERVED));
    }

    private void processFile(File file) {
        int nline = 0;
        nestedIncludes++;

        try {
            nline++;

            for (String line : Files.readAllLines(file.toPath())) {
                processLine(line, file.getName(), nline);
            }

            nline--;
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
            throwError("Can't open or read file - " + e.getMessage(), file.getName(), --nline);
        } catch (Exception e) {
            throwError(e, file.getName(), --nline);
        }
    }

    private void processLine(String src, String filename, int line) {

    }

    private String expandLine(String src, StringBuilder dst) {
        int i = 0;
        char c = 0;
        char c2 = 0;
        boolean defSkip = false;
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
                            i++;
                            dst.append(src.charAt(i));
                        }

                        i++;
                    }
                    while (c2 != 0 && c2 != c);

                    c = c2;
                } else if (c == '_' || c == '.' || c == LOCALCHAR || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) {
                    start = src.substring(i);

                    do {
                        i++;
                    }
                    while (c == '_' || c == '.' || c == LOCALCHAR || (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'));
                }
            } catch (StringIndexOutOfBoundsException e) {
                return null;
            }
        }
    }

    private void throwError(Throwable t, String filename, int line) {
        throw new RuntimeException(String.format("%s(%i): %s", filename, line, t.getMessage()));
    }

    private void throwError(String message, String filename, int line) {
        throw new RuntimeException(String.format("%s(%i): %s", filename, line, message));
    }

    //------------------------------------------
    // Opcodes and Directives
    //------------------------------------------

    private void opcode(Label id, String next) {

    }

    private void nothing(Label id, String next) {

    }

    private void _if(Label id, String next) {

    }

    private void elseif(Label id, String next) {

    }

    private void _else(Label id, String next) {

    }

    private void endif(Label id, String next) {

    }

    private void ifdef(Label id, String next) {

    }

    private void ifndef(Label id, String next) {

    }

    private void equal(Label id, String next) {

    }

    private void equ(Label id, String next) {

    }

    private void org(Label id, String next) {

    }

    private void base(Label id, String next) {

    }

    private void pad(Label id, String next) {

    }

    private void include(Label id, String next) {
        processFile(new File(next.trim()));
    }

    private void incbin(Label id, String next) {

    }

    private void hex(Label id, String next) {

    }

    private void dw(Label id, String next) {

    }

    private void db(Label id, String next) {

    }

    private void dsw(Label id, String next) {

    }

    private void dsb(Label id, String next) {

    }

    private void align(Label id, String next) {

    }

    private void macro(Label id, String next) {

    }

    private void rept(Label id, String next) {

    }

    private void endm(Label id, String next) {

    }

    private void endr(Label id, String next) {

    }

    private void _enum(Label id, String next) {

    }

    private void ende(Label id, String next) {

    }

    private void fillval(Label id, String next) {

    }

    private void dl(Label id, String next) {

    }

    private void dh(Label id, String next) {

    }

    private void makeError(Label id, String next) {

    }
}
