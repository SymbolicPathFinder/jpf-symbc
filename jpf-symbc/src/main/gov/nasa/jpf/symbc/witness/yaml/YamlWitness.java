package gov.nasa.jpf.symbc.witness.yaml;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicCharAtInteger;
import gov.nasa.jpf.symbc.string.SymbolicLengthInteger;
import gov.nasa.jpf.symbc.witness.PathConditionParser;
import gov.nasa.jpf.symbc.witness.SymbolicVariableInfo;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.VM;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.time.Instant;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.UUID;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Writes SV-COMP witnesses in the YAML format (version 2.4, Java)"
 * a violation_sequence (function_return waypoints for the Verifier.nondet* calls of the
 * violating path, then a target waypoint), or an empty invariant_set (correctness witness).
 *
 * Config (set by jr-sv-comp.sh): witness.input_files (comma list of the task's .java files,
 * as passed to the tool) and witness.property_file (the .prp file).
 */
public class YamlWitness {

  static String outputFilePath = "witness.yml";

  /**
   * Latest nondet value recorded for each Verifier counter value k (sym names are "int"+k, ...).
   * Verifier.counter is backtracked JPF state and the search is depth-first, so at a violation
   * the latest entry for every k below the current counter belongs to the violating path.
   */
  static final TreeMap<Integer, SymbolicVariableInfo> nondetByCounter = new TreeMap<>();
  static final Pattern COUNTER = Pattern.compile("^[A-Za-z]+(\\d+)");

  public static void recordNondet(SymbolicVariableInfo info) {
    Matcher m = COUNTER.matcher(info.varSymName);
    if (m.find())
      nondetByCounter.put(Integer.parseInt(m.group(1)), info);
  }

  public static void writeCorrectnessWitness() {
    write(header("invariant_set") + "  content: []\n");
  }

  /** @param pc the solved path condition of the violation, or null if there is none */
  public static void writeViolationWitness(PathCondition pc) {
    List<SymbolicVariableInfo> path = new ArrayList<>(
        nondetByCounter.headMap(verifierCounter()).values());
    for (SymbolicVariableInfo info : path)
      info.varValue = null;
    if (pc != null) {
      new PathConditionParser().parseSymVar(pc, path);
      List<String> names = new ArrayList<>();
      for (SymbolicVariableInfo info : path)
        names.add(info.varSymName);
      try {
        Map<String, Object> model = pc.solveWithValuations(names);
        for (SymbolicVariableInfo info : path)
          if (model != null && model.get(info.varSymName) != null && !info.returnType.contains("String"))
            info.varValue = model.get(info.varSymName);
      } catch (Throwable t) { // keep the values parsed from the PC
      }
    }

    StringBuilder sb = new StringBuilder(header("violation_sequence"));
    sb.append("  content:\n");
    for (SymbolicVariableInfo info : path) {
      String value = javaConstraint(info, pc);
      if (value == null)
        continue;
      sb.append("  - segment:\n");
      sb.append("    - waypoint:\n");
      sb.append("        type: \"function_return\"\n");
      sb.append("        action: \"follow\"\n");
      sb.append("        constraint:\n");
      sb.append("          value: ").append(quote(value)).append("\n");
      sb.append("          format: \"ext_java_expression\"\n");
      String file = inputFileFor(info.sourceFile);
      sb.append("        location:\n");
      sb.append("          file_name: ").append(quote(file)).append("\n");
      sb.append("          line: ").append(info.lineNumber).append("\n");
      int column = nondetColumn(file, info.lineNumber);
      if (column > 0)
        sb.append("          column: ").append(column).append("\n");
    }
    String[] target = targetLocation();
    sb.append("  - segment:\n");
    sb.append("    - waypoint:\n");
    sb.append("        type: \"target\"\n");
    sb.append("        action: \"follow\"\n");
    sb.append("        location:\n");
    sb.append("          file_name: ").append(quote(target[0])).append("\n");
    sb.append("          line: ").append(target[1]).append("\n");
    write(sb.toString());
  }

  // ---------------------------------------------------------------- constraints

  /** The ext_java_expression for the value returned by this nondet call, or null if unsupported. */
  static String javaConstraint(SymbolicVariableInfo info, PathCondition pc) {
    String type = info.returnType;
    Object v = info.varValue;
    switch (type) {
      case "int": case "short": case "byte":
        return "\\result == " + (v == null ? 4 : Long.parseLong(v.toString()));
      case "long":
        return "\\result == " + (v == null ? 4 : Long.parseLong(v.toString())) + "L";
      case "char":
        return "\\result == '" + escapeChar((char) (v == null ? 4 : Long.parseLong(v.toString()))) + "'";
      case "boolean":
        return "\\result == " + (v == null || v.toString().equals("true") || v.toString().matches("-?[1-9]\\d*"));
      case "float": {
        float f = v == null ? 2.0f : (float) Double.parseDouble(v.toString());
        if (Float.isNaN(f)) return "\\result == Float.NaN";
        if (Float.isInfinite(f)) return "\\result == Float." + (f > 0 ? "POSITIVE" : "NEGATIVE") + "_INFINITY";
        return "\\result == " + Float.toString(f) + "f";
      }
      case "double": {
        double d = v == null ? 2.0 : Double.parseDouble(v.toString());
        if (Double.isNaN(d)) return "\\result == Double.NaN";
        if (Double.isInfinite(d)) return "\\result == Double." + (d > 0 ? "POSITIVE" : "NEGATIVE") + "_INFINITY";
        return "\\result == " + Double.toString(d);
      }
      case "java.lang.String": {
        // raw solution of the string solver, not the backslash-escaped one kept for GraphML
        String s = (pc == null || pc.spc == null) ? null : pc.spc.solution.get(info.varSymName);
        boolean fromSolver = s != null; // Z3 literal: needs SMT-LIB unescaping below
        if (s == null && pc != null)
          s = stringFromNumericModel(pc, info.varSymName);
        if (s == null) s = "";
        if (s.length() >= 2 && s.startsWith("\"") && s.endsWith("\""))
          s = s.substring(1, s.length() - 1);
        if (fromSolver) s = smtUnescape(s); // "" -> quote, u{h..} escape -> char, so the witness has the solver's real string
        StringBuilder sb = new StringBuilder("\\result.equals(\"");
        for (char c : s.toCharArray())
          sb.append(c == '\'' ? "'" : c == '"' ? "\\\"" : escapeChar(c));
        return sb.append("\")").toString();
      }
      default:
        return null;
    }
  }

  /**
   * Rebuilds a nondet string from the numeric model when the string solver gave no value for it.
   * JR turns s.length() and s.charAt(i) into the integers Length_k_ and CharAt(i)_k_, so the
   * numeric model has the string's length and the characters the path depends on; every other
   * position is free and gets 'a'. Returns null if the path has no length symbol for this string.
   */
  static String stringFromNumericModel(PathCondition pc, String symName) {
    try {
      List<SymbolicInteger> vars = new ArrayList<>();       // every integer symbol of the PC
      List<SymbolicLengthInteger> lengths = new ArrayList<>();
      List<SymbolicCharAtInteger> chars = new ArrayList<>();
      ConstraintExpressionVisitor collect = new ConstraintExpressionVisitor() {
        @Override
        public void preVisit(SymbolicInteger e) {
          vars.add(e);
          if (e instanceof SymbolicLengthInteger && isString(((SymbolicLengthInteger) e).getExpression(), symName))
            lengths.add((SymbolicLengthInteger) e);
          if (e instanceof SymbolicCharAtInteger && isString(((SymbolicCharAtInteger) e).getExpression(), symName)) {
            chars.add((SymbolicCharAtInteger) e);
            ((SymbolicCharAtInteger) e).getIndex().accept(this);  // index symbols, e.g. Length_0_ - 1
          }
        }
      };
      for (Constraint c = pc.header; c != null; c = c.and)
        c.accept(collect);
      if (lengths.isEmpty())
        return null;

      // symbols left unsolved (e.g. only used in veritesting regions): take them from the full model
      List<String> unsolved = new ArrayList<>();
      for (SymbolicInteger v : vars)
        if (v.solution == SymbolicInteger.UNDEFINED)
          unsolved.add(v.getName());
      if (!unsolved.isEmpty()) {
        Map<String, Object> model = pc.solveWithValuations(unsolved);
        for (SymbolicInteger v : vars)
          if (v.solution == SymbolicInteger.UNDEFINED && model != null && model.get(v.getName()) != null)
            v.solution = Long.parseLong(model.get(v.getName()).toString());
      }

      long len = lengths.get(0).solution;
      if (len < 0 || len > 100000)
        return null;
      char[] text = new char[(int) len];
      Arrays.fill(text, 'a');
      for (SymbolicCharAtInteger ch : chars) {
        long i = ch.getIndex().solution();
        if (i >= 0 && i < len && ch.solution != SymbolicInteger.UNDEFINED)
          text[(int) i] = (char) ch.solution;
      }
      return new String(text);
    } catch (Throwable t) { // no usable model: caller falls back to ""
      return null;
    }
  }

  static boolean isString(StringExpression se, String symName) {
    return se instanceof StringSymbolic
        && ((StringSymbolic) se).fixName(((StringSymbolic) se).getName()).equals(symName);
  }

  static final Pattern SMT_CHAR = Pattern.compile("\\\\u\\{([0-9a-fA-F]{1,5})\\}|\\\\u([0-9a-fA-F]{4})");

  /**
   * Body of a Z3 string literal (outer quotes removed) as the Java string it stands for:
   * "" is one quote, a backslash-u{h..} or backslash-uhhhh escape is one character. Code points above U+FFFF are kept
   * as written, since they are one character for Z3 but two for Java.
   */
  static String smtUnescape(String s) {
    StringBuilder out = new StringBuilder();
    Matcher m = SMT_CHAR.matcher(s);
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c == '"' && i + 1 < s.length() && s.charAt(i + 1) == '"') {
        out.append('"');
        i++;
        continue;
      }
      if (c == '\\' && m.region(i, s.length()).lookingAt()) {
        int cp = Integer.parseInt(m.group(1) != null ? m.group(1) : m.group(2), 16);
        if (cp <= 0xFFFF) {
          out.append((char) cp);
          i = m.end() - 1;
          continue;
        }
      }
      out.append(c);
    }
    return out.toString();
  }

  /** Java escape of a char inside a char or string literal (ASCII only output). */
  static String escapeChar(char c) {
    switch (c) {
      case '\\': return "\\\\";
      case '\'': return "\\'";
      case '\n': return "\\n";
      case '\t': return "\\t";
      case '\r': return "\\r";
      default:
        return (c >= 0x20 && c < 0x7f) ? String.valueOf(c) : String.format("\\u%04x", (int) c);
    }
  }

  // ---------------------------------------------------------------- locations

  /** Current value of the backtracked static counter of JR's Verifier model. */
  static int verifierCounter() {
    try {
      ClassInfo ci = ClassLoaderInfo.getCurrentResolvedClassInfo("org.sosy_lab.sv_benchmarks.Verifier");
      return ci.getStaticElementInfo().getIntField("counter");
    } catch (Throwable t) {
      return Integer.MAX_VALUE;
    }
  }

  /** {file, line} of the first stack frame of the violation that lies in a task file. */
  static String[] targetLocation() {
    String details = VM.getVM().getSearch().getLastError().getDetails();
    Matcher m = Pattern.compile("at ([\\w$.]+)\\.[\\w$<>]+\\(([\\w$]+\\.java):(\\d+)\\)").matcher(details);
    String[] first = null;
    while (m.find()) {
      String cls = m.group(1);
      String pkg = cls.contains(".") ? cls.substring(0, cls.lastIndexOf('.')).replace('.', '/') + "/" : "";
      String rel = pkg + m.group(2);
      String[] loc = {inputFileFor(rel), m.group(3)};
      if (first == null) first = loc;
      if (!rel.startsWith("org/sosy_lab/sv_benchmarks/") && !loc[0].equals(rel))
        return loc;
    }
    return first != null ? first : new String[] {"Main.java", "0"};
  }

  /** The task input file for a package-relative source path (e.g. "svcomp/objects/Factories.java"). */
  static String inputFileFor(String relPath) {
    if (relPath == null)
      return "Main.java";
    for (String f : inputFiles())
      if (f.equals(relPath) || f.endsWith("/" + relPath))
        return f;
    return relPath;
  }

  /** 1-based column of the '(' of the only nondet call on the line, or -1 if not unique. */
  static int nondetColumn(String file, int line) {
    try {
      List<String> lines = Files.readAllLines(Paths.get(file), StandardCharsets.UTF_8);
      if (line < 1 || line > lines.size())
        return -1;
      Matcher m = Pattern.compile("nondet\\w*\\s*\\(").matcher(lines.get(line - 1));
      if (!m.find())
        return -1;
      int col = m.end();
      return m.find() ? -1 : col;
    } catch (Exception e) {
      return -1;
    }
  }

  // ---------------------------------------------------------------- metadata and output

  static List<String> inputFiles() {
    Config conf = VM.getVM().getConfig();
    String[] files = conf.getStringArray("witness.input_files", new String[0]);
    return new ArrayList<>(new TreeSet<>(Arrays.asList(files)));
  }

  static String header(String entryType) {
    Config conf = VM.getVM().getConfig();
    StringBuilder sb = new StringBuilder();
    sb.append("- entry_type: ").append(quote(entryType)).append("\n");
    sb.append("  metadata:\n");
    sb.append("    format_version: \"2.4\"\n");
    sb.append("    uuid: ").append(quote(UUID.randomUUID().toString())).append("\n");
    sb.append("    creation_time: ")
        .append(quote(Instant.now().truncatedTo(ChronoUnit.SECONDS).toString())).append("\n");
    sb.append("    producer:\n");
    sb.append("      name: \"Java Ranger\"\n");
    sb.append("      version: \"2027\"\n");
    sb.append("    task:\n");
    List<String> files = inputFiles();
    sb.append("      input_files:").append(files.isEmpty() ? " []" : "").append("\n");
    for (String f : files)
      sb.append("      - ").append(quote(f)).append("\n");
    sb.append("      input_file_hashes:").append(files.isEmpty() ? " {}" : "").append("\n");
    for (String f : files)
      sb.append("        ").append(quote(f)).append(": ").append(quote(sha256(f))).append("\n");
    sb.append("      specification: ").append(quote(specification(conf))).append("\n");
    sb.append("      language: \"Java\"\n");
    return sb.toString();
  }

  static String specification(Config conf) {
    String prp = conf.getString("witness.property_file");
    try {
      if (prp != null)
        return new String(Files.readAllBytes(Paths.get(prp)), StandardCharsets.UTF_8).trim();
    } catch (IOException ignored) {
    }
    return "CHECK( init(Main.main()), LTL(G assert) )";
  }

  static String sha256(String file) {
    try {
      byte[] digest = MessageDigest.getInstance("SHA-256").digest(Files.readAllBytes(Paths.get(file)));
      StringBuilder sb = new StringBuilder();
      for (byte b : digest)
        sb.append(String.format("%02x", b));
      return sb.toString();
    } catch (Exception e) {
      return "";
    }
  }

  /** YAML double-quoted scalar. */
  static String quote(String s) {
    return "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
  }

  static void write(String content) {
    try (FileWriter writer = new FileWriter(outputFilePath)) {
      writer.write(content);
    } catch (IOException e) {
      System.out.println("IOException detected: " + e.getMessage());
    }
  }
}
