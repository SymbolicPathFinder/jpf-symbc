package gov.nasa.jpf.symbc.witness;

import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.symbc.SymbolicListener;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.ApplicationContext;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

/**
 * This class maintains the witness collection state that is invoked by the listener during
 * execution.
 */
public class WitnessSymbolicState {

  // Path to the witness template
  // Assume working directory is SPF

  static String resourcePath = "witness_template/witness_template_minimal.txt";

  // Path to output directory, now it is current directory
  static String outputFilePath = "witness.graphml";

  // Temporary object to save the information of symbolic variable
  static SymbolicVariableInfo symbolicVariableInfo = new SymbolicVariableInfo();

//  // A list to save line number and return type
//  static public List<SymbolicVariableInfo> symVarInfoList = new ArrayList<>();


  // A list to save line number and return type
  public static List<SymbolicVariableInfo> symVarInfoList = new ArrayList<>();

  static boolean allowMethodInvocation = true;
  // A flag to check whether the information of symbolic variable is already parsed or not.
  static boolean interceptSymbolic = false;
  static boolean witnessAssumptionScopeIsFilled = false;
  static String fileName = "";
  static String assumptionScope = "";


  public static void collectSymNativeReturn(Instruction instruction, ThreadInfo ti) {
    String strIns = instruction.toString();
    StackFrame sf = ti.getTopFrame();
    Object symbolicVar = sf.getOperandAttr();
    if (interceptSymbolic && strIns.contains("nativereturn") && strIns.contains("makeSymbolic")) {
      symbolicVariableInfo.varSymName = symbolicVar.toString();
      symVarInfoList.add(symbolicVariableInfo);
      interceptSymbolic = false;
    }
  }

  // catch the invokestatic.Verifier.nondet~~
  // and store the line number and type
  public static void collectVerifierCalls(String className, String methodName,
      JVMInvokeInstruction md) {
    if (className.contains("Verifier") && methodName.contains("nondet")) {
      extractSymbolicVariableInfo(md);
    }
  }

  /**
   * Method that extracts line number and type of symbolic variables
   *
   * @param md JVMInvokeInstruction object
   */
  public static void extractSymbolicVariableInfo(JVMInvokeInstruction md) {
    symbolicVariableInfo.lineNumber = md.getLineNumber();
    symbolicVariableInfo.returnType = md.getReturnTypeName();
  }

  //maintain the state of whether we are still trying to intercept creation of symbolic variables
  // catch the invokestatic.Verifier.nondet~~
  // and store the line number and type
  public static void maintainWitnessInterceptionState(Instruction instruction) {
    String strInst = instruction.toString();
    if (strInst.contains("invokestatic") && strInst.contains("Verifier.nondet")) {
      JVMInvokeInstruction md = (JVMInvokeInstruction) instruction;
      extractSymbolicVariableInfo(md);
      interceptSymbolic = true;
    }
  }

  public static void collectPgmNameForSymVar(Instruction instruction) {
    String strInst = instruction.toString();
    if (strInst.contains("invokestatic") && strInst.contains("Verifier.nondet")) {
      int currPgmCounter = instruction.getInstructionIndex();
      Instruction nextInstruction = instruction.getMethodInfo().getInstructions()[currPgmCounter
          + 1];
      int symVarStackSlot = Integer.parseInt(
          nextInstruction.toString().substring(nextInstruction.toString().indexOf('_') + 1));
      LocalVarInfo[] methodLocalVars = instruction.getMethodInfo().getLocalVars();
      for(int i=0; i<methodLocalVars.length; i++){
        if(methodLocalVars[i].getSlotIndex()==symVarStackSlot){
          symbolicVariableInfo.varPgmName=methodLocalVars[i].getName();
          return;
        }
      }
    }
  }

  /**
   * It parses classname and filename to fill the value of assumption.scope at violation witness
   * Both classname and filename are needed to construct the edge of the witness assumptionScope is
   * a value of assumption.scope attribute of violation witness fileName is a value of originfile
   * attribute of violation witness
   */
  public static void parseAssumptionScope(ThreadInfo ti) {
    ApplicationContext app = ti.getApplicationContext();
    String className = app.getMainClassName();
    String[] parts = className.split("\\.");
    fileName = parts[parts.length - 1];
    assumptionScope = String.join(".", parts);
  }


  public static void oneTimeFillAssumptionScope(ThreadInfo ti) {
    if (!witnessAssumptionScopeIsFilled) {
      parseAssumptionScope(ti);
      witnessAssumptionScopeIsFilled = true;
    }
  }

  public static void createEmptyWitness() {
    Node nodeForEmptyWitness = new Node(1, 0, true);
    String strNode = nodeForEmptyWitness.serializeNode();
    try (InputStream inputStream = SymbolicListener.class.getClassLoader()
        .getResourceAsStream(resourcePath)) {
      if (inputStream == null) {
        throw new IllegalArgumentException("Resource not found : " + resourcePath);
      }
      GraphML emptyWitness = new GraphML(inputStream, outputFilePath);
      String headerForEmptyWitness = emptyWitness.constructHeader();
      emptyWitness.serializeEmptyWitness(strNode, headerForEmptyWitness);
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  //  populates the GraphML with the witness information
  public static void populateWitnessGraph(PathCondition pc) {

    List<Node> nodeList = new ArrayList<>();
    List<Edge> edgeList = new ArrayList<>();
    PathConditionParser parser = new PathConditionParser();
    parser.parseSymVar(pc, symVarInfoList);
    for (int i = 0; i < symVarInfoList.size(); i++) {
      Node node = new Node(symVarInfoList.size(), i, false);
      nodeList.add(node);
      Edge edge = new Edge(i, fileName, symVarInfoList, allowMethodInvocation,
                           assumptionScope);
      edgeList.add(edge);
    }
    // Add last node that contains violation key
    nodeList.add(new Node(symVarInfoList.size(), symVarInfoList.size(), false));
    try (InputStream inputStream = SymbolicListener.class.getClassLoader()
        .getResourceAsStream(resourcePath)) {
      if (inputStream == null) {
        throw new IllegalArgumentException("Resource not found : " + resourcePath);
      }
      GraphML graphML = new GraphML(inputStream, outputFilePath);
      String header = graphML.constructHeader();
      graphML.serializeWitness(edgeList, nodeList, header);
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  public static boolean witnessHasStringVar() {
    for (SymbolicVariableInfo symInfo : symVarInfoList) {
      if (symInfo.returnType.contains("String"))
        return true;
    }
    return false;
  }

}
