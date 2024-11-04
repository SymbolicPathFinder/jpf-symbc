/**
 * Object for parsing symbolic variable at PathCondition It has one method, parseSymVar()
 */
package gov.nasa.jpf.symbc.witness;


import gov.nasa.jpf.symbc.numeric.PathCondition;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PathConditionParser {

  /**
   * It parses a value of symbolic variable from PathCondition, and match it to corresponding
   * variable
   *
   * @param pc                       is the PathCondition
   * @param symbolicVariableInfoList is a list that contains the information of symbolic variables
   */
  public void parseSymVar(PathCondition pc, List<SymbolicVariableInfo> symbolicVariableInfoList) {
    String strPathCondition = pc.toString();

    // Extract variable name and value
    Pattern pattern = Pattern.compile("(\\w+)\\[(-?\\d+(\\.\\d+)?([eE][-+]?\\d+)?)\\]");
    Matcher matcher = pattern.matcher(strPathCondition);

    // Insert value to list
    while (matcher.find()) {
      String pcVariableName = matcher.group(1);
      String pcVariableValue = matcher.group(2);
      // There are 3 cases, real number, string and other numeric types

      // For real type
      if (pcVariableName.contains("double") || pcVariableName.contains("float")
          || pcVariableName.contains("REAL")) {
        double value = Double.parseDouble(pcVariableValue); // 실수로 파싱
        for (int i = 0; i < symbolicVariableInfoList.size(); i++) {
          if (symbolicVariableInfoList.get(i).varSymName.equals(pcVariableName)) {
            symbolicVariableInfoList.get(i).varValue = value;
            break;
          }
        }

      }
      // Other types
      else {
        int value = Integer.parseInt(pcVariableValue);
        for (int i = 0; i < symbolicVariableInfoList.size(); i++) {
          if (symbolicVariableInfoList.get(i).varSymName.equals(pcVariableName)) {
            // special case for boolean type
            if (symbolicVariableInfoList.get(i).returnType.equals("boolean")) {
              if (value == 1)
                symbolicVariableInfoList.get(i).varValue = true;
              else if (value == 0)
                symbolicVariableInfoList.get(i).varValue = false;
              break;
            } else
              symbolicVariableInfoList.get(i).varValue = value;
            break;
          }
        }

      }
    }

    /**
     * Attempting to use the string PathCondition to find the solutions for the symbolic variables.
     * This should be cleaner if we have a consistent way of have a path condition that is joint
     * between string and numeric, and also, if we have a uniform way of populating an intermediate
     * datastructure that hold the model of the sat query.
     */

    for (SymbolicVariableInfo symInfo : symbolicVariableInfoList) {
      String solution = pc.spc.solution.get(symInfo.varSymName);
      if (solution != null) {
        if (symInfo.returnType.contains("String")) {
          symInfo.varValue = solution;
        } else if (symInfo.returnType.contains("int")) {
          symInfo.varValue = solution;
        } else if (symInfo.returnType.equals("boolean")) {
          symInfo.varValue =
              Integer.parseInt(solution) == 0 ? "false" : "true";
        }
      }
    }
  }

}


