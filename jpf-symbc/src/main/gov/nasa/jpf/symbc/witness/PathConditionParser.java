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
   * It parses a value of symbolic variable from PathCondition, and match it to corresponding variable
   * @param pc is the PathCondition
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
      // For String type we do not to do the parsing the solution already exists in the spc
//            else if (pcVariableName.contains("string")) {
//                for (int i = 0; i < symbolicVariableInfoList.size(); i++) {
//                    if (symbolicVariableInfoList.get(i).varName.equals(pcVariableName)) {
//                        symbolicVariableInfoList.get(i).varValue = pc.spc.solution.get(pcVariableName);
//                        break;
//                    }
//                }
//
//            }
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

    for(SymbolicVariableInfo symInfo: symbolicVariableInfoList){
      if (symInfo.returnType.contains("String")) {
        symInfo.varValue = pc.spc.solution.get(symInfo.varSymName);
        break;
      }

    }
  }

}


