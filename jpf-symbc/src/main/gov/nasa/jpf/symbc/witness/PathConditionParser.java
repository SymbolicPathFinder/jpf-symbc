package gov.nasa.jpf.symbc.witness;


import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PathConditionParser{

    public void parseSymVar(String strPathCondition, List<SymbolicVariableInfo> symbolicVariableInfoList){
        // Currently not handling String type
        // Extract variable name and value
        Pattern pattern = Pattern.compile("(\\w+)\\[(-?\\d+(\\.\\d+)?([eE][-+]?\\d+)?)\\]");
        Matcher matcher = pattern.matcher(strPathCondition);


        // Insert value to list
        while (matcher.find()) {
            String pcVariableName = matcher.group(1);
            String pcVariableValue = matcher.group(2);
            // There are 3 cases, real number, string and other numeric types
            if (pcVariableName.contains("double") || pcVariableName.contains("float") || pcVariableName.contains("REAL")) {
                double value = Double.parseDouble(pcVariableValue); // 실수로 파싱
                for(int i=0; i<symbolicVariableInfoList.size(); i++){
                    if(symbolicVariableInfoList.get(i).varName.equals(pcVariableName)){
                        symbolicVariableInfoList.get(i).varValue = value;
                        break;
                    }
                }

            }

            else if (pcVariableName.contains("string")) {
                for (int i = 0; i < symbolicVariableInfoList.size(); i++) {
                    if (symbolicVariableInfoList.get(i).varName.equals(pcVariableName)) {
                        symbolicVariableInfoList.get(i).varValue = pcVariableValue;
                        break;
                    }
                }

            }

            else {
                int value = Integer.parseInt(pcVariableValue);
                for(int i=0; i<symbolicVariableInfoList.size(); i++){
                    if(symbolicVariableInfoList.get(i).varName.equals(pcVariableName)){
                        // SPF outputs true or false as 1 or 0, respectively. Handle such cases
                        if(symbolicVariableInfoList.get(i).returnType.equals("boolean")){
                            if(value == 1) symbolicVariableInfoList.get(i).varValue = true;
                            else if(value == 0) symbolicVariableInfoList.get(i).varValue = false;
                            break;
                        }
                        else symbolicVariableInfoList.get(i).varValue = value;
                        break;
                    }
                }

            }
        }

    }

}


