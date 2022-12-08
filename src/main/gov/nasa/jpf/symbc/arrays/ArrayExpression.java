/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

package gov.nasa.jpf.symbc.arrays;

import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor2;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;

import java.util.Map;

public class ArrayExpression extends Expression {
    public IntegerExpression length;
    private String elemType = "?";
    private final String name;

    public String getName() {
        return this.name;
    }

    public ArrayExpression(String name) {
        this.name=name;
        this.length = new SymbolicInteger(name+"_length");
    }

    public ArrayExpression(String name, int l) {
        this.name = name;
        this.length = new IntegerConstant(l);
    }

    public ArrayExpression(String name, String arrayType) {
        this.name = name;
        this.length = new SymbolicInteger(name+"_length");
        this.elemType = arrayType;
    }

    public static String getNewName(ArrayExpression prev) {
        String newName = prev.getName();
        if (newName.indexOf("!") == -1) {
            newName = newName + "!1";
        } else {
            /* Increment the number after '!' */
            int aux = Integer.parseInt(newName.substring(newName.indexOf("!") + 1));
            newName = newName.substring(0, newName.indexOf("!") + 1) + (aux + 1);
        }
        return newName;
    }

    public String getRootName() {
        if (this.getName().indexOf("!") == -1) {
            return this.getName();
        } else {
            return this.getName().substring(0, this.getName().indexOf("!"));
        }

    }

    public ArrayExpression(ArrayExpression prev) {
        this.name = getNewName(prev);
        this.length = prev.length;
        this.elemType = prev.getElemType();
    }
        
    public String getElemType() {
        return elemType;
    }

    public static ArrayExpression create(String name) {
        return new ArrayExpression(name);
    }

    public static ArrayExpression create(String name, String arrayType) {
        return new ArrayExpression(name, arrayType);
    }

    public static ArrayExpression create(String name, int l) {
       return new ArrayExpression(name, l);
    }

   public String stringPC() {
        return (name != null) ? name : "ARRAY_" + hashCode();
    }

    public void accept(ConstraintExpressionVisitor visitor) {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    public void getVarsVals(Map<String,Object> varsVals) {
        return;
    }

    public int compareTo(Expression expr) {
        // unimplemented
        return 0;
    }

    public String toString() {
        return this.stringPC();
    }
}
