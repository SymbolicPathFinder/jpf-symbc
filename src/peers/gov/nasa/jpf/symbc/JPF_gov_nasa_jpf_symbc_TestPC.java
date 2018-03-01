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

package gov.nasa.jpf.symbc;

/*import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;*/

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Operator;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;
import gov.nasa.jpf.vm.ReferenceFieldInfo;
import gov.nasa.jpf.vm.StaticElementInfo;
import gov.nasa.jpf.vm.SystemState;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

public class JPF_gov_nasa_jpf_symbc_TestPC extends NativePeer {


	private static Comparator getComparator(String str){
		Comparator[] comp = Comparator.values();
		for(Comparator comparator : comp){
			if(comparator.toString().equals(str))
				return comparator;
		}
		return null;
	}


	private static Operator getOperator(String str){
		Operator[] opArr = Operator.values();
		for(Operator operator : opArr){
			if(operator.toString().equals(str))
				return operator;
		}
		return null;
	}

	@MJI
	public static int booleanPC_x_y(MJIEnv env, int objRef, int stringRef1, int compRef1, int stringRef2, int compRef2) {
		String var1 = env.getStringObject(stringRef1);
		String var2 = env.getStringObject(stringRef2);
		String comp1 = env.getStringObject(compRef1);
		String comp2 = env.getStringObject(compRef2);
		PathCondition pc = new PathCondition();
		SymbolicInteger sym1 = new SymbolicInteger(var1);
		SymbolicInteger sym2 = new SymbolicInteger(var2);
		pc._addDet(getComparator(" "+comp2.trim()+" "),sym2,0);
		pc._addDet(getComparator(" "+comp1.trim()+" "),sym1,0);

		return env.newString(pc.stringPC());
	}

	
	@MJI
	public static int doublePC1(MJIEnv env, int objRef, int stringRef1, int compRef1, double val) {
		String var1 = env.getStringObject(stringRef1);
		PathCondition pc = new PathCondition();
		SymbolicReal sym1 = new SymbolicReal(var1);
		String comp1 = env.getStringObject(compRef1);
		pc._addDet(getComparator(" "+comp1.trim()+" "),sym1,val);
		return env.newString(pc.stringPC());
	}


	@MJI
	public static int doublePC2(MJIEnv env, int objRef, double val, int compRef1, int stringRef1) {
		String var1 = env.getStringObject(stringRef1);
		PathCondition pc = new PathCondition();
		SymbolicReal sym1 = new SymbolicReal(var1);
		String comp1 = env.getStringObject(compRef1);
		pc._addDet(getComparator(" "+comp1.trim()+" "),val,sym1);
		return env.newString(pc.stringPC());
	}

	@MJI
	public static int doublePC3(MJIEnv env, int objRef, int stringRef1, int opRef ,int stringRef2,int compRef, double val) {
		String var1 = env.getStringObject(stringRef1);
		String var2 = env.getStringObject(stringRef2);
		PathCondition pc = new PathCondition();
		SymbolicReal sym1 = new SymbolicReal(var1);
		SymbolicReal sym2 = new SymbolicReal(var2);
		String op = env.getStringObject(opRef);
		BinaryRealExpression expr = new BinaryRealExpression(sym1,getOperator(" "+op.trim()+" "),sym2);
		String comp = env.getStringObject(compRef);
		pc._addDet(getComparator(" "+comp.trim()+" "), expr, val);
		return env.newString(pc.stringPC());
	}

	@MJI
	public static int doublePC4(MJIEnv env, int objRef,double val, int stringRef1, int opRef ,int stringRef2,int compRef) {
		String var1 = env.getStringObject(stringRef1);
		String var2 = env.getStringObject(stringRef2);
		PathCondition pc = new PathCondition();
		SymbolicReal sym1 = new SymbolicReal(var1);
		SymbolicReal sym2 = new SymbolicReal(var2);
		String op = env.getStringObject(opRef);
		BinaryRealExpression expr = new BinaryRealExpression(sym1,getOperator(" "+op.trim()+" "),sym2);
		String comp = env.getStringObject(compRef);
		pc._addDet(getComparator(" "+comp.trim()+" "), val,expr);
		return env.newString(pc.stringPC());
	}

	@MJI
	public static int intPC1(MJIEnv env, int objRef, int stringRef1, int compRef1, int val) {
		String var1 = env.getStringObject(stringRef1);
		PathCondition pc = new PathCondition();
		SymbolicInteger sym1 = new SymbolicInteger(var1);
		String comp1 = env.getStringObject(compRef1);
		pc._addDet(getComparator(" "+comp1.trim()+" "),sym1,val);
		return env.newString(pc.stringPC());
	}

	@MJI
	public static int intPC2(MJIEnv env, int objRef, int stringRef1, int opRef ,int stringRef2,int compRef, int val) {
		String var1 = env.getStringObject(stringRef1);
		String var2 = env.getStringObject(stringRef2);
		PathCondition pc = new PathCondition();
		SymbolicInteger sym1 = new SymbolicInteger(var1);
		SymbolicInteger sym2 = new SymbolicInteger(var2);
		String op = env.getStringObject(opRef);
		BinaryLinearIntegerExpression expr = new BinaryLinearIntegerExpression(sym1,getOperator(" "+op.trim()+" "),sym2);
		String comp = env.getStringObject(compRef);
		pc._addDet(getComparator(" "+comp.trim()+" "), expr, val);
		return env.newString(pc.stringPC());
	}


}