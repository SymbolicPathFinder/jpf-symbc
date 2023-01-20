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

//
//Copyright (C) 2006 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc.numeric.solvers;

//import choco.Problem;
import gov.nasa.jpf.symbc.numeric.RealProblem;
import choco.integer.*;
import choco.integer.var.IntTerm;
import choco.integer.var.IntTerm.*;
import choco.real.*;
import choco.real.constraint.MixedEqXY;

/* Rody: add typecasts long->int everywhere now. Needs a nice solution where the user
 * is notified to use another solver with longs.
 */
public class ProblemChoco extends ProblemGeneral {
	RealProblem pb;
	public static int timeBound;// = 30000;
	public ProblemChoco() {
		pb = new RealProblem();
		//pb.setPrecision(1e-8);// need to check this
	}

	public IntDomainVar makeIntVar(String name, long min, long max) {
		assert(min>=Integer.MIN_VALUE && max<=Integer.MAX_VALUE);
		return pb.makeBoundIntVar(name, (int) min, (int) max);
	}

	public RealVar makeRealVar(String name, double min, double max) {
		return pb.makeRealVar(name,min,max);
	}

	//Added by Gideon
//	public Object logicOr (choco.Constraint[] arr) {
//		/*System.out.println("orring...");
//		for (choco.Constraint c: arr) {
//			System.out.println(c.pretty());
//		}*/
//		return pb.or(arr);
//	}

	public Object eq(long value, Object exp){return pb.eq((int) value, (IntExp)exp);}
	public Object eq(Object exp, long value){return pb.eq((IntExp) exp, (int) value);}
	public Object eq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.eq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.eq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object eq(double value, Object exp){return pb.eq(value, (RealExp) exp);}
	public Object eq(Object exp, double value){return pb.eq(value, (RealExp) exp);}
	public Object neq(long value, Object exp){return pb.neq((int) value, (IntExp) exp);}
	public Object neq(Object exp, long value){return pb.neq((int) value, (IntExp) exp);}
	public Object neq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.neq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.neq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object neq(double value, Object exp){return pb.neq(value, (RealExp) exp);}
	public Object neq(Object exp, double value){return pb.neq(value, (RealExp) exp);}
	public Object leq(long value, Object exp){return pb.leq((int) value,(IntExp)exp);}
	public Object leq(Object exp, long value){return pb.leq((IntExp)exp,(int) value);}
	public Object leq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.leq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.leq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object leq(double value, Object exp){return pb.leq(value,(RealExp)exp);}
	public Object leq(Object exp, double value){return pb.leq((RealExp)exp, value);}
	public Object geq(long value, Object exp){return pb.geq((int) value, (IntExp)exp);}
	public Object geq(Object exp, long value){return pb.geq((IntExp)exp,(int) value);}
	public Object geq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.geq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.geq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object geq(double value, Object exp){
		return pb.geq(value, (RealExp) exp);
	}
	public Object geq(Object exp, double value){
		return pb.geq((RealExp) exp, value);
	}
	public Object lt(long value, Object exp){
		return pb.lt((int) value, (IntExp) exp);
	}
	public Object lt(Object exp, long value){
		return pb.lt((IntExp) exp,(int) value);
	}
	public Object lt(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.lt((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.lt((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object lt(double value, Object exp){
		return pb.lt(value,(RealExp) exp);
	}
	public Object lt(Object exp, double value){
		return pb.lt((RealExp) exp,value);
	}
	public Object gt(long value, Object exp){
		return pb.gt((int) value,(IntExp) exp);
	}
	public Object gt(Object exp, long value){
		return pb.gt((IntExp) exp,(int) value);
	}
	public Object gt(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.gt((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.gt((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object gt(double value, Object exp){
		return pb.gt(value,(RealExp) exp);
	}
	public Object gt(Object exp, double value){
		return pb.gt((RealExp) exp, value);
	}

	public Object plus(long value, Object exp) {
		return pb.plus((int) value,(IntExp) exp);
	}
	public Object plus(Object exp, long value) {
		return pb.plus((IntExp) exp, (int) value);
	}
	public Object plus(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.plus((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.plus((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object plus(double value, Object exp) {
		return pb.plus(pb.cst(value),(RealExp) exp);
	}
	public Object plus(Object exp, double value) {
		return pb.plus((RealExp) exp, pb.cst(value));
	}

	public Object minus(long value, Object exp) {
		return pb.minus((int) value, (IntExp) exp);
	}
	public Object minus(Object exp, long value) {
		return pb.minus((IntExp) exp, (int) value);
	}
	public Object minus(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.minus((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.minus((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object minus(double value, Object exp) {
		return pb.minus(pb.cst(value), (RealExp) exp);
	}
	public Object minus(Object exp, double value) {
		return pb.minus((RealExp) exp, pb.cst(value));
	}
	public Object mult(long value, Object exp) {
		if (exp instanceof IntVar)
			return pb.mult((int) value, (IntExp) exp);
		else if (exp instanceof IntTerm) {
			// distribute value over exp
			//return pb.mult(value, (IntExp) exp);
			IntTerm it= (IntTerm) exp;
        	IntTerm constant= new IntTerm(0);
        	constant.setConstant((int) value * it.getConstant());
        	IntExp sum = constant;
        	for (int i = 0; i < it.getSize(); i++) {
        		IntTerm newterm= new IntTerm(1);
        		newterm.setCoefficient(i, it.getCoefficient(i)*(int) value);
        		newterm.setVariable(i, it.getVariable(i));
        		sum= (IntExp) pb.plus(sum, newterm);
        	}
        	return sum;
		}
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object mult(Object exp, long value) {
		if (exp instanceof IntVar)
			return pb.mult((int) value, (IntExp) exp);

		else if (exp instanceof IntTerm) {
			// distribute value over exp
			//return pb.mult(value, (IntExp) exp);
			IntTerm it= (IntTerm) exp;
    		IntTerm constant= new IntTerm(0);
    		constant.setConstant((int) value * it.getConstant());
    		IntExp sum = constant;
    		for (int i = 0; i < it.getSize(); i++) {
    			IntTerm newterm= new IntTerm(1);
    			newterm.setCoefficient(i, it.getCoefficient(i)*(int) value);
    			newterm.setVariable(i, it.getVariable(i));
    			sum= (IntExp) pb.plus(sum, newterm);
    		}
    		return sum;
		}
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object mult(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			throw new RuntimeException("## Error Choco: non-lin int constraint");
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.mult((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object mult(double value, Object exp) {
		return pb.mult(pb.cst(value), (RealExp) exp);
	}
	public Object mult(Object exp, double value) {
		return pb.mult((RealExp) exp, pb.cst(value));
	}
	public Object div(long value, Object exp) {
		throw new RuntimeException("## Error Choco: non-lin int constraint");
	}
	public Object div(Object exp, long value) {
		throw new RuntimeException("## Error Choco: non-lin int constraint");
	}
	public Object div(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			throw new RuntimeException("## Error Choco: non-lin int constraint");
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.div((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	public Object div(double value, Object exp) {
		return pb.div(pb.cst(value), (RealExp) exp);
	}
	public Object div(Object exp, double value) {
		return pb.div((RealExp) exp,value);
	}
	public Object sin(Object exp) {
		return pb.sin((RealExp) exp);
	}
	public Object cos(Object exp) {
		return pb.cos((RealExp) exp);
	}

	public Object power(Object exp, double value) {
		return pb.power((RealExp) exp, (int)value);
	}
	public Object mixed(Object exp1, Object exp2) { // TODO:check !!!

		if (exp1 instanceof RealVar && exp2 instanceof IntVar)
			return new MixedEqXY((RealVar)exp1,(IntDomainVar)exp2);
		else
			throw new RuntimeException("## Error Choco: mixed");
	}

	public double getRealValueInf(Object dpVar) {
		return ((RealVar) dpVar).getValue().getInf();
	}
	public double getRealValueSup(Object dpVar) {
		return ((RealVar) dpVar).getValue().getSup();
	}
	public double getRealValue(Object dpVar) {
		throw new RuntimeException("# Error: Choco can not compute real solution!");
	}
	public long getIntValue(Object dpVar) {
		return ((IntDomainVar) dpVar).getVal();
	}

	public Object constant(double d) {
		return pb.cst(d);
	}

	public Boolean solve() {
        pb.getSolver().setTimeLimit(ProblemChoco.timeBound);

        Boolean result = pb.solve();
//        if (result == null)
 //       	System.out.println("Choco PC"+pb.pretty());

		return result;
	}
	public void post(Object constraint) {
		pb.post((choco.Constraint)constraint);
	}

	public Object and(long value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise AND");
	}

	public Object and(Object exp, long value) {
		throw new RuntimeException("## Error Choco does not support bitwise AND");
	}

	public Object and(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise AND");
	}

	@Override
	public Object or(long value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise OR");
	}

	@Override
	public Object or(Object exp, long value) {
		throw new RuntimeException("## Error Choco does not support bitwise OR");
	}


	public Object or(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise OR");
	}


	public Object shiftL(long value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object shiftL(Object exp, long value) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object shiftR(long value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object shiftR(Object exp, long value) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object xor(long value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise XOR");
	}

	public Object xor(Object exp, long value) {
		throw new RuntimeException("## Error Choco does not support bitwise XOR");
	}

	public Object xor(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise XOR");
	}

	public Object shiftL(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object shiftR(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object shiftUR(long value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");

	}

	public Object shiftUR(Object exp, long value) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	public Object shiftUR(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	@Override
	public void postLogicalOR(Object[] constraints) {

		choco.Constraint [] choco_constraints = new choco.Constraint[constraints.length];
		for (int i =0; i<constraints.length; i++)
			choco_constraints[i] = (choco.Constraint) constraints[i];
		Object orCon = ((RealProblem) pb).or(choco_constraints);
		choco.Constraint temp = (choco.Constraint) orCon;
		pb.post(temp);

	}

	@Override
	public Object rem(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object rem(long exp1, Object exp2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object rem(Object exp1, long exp2) {
		// TODO Auto-generated method stub
		return null;
	}

}
