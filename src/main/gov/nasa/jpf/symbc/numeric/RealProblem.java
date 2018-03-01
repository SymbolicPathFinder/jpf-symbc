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

package gov.nasa.jpf.symbc.numeric;

import choco.Constraint;
import choco.Problem;
import choco.integer.*;
import choco.real.*;
import choco.real.constraint.MixedEqXY;

// here we put all the operations that are not really handled by choco

public class RealProblem extends Problem {

	// not clear if neq works
	 public Constraint neq(double c, RealExp x) {

		 //throw new RuntimeException("## Error: neq(double,RealExp) not implemented ");
	     return createBinDisjunction(lt(c, x),gt(c,x));
	 }
	 public Constraint neq(RealExp x, double c) {
		 //throw new RuntimeException("## Error: neq(RealExp,double) not implemented ");
		 return createBinDisjunction(lt(c, x),gt(c,x));
	        //return or(lt(x, c),gt(x,c));
	 }
	 public Constraint neq(RealExp x, RealExp y) {
		 //throw new RuntimeException("## Error: neq(RealExp,RealExp) not implemented ");
		 return createBinDisjunction(lt(y, x),gt(x,x));
	        //return or(lt(x, y),gt(x,y));
	 }

	 public Constraint lt(double c, RealExp x) {
	        return leq(c+getPrecision(), x);
	 }
	 public Constraint lt(RealExp x, double c) {
	        return leq(x, c-getPrecision());
	 }
	 public Constraint lt(RealExp x, RealExp y) {
	        return leq(plus(x,cst(getPrecision())), y);
	 }
	 public Constraint gt(double c, RealExp x) {
	        return geq(c-getPrecision(), x);
	 }
	 public Constraint gt(RealExp x, double c) {
	        return geq(x, c+getPrecision());
	 }
	 public Constraint gt(RealExp x, RealExp y) {
	        return geq(x, plus(y,cst(getPrecision())));
	 }

	 public RealExp div(RealExp x, RealExp y) {
		 // check for y neq 0 done in DDIV and FDIV?
		 RealVar res = makeRealVar(MinMax.getVarMinDouble(""),MinMax.getVarMaxDouble("")); // res = x/y
		 post(eq(mult(res,y), x));
	     return res;
	 }

	 public RealExp div(RealExp x, double y) {
		 if(y==0)
			 throw new RuntimeException("## Error: DivideBy 0 ");
		 else
	        return mult(x, cst(1/y));
	 }
}
