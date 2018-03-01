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

//TODO: problem: we do not distinguish between ints and reals?
// still needs a lot of work: do not use!


import java.util.HashMap;
import java.util.List;

import symlib.SymBool;
import symlib.Util;
import cvc3.Expr;
import cvc3.ExprMut;
import cvc3.FlagsMut;
import cvc3.QueryResult;
import cvc3.Rational;
import cvc3.SatResult;
import cvc3.TypeMut;
//import cvc3.SatResult;
import cvc3.Type;
import cvc3.ValidityChecker;
/* Rody: add typecasts long->int everywhere now. Needs a nice solution where the user
 * is notified to use another solver with longs.
 */
public class ProblemCVC3 extends ProblemGeneral {
	protected Expr pb;
	protected ValidityChecker vc = null;
    protected FlagsMut flags = null;
    protected final int base = 10; //used in creating real variables
    protected HashMap model;

	public ProblemCVC3() {
		pb = null;
		try{
			if(vc != null) vc.delete();
	        flags = ValidityChecker.createFlags(null);
	        flags.setFlag("dagify-exprs",false);
	        vc = ValidityChecker.create(flags);
	       // System.out.println("validity checker is initialized");
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
	    }
	}

	//To Do: need to call this at some point;
	public void cleanup(){
		try{
	        if (vc != null) vc.delete();
	        if (flags != null) flags.delete();
		}catch(Exception e){
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	//if min or max are passed in as null objects to the vc
	//it will use minus and plus infinity
	public Object makeIntVar(String name, long min, long max) {
		assert(min>=Integer.MIN_VALUE && max<=Integer.MAX_VALUE);
		try{
			Type sType = vc.subrangeType(vc.ratExpr((int) min),
                    vc.ratExpr((int) max));
			return vc.varExpr(name, sType);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}



	public Object makeRealVar(String name, double min, double max) {

		//WARNING: need to downcast double to int - I don't see
		// a way in CVC3 to create a sub-range for real types
		//other choice is not to bound and use vc.realType() to
		//create the expression
		int minInt = (int)min;
		int maxInt = (int)max;
		try{
			//Expr x = vc.varExpr(name, vc.realType());
			Type sType = vc.subrangeType(vc.ratExpr(minInt),
                    vc.ratExpr(maxInt));
			return vc.varExpr(name, sType);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object eq(long value, Object exp){
		try{
			return  vc.eqExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object eq(Object exp, long value){
		try{
			return  vc.eqExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object eq(Object exp1, Object exp2){
		try{
			return  vc.eqExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object eq(double value, Object exp){
		try{
			return  vc.eqExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object eq(Object exp, double value){
		try{
			return  vc.eqExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object neq(long value, Object exp){
		try{
			return  vc.notExpr(vc. eqExpr(vc.ratExpr((int) value), (Expr)exp));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object neq(Object exp, long value){
		try{
			return  vc.notExpr(vc.eqExpr((Expr)exp, vc.ratExpr((int) value)));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object neq(Object exp1, Object exp2){
		try{
			return  vc.notExpr(vc.eqExpr((Expr)exp1, (Expr)exp2));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object not(Object exp1){
		try{
			return  vc.notExpr((Expr)exp1);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object neq(double value, Object exp){
		try{
			return  vc.notExpr(vc.eqExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object neq(Object exp, double value){
		try{
			return  vc.notExpr(vc.eqExpr((Expr)exp, vc.ratExpr(Double.toString(value), base)));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object leq(long value, Object exp){
		try{
			return  vc.leExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object leq(Object exp, long value){
		try{
			return  vc.leExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object leq(Object exp1, Object exp2){
		try{
			return  vc.leExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object leq(double value, Object exp){
		try{
			return  vc.leExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object leq(Object exp, double value){
		try{
			return  vc.leExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object geq(long value, Object exp){
		try{
			return  vc.geExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object geq(Object exp, long value){
		try{
			return  vc.geExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object geq(Object exp1, Object exp2){
		try{
			return  vc.geExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object geq(double value, Object exp){
		try{
			return  vc.geExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object geq(Object exp, double value){
		try{
			return  vc.geExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object lt(long value, Object exp){
		try{
			return  vc.ltExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object lt(Object exp, long value){
		try{
			return  vc.ltExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object lt(Object exp1, Object exp2){
		try{
			return  vc.ltExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object lt(double value, Object exp){
		try{
			return  vc.ltExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object lt(Object exp, double value){
		try{
			return  vc.ltExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}


	public Object gt(long value, Object exp){
		try{
			return  vc.gtExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object gt(Object exp, long value){
		try{
			return  vc.gtExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object gt(Object exp1, Object exp2){
		try{
			return  vc.gtExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object implies(Object exp1, Object exp2){
		try{
			return  vc.impliesExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object gt(double value, Object exp){
		try{
			return  vc.gtExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}

	public Object gt(Object exp, double value){
		try{
			return  vc.gtExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);

	    }
	}




	public Object plus(long value, Object exp) {
		try{
			return  vc.plusExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object plus(Object exp, long value) {
		try{
			return  vc.plusExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object plus(Object exp1, Object exp2) {
		try{
			return  vc.plusExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object plus(double value, Object exp) {
		try{
			return  vc.plusExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object plus(Object exp, double value) {
		try{
			return  vc.plusExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object minus(long value, Object exp) {
		try{
			return  vc.minusExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object minus(Object exp, long value) {
		try{
			return  vc.minusExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object minus(Object exp1, Object exp2) {
		try{
			return  vc.minusExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object minus(double value, Object exp) {
		try{
			return  vc.minusExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object minus(Object exp, double value) {
		try{
			return  vc.minusExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object mult(long value, Object exp) {
		try{
			return  vc.multExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object mult(Object exp, long value) {
		try{
			return  vc.multExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object mult(Object exp1, Object exp2) {
		try{
			return  vc.multExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}
	public Object mult(double value, Object exp) {
		try{
			return  vc.multExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}
	public Object mult(Object exp, double value) {
		try{
			return  vc.multExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	//TODO

	public Object div(long value, Object exp) {
		try{
			return  vc.divideExpr(vc.ratExpr((int) value), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object div(Object exp, long value) {
		try{
			return  vc.divideExpr((Expr)exp, vc.ratExpr((int) value));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public Object div(Object exp1, Object exp2) {
		try{
			return  vc.divideExpr((Expr)exp1, (Expr)exp2);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}
	public Object div(double value, Object exp) {
		try{
			return  vc.divideExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}
	public Object div(Object exp, double value) {
		try{
			return  vc.divideExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}



	// not yet done for CVC3
//	public Object sin(Object exp) {
//		throw new RuntimeException("## Error: Math.sin not supported");
//	}
//	public Object cos(Object exp) {
//		throw new RuntimeException("## Error: Math.cos not supported");
//	}
//
//	public Object round(Object exp) {
//		throw new RuntimeException("## Error: Math.round not supported");
//	}
//	public Object exp(Object exp) {
//		throw new RuntimeException("## Error: Math.exp not supported");
//	}
//	public Object asin(Object exp) {
//		throw new RuntimeException("## Error: Math.asin not supported");
//
//	}
//	public Object acos(Object exp) {
//		throw new RuntimeException("## Error: Math.acos not supported");
//
//	}
//	public Object atan(Object exp) {
//		throw new RuntimeException("## Error: Math.atan not supported");
//
//	}
//	public Object log(Object exp) {
//		throw new RuntimeException("## Error: Math.log not supported");
//
//	}
//	public Object tan(Object exp) {
//		throw new RuntimeException("## Error: Math.tan not supported");
//
//	}
//	public Object sqrt(Object exp) {
//		throw new RuntimeException("## Error: Math.sqrt not supported");
//
//	}
//	public Object power(Object exp1, Object exp2) {
//		throw new RuntimeException("## Error: Math.power not supported");
//	}
//	public Object power(Object exp1, double exp2) {
//		throw new RuntimeException("## Error: Math.power not supported");
//	}
//	public Object power(double exp1, Object exp2) {
//		throw new RuntimeException("## Error: Math.power not supported");
//	}
//
//	public Object atan2(Object exp1, Object exp2) {
//		throw new RuntimeException("## Error: Math.atan2 not supported");
//	}
//	public Object atan2(Object exp1, double exp2) {
//		throw new RuntimeException("## Error: Math.atan2 not supported");
//	}
//	public Object atan2(double exp1, Object exp2) {
//		throw new RuntimeException("## Error: Math.atan2 not supported");
//	}

	public Object mixed(Object exp1, Object exp2) {  //not done yet for cvc3
		throw new RuntimeException("## Error CVC3: mixed integer/real constraint not yet implemented");
	}

	//there must be a better way to do this
	//returns the upper bound on the range
	public double getRealValueInf(Object dpVar) {
		try{
			Expr exp = (Expr)dpVar;
			Type t = exp.getType();
			String bounds = t.toString();
			String s = bounds.substring(bounds.lastIndexOf('.')+1,bounds.length()-1);
			return Double.parseDouble(s);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public double getRealValue(Object dpVar) { //not done yet for cvc3
		try{
			Expr exp = (Expr)model.get((Expr)dpVar);
			Rational val = exp.getRational();
			int num = val.getNumerator().getInteger();
			int den = val.getDenominator().getInteger();
			return num/den;
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	public long getIntValue(Object dpVar) { //not done yet for cvc3
		try{
		Expr exp = (Expr)model.get((Expr)dpVar);
		Rational val = exp.getRational();
		return val.getInteger();
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	//there must be a better way to do this
	//returns the upper bound on the range
	public double getRealValueSup(Object dpVar) {
		try{
			Expr exp = (Expr)dpVar;
			Type t = exp.getType();
			String bounds = t.toString();
			String s = bounds.substring(1,bounds.indexOf('.'));
			return Double.parseDouble(s);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	private Expr test(){
		Expr e = (Expr)makeIntVar("Z",-10, 10);
		Expr f = (Expr)makeIntVar("f", -10,10);
		Expr plus = (Expr)plus(10,e);
		Expr plus2 = (Expr)plus(1,e);
		Expr eq = (Expr)eq(plus, plus2);
		return eq;
	}

	public Boolean solve() {
        try {
			if (pb==null)
				return true;
			//Expr ex = test();
			//System.out.println("Query: " + pb.toString());
			vc.push();
			SatResult result = vc.checkUnsat(pb);
			//QueryResult result = vc.query(eq); //does not seem to work properly
			if (result == SatResult.UNSATISFIABLE) {
	            //System.out.println("Unsatisfiable (Valid)\n");
				vc.pop();
	            return false;
	        }
	        else if (result == SatResult.SATISFIABLE) {
	        	model = vc.getConcreteModel();
	        	vc.pop();
	           // System.out.println("Satisfiable (Invalid)\n");
	            return true;
	        }else{
	        	vc.pop();
	        	return false;
	        }
        }catch(Exception e){
        	e.printStackTrace();
        	throw new RuntimeException("## Error CVC3: Exception caught initializing CVC3 validity checker: \n" + e);
        }
	}

	public void post(Object constraint) {
		try{
			if (pb != null)
				pb = vc.andExpr(pb, (Expr)constraint);
			else
				pb = (Expr)constraint;
		} catch (Exception e) {
			e.printStackTrace();
        	throw new RuntimeException("## Error CVC3: Exception caught making Int Var in CVC3 ???: \n" + e);
	    }
	}

	public void postOr(Object constraint) {
		try{
			if (pb != null)
				pb = vc.orExpr(pb, (Expr)constraint);
			else
				pb = (Expr)constraint;
		} catch (Exception e) {
			e.printStackTrace();
        	throw new RuntimeException("## Error CVC3: Exception caught making Int Var in CVC3 ???: \n" + e);
	    }
	}

	public Object and(long value, Object exp) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object and(Object exp, long value) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object and(Object exp1, Object exp2) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object or(long value, Object exp) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object or(Object exp, long value) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object or(Object exp1, Object exp2) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftL(long value, Object exp) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftL(Object exp, long value) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftR(long value, Object exp) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftR(Object exp, long value) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object xor(long value, Object exp) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object xor(Object exp, long value) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object xor(Object exp1, Object exp2) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftL(Object exp1, Object exp2) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftR(Object exp1, Object exp2) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftUR(long value, Object exp) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftUR(Object exp, long value) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	public Object shiftUR(Object exp1, Object exp2) {
		throw new RuntimeException("## Switch to CVC3BitVec");
	}

	@Override
	public void postLogicalOR(Object[] constraints) {
		assert(constraints != null && constraints.length >=1);
		Expr orResult = (Expr) ( constraints[0]);
		for (int i =1; i<constraints.length; i++) {
			//System.out.println("****** orResult"+ orResult + "************ " +i);
			orResult = vc.orExpr(orResult, (Expr)constraints[i]);
		}

		post(orResult);

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