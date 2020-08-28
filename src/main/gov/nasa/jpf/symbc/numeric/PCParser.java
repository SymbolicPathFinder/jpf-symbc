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
//Copyright (C) 2005 United States Government as represented by the
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

import gov.nasa.jpf.symbc.arrays.ArrayConstraint;
import gov.nasa.jpf.symbc.arrays.RealArrayConstraint;
import gov.nasa.jpf.symbc.numeric.solvers.IncrementalSolver;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemCoral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVector;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Optimize;
import gov.nasa.jpf.symbc.numeric.visitors.ArrayConstraintVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.LinearIntegerConstraintVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.LogicalORLinearIntegerConstraintVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.MixedConstraintVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.NonLinearIntegerConstraintVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.ProblemGeneralVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.RealArrayConstraintVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.RealConstraintVisitor;

import java.util.HashMap;
import java.util.Map;


// parses PCs
public class PCParser {
  static ProblemGeneral pb;
  static ProblemGeneralVisitor pgv;
  static public Map<SymbolicReal, Object>	symRealVar = new HashMap<SymbolicReal,Object>(); // a map between symbolic real variables and DP variables
  static public Map<SymbolicInteger,Object>	symIntegerVar = new HashMap<SymbolicInteger,Object>(); // a map between symbolic variables and DP variables
  //static Boolean result; // tells whether result is satisfiable or not
  
  //Converts IntegerExpression's into DP's IntExp's
  //Carson: Can't remove this yet as it's called within SymbolicConstraintsGeneral
  static Object getExpression(IntegerExpression eRef) {
    assert eRef != null;
    assert !(eRef instanceof IntegerConstant);

    if (eRef instanceof SymbolicInteger) {
      Object dp_var = symIntegerVar.get(eRef);
      if (dp_var == null) {
        dp_var = pb.makeIntVar(((SymbolicInteger)eRef).getName(),
            ((SymbolicInteger)eRef)._min, ((SymbolicInteger)eRef)._max);
        symIntegerVar.put((SymbolicInteger)eRef, dp_var);
      }
      return dp_var;
    }

    Operator    opRef;
    IntegerExpression	e_leftRef;
    IntegerExpression	e_rightRef;

    if(eRef instanceof BinaryLinearIntegerExpression) {
      opRef = ((BinaryLinearIntegerExpression)eRef).op;
      e_leftRef = ((BinaryLinearIntegerExpression)eRef).left;
      e_rightRef = ((BinaryLinearIntegerExpression)eRef).right;
    } else { // bin non lin expr
      if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
        opRef = ((BinaryNonLinearIntegerExpression)eRef).op;
        e_leftRef = ((BinaryNonLinearIntegerExpression)eRef).left;
        e_rightRef = ((BinaryNonLinearIntegerExpression)eRef).right;
      }
      else
        throw new RuntimeException("## Error: Binary Non Linear Expression " + eRef);
    }
    switch(opRef){
      case PLUS:
        if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.plus(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.plus(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else
          return pb.plus(getExpression(e_leftRef),getExpression(e_rightRef));
      case MINUS:
        if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.minus(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.minus(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else
          return pb.minus(getExpression(e_leftRef),getExpression(e_rightRef));
      case MUL:
        if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.mult(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.mult(((IntegerConstant)e_rightRef).value,getExpression(e_leftRef));
        else {
          if(pb instanceof ProblemCoral || pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize ||  pb instanceof ProblemZ3BitVector ||
          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental)
            return pb.mult(getExpression(e_leftRef),getExpression(e_rightRef));
          else
            throw new RuntimeException("## Error: Binary Non Linear Operation");
        }
      case DIV:
        if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant) // TODO: this might not be linear
          return pb.div(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.div(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else {
          if(pb instanceof ProblemCoral || pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental)
            return pb.div(getExpression(e_leftRef),getExpression(e_rightRef));
          else
            throw new RuntimeException("## Error: Binary Non Linear Operation");
        }
      case REM:
        if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant) // TODO: this might not be linear
          return pb.rem(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.rem(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else {
          if(pb instanceof ProblemCoral || pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental)
            return pb.rem(getExpression(e_leftRef),getExpression(e_rightRef));
          else
            throw new RuntimeException("## Error: Binary Non Linear Operation");
        }
      case AND:
        if(e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.and(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.and(((IntegerConstant)e_rightRef).value,getExpression(e_leftRef));
        else
          return pb.and(getExpression(e_leftRef),getExpression(e_rightRef));
      case OR:
        if(e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.or(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.or(((IntegerConstant)e_rightRef).value,getExpression(e_leftRef));
        else
          return pb.or(getExpression(e_leftRef),getExpression(e_rightRef));
      case XOR:
        if(e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.xor(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.xor(((IntegerConstant)e_rightRef).value,getExpression(e_leftRef));
        else
          return pb.xor(getExpression(e_leftRef),getExpression(e_rightRef));
      case SHIFTR:
        if(e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.shiftR(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.shiftR(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else
          return pb.shiftR(getExpression(e_leftRef),getExpression(e_rightRef));
      case SHIFTUR:
        if(e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.shiftUR(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.shiftUR(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else
          return pb.shiftUR(getExpression(e_leftRef),getExpression(e_rightRef));
      case SHIFTL:
        if(e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
          throw new RuntimeException("## Error: this is not a symbolic expression"); //
        else if (e_leftRef instanceof IntegerConstant)
          return pb.shiftL(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
        else if (e_rightRef instanceof IntegerConstant)
          return pb.shiftL(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
        else
          return pb.shiftL(getExpression(e_leftRef),getExpression(e_rightRef));
      default:
        throw new RuntimeException("## Error: Binary Non Linear Operation");
    }
  }

  /**
   * Merges the given path condition with the given ProblemGeneral object (i.e. the solver).
   * Normally the merging means only adding the assertions from the path condition to the 
   * solver's internal representation.
   * 
   * @param pc PathCondition
   * @param pbtosolve ProblemGeneral
   * @return the merged ProblemGeneral object; NULL if problem is unsat
   */
  public static ProblemGeneral parse(PathCondition pc, ProblemGeneral pbtosolve) {
    pb = pbtosolve;
    
    symRealVar = new HashMap<SymbolicReal,Object>();
    symIntegerVar = new HashMap<SymbolicInteger,Object>();
    
    Constraint cRef = pc.header;
    
    pgv = new ProblemGeneralVisitor(pb);
    
    if(pb instanceof IncrementalSolver) {
      //If we use an incremental solver, then we push the context
      //*before* adding only the constraint header

    	setPGV(cRef);
    	if(!cRef.accept(pgv)) {
			return null;
		}
    } else {
        //For a non-incremental solver, we submit the *entire* pc to the solver
    	while(cRef != null) {
    		setPGV(cRef);
    		if(!cRef.accept(pgv)) {
    			return null;
    		}
    		cRef = cRef.and;
    	}
    }
    return pb;
  }

  /**
   * Sets what type of visitor will be created based on the constraint being parsed.
   * 
   * @param cRef - the Constraint to create a visitor for.
   * @author Carson Smith
   */
  private static void setPGV(Constraint cRef) {
	  
	  if (cRef instanceof RealConstraint) {
		  pgv = new RealConstraintVisitor(pb);
	  } else if (cRef instanceof LinearIntegerConstraint)  {
		  pgv = new LinearIntegerConstraintVisitor(pb);
	  } else if (cRef instanceof MixedConstraint) {
		  pgv = new MixedConstraintVisitor(pb);
	  } else if (cRef instanceof LogicalORLinearIntegerConstraints) {
		  pgv = new LogicalORLinearIntegerConstraintVisitor(pb);
	  } else if (cRef instanceof ArrayConstraint) {
		  pgv = new ArrayConstraintVisitor(pb);
	  } else if (cRef instanceof RealArrayConstraint) {
		  pgv = new RealArrayConstraintVisitor(pb);
	  } else if (cRef instanceof NonLinearIntegerConstraint) {
		  pgv = new NonLinearIntegerConstraintVisitor(pb);
	  } else {
		  throw new RuntimeException("PCParser - Unknown constraint type. Create a visitor for it.\n" + cRef.getClass());
	  }
  }
}
