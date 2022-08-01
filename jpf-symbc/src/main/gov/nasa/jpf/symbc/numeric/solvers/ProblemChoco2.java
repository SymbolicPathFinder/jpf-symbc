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

package gov.nasa.jpf.symbc.numeric.solvers;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;

/**
 * Integration of the Choco CP library version 2 (2.1.1, specifically).
 * Currently only supports integer operations.
 *
 * @author staats
 *
 */
/* Rody: add typecasts long->int everywhere now. Needs a nice solution where the user
 * is notified to use another solver with longs.
 */
public class ProblemChoco2 extends ProblemGeneral {
	private CPSolver solver;
	private Model model;
	public static int timeBound = 300;

	public ProblemChoco2() {
		model = new CPModel();
		solver = new CPSolver();
	}

	public Object and(long value, Object exp) {	throw new RuntimeException("## Unsupported and "); }
	public Object and(Object exp, long value) {	throw new RuntimeException("## Unsupported and "); }
	public Object and(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported and "); }

	public Object div(long value, Object exp) { return Choco.div((int) value, (IntegerExpressionVariable) exp); }
	public Object div(Object exp, long value) { return Choco.div((IntegerExpressionVariable) exp, (int) value); }
	public Object div(Object exp1, Object exp2) { return Choco.div((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object div(double value, Object exp) {	throw new RuntimeException("## Unsupported double div "); }
	public Object div(Object exp, double value) {	throw new RuntimeException("## Unsupported double div "); }

	public Object eq(long value, Object exp) { return Choco.eq((int) value, (IntegerExpressionVariable) exp);	}
	public Object eq(Object exp, long value) { return Choco.eq((IntegerExpressionVariable) exp,(int)  value);	}
	public Object eq(Object exp1, Object exp2) { return Choco.eq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp1);	}

	public Object eq(double value, Object exp) {	throw new RuntimeException("## Unsupported eq "); }
	public Object eq(Object exp, double value) {	throw new RuntimeException("## Unsupported eq "); }

	public Object geq(long value, Object exp) { return Choco.geq((int) value, (IntegerExpressionVariable) exp);	}
	public Object geq(Object exp, long value) { return Choco.geq((IntegerExpressionVariable) exp, (int) value);	}
	public Object geq(Object exp1, Object exp2) { return Choco.geq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp1);	}

	public Object geq(double value, Object exp) {	throw new RuntimeException("## Unsupported geq "); }
	public Object geq(Object exp, double value) {	throw new RuntimeException("## Unsupported geq "); }

	public long getIntValue(Object dpVar) {
		try {
			return solver.getVar((IntegerVariable) dpVar).getVal();
		} catch (Throwable t) {
			return ((IntegerVariable) dpVar).getLowB();
		}
	}

	public double getRealValue(Object dpVar) {	throw new RuntimeException("## Unsupported get real value "); }
	public double getRealValueInf(Object dpvar) {	throw new RuntimeException("## Unsupported get real value "); }
	public double getRealValueSup(Object dpVar) {	throw new RuntimeException("## Unsupported get real value "); }

	public Object gt(long value, Object exp) { return Choco.gt((int) value, (IntegerExpressionVariable) exp); }
	public Object gt(Object exp, long value) { return Choco.gt((IntegerExpressionVariable) exp, (int) value); }
	public Object gt(Object exp1, Object exp2) { return Choco.gt((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object gt(double value, Object exp) {	throw new RuntimeException("## Unsupported double gt "); }
	public Object gt(Object exp, double value) {	throw new RuntimeException("## Unsupported double gt "); }

	public Object leq(long value, Object exp) { return Choco.leq((int) value, (IntegerExpressionVariable) exp); }
	public Object leq(Object exp, long value) { return Choco.leq((IntegerExpressionVariable) exp,(int)  value); }
	public Object leq(Object exp1, Object exp2) { return Choco.leq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object leq(double value, Object exp) {	throw new RuntimeException("## Unsupported double leq "); }
	public Object leq(Object exp, double value) {	throw new RuntimeException("## Unsupported double leq "); }

	public Object lt(long value, Object exp) { return Choco.lt((int) value, (IntegerExpressionVariable) exp); }
	public Object lt(Object exp, long value) { return Choco.lt((IntegerExpressionVariable) exp, (int) value); }
	public Object lt(Object exp1, Object exp2) { return Choco.lt((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object lt(double value, Object exp) {	throw new RuntimeException("## Unsupported double lt "); }
	public Object lt(Object exp, double value) {	throw new RuntimeException("## Unsupported double lt "); }

	public Object makeIntVar(String name, long min, long max) {
		assert(min>=Integer.MIN_VALUE && max<=Integer.MAX_VALUE);
		return Choco.makeIntVar(name, (int) min, (int) max);
	}

	public Object makeRealVar(String name, double min, double max) {	throw new RuntimeException("## Unsupported make real "); }

	public Object minus(long value, Object exp) { return Choco.minus((int) value, (IntegerExpressionVariable) exp); }
	public Object minus(Object exp, long value) { return Choco.minus((IntegerExpressionVariable) exp, (int) value); }
	public Object minus(Object exp1, Object exp2)  { return Choco.minus((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object minus(double value, Object exp) {	throw new RuntimeException("## Unsupported double minus "); }
	public Object minus(Object exp, double value) {	throw new RuntimeException("## Unsupported double minus "); }
	public Object mixed(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported mixed "); }

	public Object mult(long value, Object exp) { return Choco.mult((int) value, (IntegerExpressionVariable) exp); }
	public Object mult(Object exp, long value) { return Choco.mult((IntegerExpressionVariable) exp,(int)  value); }
	public Object mult(Object exp1, Object exp2)  { return Choco.mult((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object mult(double value, Object exp) {	throw new RuntimeException("## Unsupported double mult "); }
	public Object mult(Object exp, double value) {	throw new RuntimeException("## Unsupported double mult "); }

	public Object neq(long value, Object exp) { return Choco.neq((int) value, (IntegerExpressionVariable) exp); }
	public Object neq(Object exp, long value) { return Choco.neq((IntegerExpressionVariable) exp, (int) value); }
	public Object neq(Object exp1, Object exp2)  { return Choco.neq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object neq(double value, Object exp) {	throw new RuntimeException("## Unsupported double NEQ "); }
	public Object neq(Object exp, double value) {	throw new RuntimeException("## Unsupported double NEQ "); }

	public Object or(long value, Object exp) {	throw new RuntimeException("## Unsupported OR "); }
	public Object or(Object exp, long value) {	throw new RuntimeException("## Unsupported OR "); }
	public Object or(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported OR "); }

	public Object plus(long value, Object exp) { return Choco.plus((int) value, (IntegerExpressionVariable) exp); }
	public Object plus(Object exp, long value) { return Choco.plus((IntegerExpressionVariable) exp, (int) value); }
	public Object plus(Object exp1, Object exp2)  { return Choco.plus((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	public Object plus(double value, Object exp) {	throw new RuntimeException("## Unsupported double plus "); }
	public Object plus(Object exp, double value) {	throw new RuntimeException("## Unsupported double plus "); }

	public void post(Object constraint) {
		model.addConstraint((Constraint) constraint);
	}

	public Object shiftL(long value, Object exp) {	throw new RuntimeException("## Unsupported shiftL"); }
	public Object shiftL(Object exp, long value) {	throw new RuntimeException("## Unsupported shiftL"); }
	public Object shiftL(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftL"); }

	public Object shiftR(long value, Object exp) {	throw new RuntimeException("## Unsupported shiftR"); }
	public Object shiftR(Object exp, long value) {	throw new RuntimeException("## Unsupported shiftR"); }
	public Object shiftR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftR"); }

	public Object shiftUR(long value, Object exp) {	throw new RuntimeException("## Unsupported shiftUR"); }
	public Object shiftUR(Object exp, long value) {	throw new RuntimeException("## Unsupported shiftUR"); }
	public Object shiftUR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftUR"); }

	/*
	 * One potential issue is determining the best way to build constraints.
	 * Currently the model is reset after solving, and the solver
	 * is reset right before solving. Is this the best way to do this?
	 * We could alternatively pop constraints when backtracking,
	 * though this would require some changes to how ProblemGeneral
	 * is interfaced.
	 *
	 */
	public Boolean solve() {
		solver.read(model);

		System.out.println("Model:" + model.constraintsToString());

		solver.setTimeLimit(timeBound);
		Boolean solved = solver.solve();
		boolean feasible = solver.isFeasible();

		System.out.println("Solved: " + solved);
		System.out.println("Feasible: " + feasible);

		return solved;
	}

	public Object xor(long value, Object exp) { throw new RuntimeException("## Unsupported XOR "); }
	public Object xor(Object exp, long value) { throw new RuntimeException("## Unsupported XOR"); }
	public Object xor(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported XOR"); }

	@Override
	public void postLogicalOR(Object[] constraint) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Choco2 does not support LogicalOR");
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
