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

import gov.nasa.jpf.symbc.numeric.PathCondition;

public class DebugSolvers extends ProblemGeneral {

	private ProblemGeneral[] probs;
	private int numSolvers;
	private boolean alwaysPrint;
	private PathCondition p;

	public DebugSolvers(PathCondition pc) {
		p = pc;

		alwaysPrint = false;
		numSolvers = 3;
		probs = new ProblemGeneral[numSolvers];

		probs[0] = new ProblemChoco();
//		probs[1] = new ProblemChoco2();
		probs[2] = new ProblemCoral();
	}

	public class SolverObjects {
		private Object[] cons;

		public SolverObjects() {
			cons = new Object[numSolvers];
		}

		public Object getConstraint(int i) {
			return cons[i];
		}

		public void setConstraint(int i, Object o) {
			cons[i] = o;
		}
	}

	@Override
	public Object and(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].and(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object and(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].and(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object and(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].and(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object div(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].div(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object div(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].div(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object div(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].div(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object div(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].and(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object div(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].div(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object eq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].eq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object eq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].eq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object eq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].eq(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object eq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].eq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object eq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].eq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object geq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].geq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object geq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].geq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object geq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].geq(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object geq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].geq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object geq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].geq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public long getIntValue(Object dpVar) {
		return probs[0].getIntValue(((SolverObjects) dpVar).getConstraint(0));
	}

	@Override
	public double getRealValue(Object dpVar) {
		return probs[0].getRealValue(((SolverObjects) dpVar).getConstraint(0));
	}

	@Override
	public double getRealValueInf(Object dpvar) {
		return probs[0].getRealValueInf(((SolverObjects) dpvar).getConstraint(0));
	}

	@Override
	public double getRealValueSup(Object dpVar) {
		return probs[0].getRealValueSup(((SolverObjects) dpVar).getConstraint(0));
	}

	@Override
	public Object gt(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].gt(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object gt(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].gt(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object gt(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].gt(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object gt(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].gt(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object gt(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].gt(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object leq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].leq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object leq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].leq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	public Object leq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].leq(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object leq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].leq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object leq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].leq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object lt(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].lt(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object lt(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].lt(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object lt(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].lt(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object lt(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].lt(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object lt(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].lt(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object makeIntVar(String name, long min, long max) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].makeIntVar(name, min, max));
		}
		return so;
	}

	@Override
	public Object makeRealVar(String name, double min, double max) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].makeRealVar(name, min, max));
		}
		return so;
	}

	@Override
	public Object minus(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].minus(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object minus(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].minus(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object minus(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].minus(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object minus(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].minus(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object minus(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].minus(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object mixed(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].mixed(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object mult(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].mult(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object mult(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].mult(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object mult(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].mult(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object mult(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].mult(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object mult(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].mult(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object neq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].neq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object neq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].neq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object neq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].neq(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object neq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].neq(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object neq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].neq(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object or(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].or(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object or(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].or(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object or(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].or(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object plus(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].plus(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object plus(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].plus(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object plus(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].plus(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object plus(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].plus(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object plus(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].plus(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public void post(Object constraint) {
		for (int i = 0; i < numSolvers; i++) {
			probs[i].post(((SolverObjects) constraint).getConstraint(i));
		}
	}

	@Override
	public Object shiftL(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].shiftL(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object shiftL(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].shiftL(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object shiftL(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].shiftL(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object shiftR(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].shiftR(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object shiftR(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].shiftR(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object shiftR(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].shiftR(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object shiftUR(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].shiftUR(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object shiftUR(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].shiftUR(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object shiftUR(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so
					.setConstraint(i, probs[i].shiftUR(((SolverObjects) exp1)
							.getConstraint(i), ((SolverObjects) exp2)
							.getConstraint(i)));
		}
		return so;
	}

	@Override
	public
	Boolean solve() {
		boolean[] solved = new boolean[numSolvers];
		for (int i = 0; i < numSolvers; i++) {
			Boolean s = probs[i].solve();
			if (s == null) {
				solved[i] = false;
			} else {
				solved[i] = s;
			}

			if (alwaysPrint) {
				System.out.println("Solver " + Integer.toString(i) + ": " + Boolean.toString(solved[i]));
			}
		}

		if (!alwaysPrint) {
			boolean first = solved[0];
			boolean print = false;
			for (int j = 1; j < numSolvers; j++) {
				if (solved[j] != first) {
					print = true;
					break;
				}
			}
			if (print) {
				System.out.println("---- SOLVERS DISAGREE! ------");
				System.out.println(p.toString());
				for (int i = 0; i < numSolvers; i++) {
					System.out.println("   Solver " + Integer.toString(i) + ": "
							+ Boolean.toString(solved[i]));
				}
			}
		}

		return solved[0];
	}

	@Override
	public Object xor(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].xor(value, ((SolverObjects) exp)
					.getConstraint(i)));
		}
		return so;
	}

	@Override
	public Object xor(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].xor(((SolverObjects) exp)
					.getConstraint(i), value));
		}
		return so;
	}

	@Override
	public Object xor(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].xor(((SolverObjects) exp1).getConstraint(i), ((SolverObjects) exp2).getConstraint(i)));
		}
		return so;
	}

	@Override
	public void postLogicalOR(Object[] constraint) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error LogicalOR not implemented");
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
