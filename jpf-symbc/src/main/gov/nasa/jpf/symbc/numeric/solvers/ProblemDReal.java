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

import java.util.ArrayList;
import java.util.List;

import proteus.dl.semantics.Valuation;
import proteus.dl.syntax.AbsTerm;
import proteus.dl.syntax.AdditionTerm;
import proteus.dl.syntax.ArcCosTerm;
import proteus.dl.syntax.ArcSinTerm;
import proteus.dl.syntax.ArcTan2Term;
import proteus.dl.syntax.ArcTanTerm;
import proteus.dl.syntax.ComparisonFormula;
import proteus.dl.syntax.CosTerm;
import proteus.dl.syntax.DivisionTerm;
import proteus.dl.syntax.ExpTerm;
import proteus.dl.syntax.FalseFormula;
import proteus.dl.syntax.LogTerm;
import proteus.dl.syntax.MultiplicationTerm;
import proteus.dl.syntax.NegativeTerm;
import proteus.dl.syntax.OrFormula;
import proteus.dl.syntax.PowerTerm;
import proteus.dl.syntax.Real;
import proteus.dl.syntax.RealVariable;
import proteus.dl.syntax.SinTerm;
import proteus.dl.syntax.SqrtTerm;
import proteus.dl.syntax.SubtractionTerm;
import proteus.dl.syntax.TanTerm;
import proteus.dl.syntax.Term;
import proteus.dl.syntax.TrueFormula;
import proteus.dl.syntax.dLFormula;
import proteus.logicsolvers.abstractions.LogicSolverResult;
import proteus.logicsolvers.drealkit.dRealInterface;

/** Additional Parameters:
  * dreal.mode = strictified or relaxed
  * dreal.precision=0.001
  * dreal.timeBound=10000   (in milliseconds) 
  * Instances are not thread-safe. 
  * @author Nima Roohi */
public abstract class ProblemDReal extends ProblemGeneral {

	private static class ProblemDRealRelaxed extends ProblemDReal {

		public ProblemDRealRelaxed(final double precision, final int timeBound) {
			super(Mode.RELAXED, precision, timeBound);
			assert (precision >= 0);
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula eq(final Object lhs, final Object rhs) {
			return comp("=", (Term) lhs, (Term) rhs);
		}

		@Override
		public ComparisonFormula eq(final double value, final Object exp) {
			return comp("=", (Term) exp, constant(value));
		}

		@Override
		public ComparisonFormula eq(final Object exp, final double value) {
			return comp("=", (Term) exp, constant(value));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public dLFormula neq(final Object lhs, final Object rhs) {
			return TRUE;
		}

		@Override
		public dLFormula neq(final double value, final Object exp) {
			return TRUE;
		}

		@Override
		public dLFormula neq(final Object exp, final double value) {
			return TRUE;
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula leq(final Object lhs, final Object rhs) {
			return comp("<=", (Term) lhs, (Term) rhs);
		}

		@Override
		public ComparisonFormula leq(final double value, final Object exp) {
			return comp(">=", (Term) exp, constant(value));
		}

		@Override
		public ComparisonFormula leq(final Object exp, final double value) {
			return comp("<=", (Term) exp, constant(value));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula geq(final Object lhs, final Object rhs) {
			return comp(">=", (Term) lhs, (Term) rhs);
		}

		@Override
		public ComparisonFormula geq(final double value, final Object exp) {
			return comp("<=", (Term) exp, constant(value));
		}

		@Override
		public ComparisonFormula geq(final Object exp, final double value) {
			return comp(">=", (Term) exp, constant(value));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula lt(final Object lhs, final Object rhs) {
			return comp("<", (Term) lhs, (Term) rhs);
		}

		@Override
		public ComparisonFormula lt(final double value, final Object exp) {
			return comp(">", (Term) exp, constant(value));
		}

		@Override
		public ComparisonFormula lt(final Object exp, final double value) {
			return comp("<", (Term) exp, constant(value));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula gt(final Object lhs, final Object rhs) {
			return comp(">", (Term) lhs, (Term) rhs);
		}

		@Override
		public ComparisonFormula gt(final double value, final Object exp) {
			return comp("<", (Term) exp, constant(value));
		}

		@Override
		public ComparisonFormula gt(final Object exp, final double value) {
			return comp(">", (Term) exp, constant(value));
		}

		private static TrueFormula TRUE = new TrueFormula();

		@Override
		public Object rem(Object exp1, Object exp2) {
			throw new UnsupportedOperationException("## Error: dReal unsupported operation");
		}

		@Override
		public Object rem(long exp1, Object exp2) {
			throw new UnsupportedOperationException("## Error: dReal unsupported operation");
		}

		@Override
		public Object rem(Object exp1, long exp2) {
			throw new UnsupportedOperationException("## Error: dReal unsupported operation");
		}
	}

	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------

	private static class ProblemDRealStrict extends ProblemDReal {

		public ProblemDRealStrict(final double precision, final int timeBound) {
			super(Mode.STRICTIFIED, precision, timeBound);
			assert (precision > 0);
			this.precision = constant(precision);
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public dLFormula eq(final Object lhs, final Object rhs) {
			return FALSE;
		}

		@Override
		public dLFormula eq(final double value, final Object exp) {
			return FALSE;
		}

		@Override
		public dLFormula eq(final Object exp, final double value) {
			return FALSE;
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public dLFormula neq(final Object lhs, final Object rhs) {
			return new OrFormula(//
					comp("<", (Term) lhs, minus(rhs, precision)), //
					comp(">", (Term) lhs, plus(rhs, precision)));
		}

		@Override
		public dLFormula neq(final double lhs, final Object rhs) {
			return new OrFormula(//
					comp("<", (Term) rhs, constant(lhs - super.precision)), //
					comp(">", (Term) rhs, constant(lhs + super.precision)));
		}

		@Override
		public dLFormula neq(final Object lhs, final double rhs) {
			return new OrFormula(//
					comp("<", (Term) lhs, constant(rhs - super.precision)), //
					comp(">", (Term) lhs, constant(rhs + super.precision)));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula leq(final Object lhs, final Object rhs) {
			return comp("<=", (Term) lhs, minus(rhs, precision));
		}

		@Override
		public ComparisonFormula leq(final double value, final Object exp) {
			return comp(">=", (Term) exp, constant(value + super.precision));
		}

		@Override
		public ComparisonFormula leq(final Object exp, final double value) {
			return comp("<=", (Term) exp, constant(value - super.precision));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula geq(final Object lhs, final Object rhs) {
			return comp(">=", (Term) lhs, plus(rhs, precision));
		}

		@Override
		public ComparisonFormula geq(final double value, final Object exp) {
			return comp("<=", (Term) exp, constant(value - super.precision));
		}

		@Override
		public ComparisonFormula geq(final Object exp, final double value) {
			return comp(">=", (Term) exp, constant(value + super.precision));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula lt(final Object lhs, final Object rhs) {
			return comp("<", (Term) lhs, minus(rhs, precision));
		}

		@Override
		public ComparisonFormula lt(final double value, final Object exp) {
			return comp(">", (Term) exp, constant(value + super.precision));
		}

		@Override
		public ComparisonFormula lt(final Object exp, final double value) {
			return comp("<", (Term) exp, constant(value - super.precision));
		}

		// ------------------------------------------------------------------------------------------------------------------

		@Override
		public ComparisonFormula gt(final Object lhs, final Object rhs) {
			return comp(">", (Term) lhs, plus(rhs, precision));
		}

		@Override
		public ComparisonFormula gt(final double value, final Object exp) {
			return comp("<", (Term) exp, constant(value - super.precision));
		}

		@Override
		public ComparisonFormula gt(final Object exp, final double value) {
			return comp(">", (Term) exp, constant(value + super.precision));
		}

		private final Real precision;
		private static FalseFormula FALSE = new FalseFormula();
		@Override
		public Object rem(Object exp1, Object exp2) {
			throw new UnsupportedOperationException("## Error: dReal unsupported operation");
		}

		@Override
		public Object rem(long exp1, Object exp2) {
			throw new UnsupportedOperationException("## Error: dReal unsupported operation");
		}

		@Override
		public Object rem(Object exp1, long exp2) {
			throw new UnsupportedOperationException("## Error: dReal unsupported operation");
		}
	}

	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public abstract dLFormula leq(double value, Object exp);

	@Override
	public abstract dLFormula leq(Object exp, double value);

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public RealVariable makeRealVar(final String name, final double min, final double max) {
		final RealVariable res = new RealVariable(name);
		/* The current dReal interface does not support bounded existential quantifier. So I am saving the given bounds to be
		 * used later. Note that it means I am assuming any variable that is created here, will be used in the given
		 * constraints. Otherwise, redundant constraints will be given to dReal that has no effect on the output but only makes
		 * it slower! */
		if (Double.isNaN(min))
			throw new IllegalArgumentException("'min' must be a number");
		if (Double.isNaN(max))
			throw new IllegalArgumentException("'max' must be a number");
		if (!Double.isInfinite(min))
			formulas.add(leq(min, res));
		else if (min > 0)
			throw new IllegalArgumentException("'min' cannot be positive infinity");
		if (!Double.isInfinite(max))
			formulas.add(leq(res, max));
		else if (max < 0)
			throw new IllegalArgumentException("'max' cannot be negative infinity");
		return res;
	}

	@Override
	public Real constant(final double value) {
		if (!Double.isFinite(value))
			throw new IllegalArgumentException("'value' must be finite");
		return new Real(value);
	}

	// ------------------------------------------------------------------------------------------------------------------

	protected ComparisonFormula comp(final String op, final Term lhs, final Term rhs) {
		return new ComparisonFormula(op, lhs, rhs);
	}

	private static boolean isZero(final Term t) {
		return ZERO.equals(t) || ZERO2.equals(t);
	}

	private static boolean isOne(final Term t) {
		return ONE.equals(t);
	}

	// ------------------------------------------------------------------------------------------------------------------

	public Term plus(final Term lhs, final Term rhs) {
		if (isZero(lhs))
			return rhs;
		if (isZero(rhs))
			return lhs;
		return new AdditionTerm(lhs, rhs);
	}

	@Override
	public Term plus(final Object lhs, final Object rhs) {
		return plus((Term) lhs, (Term) rhs);
	}

	@Override
	public Term plus(final double value, final Object exp) {
		return plus(constant(value), (Term) exp);
	}

	@Override
	public Term plus(final Object exp, final double value) {
		return plus((Term) exp, constant(value));
	}

	// ------------------------------------------------------------------------------------------------------------------

	public Term minus(final Term lhs, final Term rhs) {
		if (isZero(rhs))
			return lhs;
		if (isZero(lhs))
			return new NegativeTerm(rhs);
		return new SubtractionTerm(lhs, rhs);
	}

	@Override
	public Term minus(final Object lhs, final Object rhs) {
		return minus((Term) lhs, (Term) rhs);
	}

	@Override
	public Term minus(final double value, final Object exp) {
		return minus(constant(value), (Term) exp);
	}

	@Override
	public Term minus(final Object exp, final double value) {
		if (isZero((Term) exp))
			return constant(-value);
		return minus((Term) exp, constant(value));
	}

	// ------------------------------------------------------------------------------------------------------------------

	public Term mult(final Term lhs, final Term rhs) {
		if (isZero(lhs) || isZero(rhs))
			return ZERO;
		if (isOne(rhs))
			return lhs;
		if (isOne(lhs))
			return rhs;
		return new MultiplicationTerm(lhs, rhs);
	}

	@Override
	public Term mult(final Object lhs, final Object rhs) {
		return mult((Term) lhs, (Term) rhs);
	}

	@Override
	public Term mult(final double value, final Object exp) {
		return mult(constant(value), (Term) exp);
	}

	@Override
	public Term mult(final Object exp, final double value) {
		return mult((Term) exp, constant(value));
	}

	// ------------------------------------------------------------------------------------------------------------------

	public Term div(final Term lhs, final Term rhs) {
		if (isZero(lhs))
			return ZERO;
		if (isOne(rhs))
			return lhs;
		return new DivisionTerm(lhs, rhs);
	}

	@Override
	public Term div(final Object lhs, final Object rhs) {
		return div((Term) lhs, (Term) rhs);
	}

	@Override
	public Term div(final double value, final Object exp) {
		return div(constant(value), (Term) exp);
	}

	@Override
	public Term div(final Object exp, final double value) {
		if (isOne((Term) exp))
			return constant(1.0 / value);
		return div((Term) exp, constant(value));
	}

	// ------------------------------------------------------------------------------------------------------------------

	//@Override
	public Term abs(final Object exp) {
		return new AbsTerm((Term) exp);
	}

	@Override
	public Term sin(final Object exp) {
		return new SinTerm((Term) exp);
	}

	@Override
	public Term cos(final Object exp) {
		return new CosTerm((Term) exp);
	}

	@Override
	public Term asin(final Object exp) {
		return new ArcSinTerm((Term) exp);
	}

	@Override
	public Term acos(final Object exp) {
		return new ArcCosTerm((Term) exp);
	}

	@Override
	public Term tan(final Object exp) {
		return new TanTerm((Term) exp);
	}

	@Override
	public Term atan(final Object exp) {
		return new ArcTanTerm((Term) exp);
	}

	@Override
	public Term atan2(final Object lhs, final Object rhs) {
		return new ArcTan2Term((Term) lhs, (Term) rhs);
	}

	@Override
	public Term atan2(final Object lhs, final double rhs) {
		return new ArcTan2Term((Term) lhs, constant(rhs));
	}

	@Override
	public Term atan2(final double lhs, final Object rhs) {
		return new ArcTan2Term(constant(lhs), (Term) rhs);
	}

	@Override
	public Term exp(final Object exp) {
		return new ExpTerm((Term) exp);
	}

	@Override
	public Term log(final Object exp) {
		return new LogTerm((Term) exp);
	}

	@Override
	public Term sqrt(final Object exp) {
		return new SqrtTerm((Term) exp);
	}

	@Override
	public Term power(final Object lhs, final Object rhs) {
		return new PowerTerm((Term) lhs, (Term) rhs);
	}

	@Override
	public Term power(final Object lhs, final double rhs) {
		return new PowerTerm((Term) lhs, constant(rhs));
	}

	@Override
	public Term power(final double lhs, final Object rhs) {
		return new PowerTerm(constant(lhs), (Term) rhs);
	}

	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Object makeIntVar(final String name, final long min, final long max) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer Variables");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public ComparisonFormula eq(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public ComparisonFormula eq(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public ComparisonFormula neq(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public ComparisonFormula neq(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public ComparisonFormula leq(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public ComparisonFormula leq(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public ComparisonFormula geq(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public ComparisonFormula geq(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public ComparisonFormula lt(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public ComparisonFormula lt(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public ComparisonFormula gt(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public ComparisonFormula gt(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term plus(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public Term plus(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term minus(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public Term minus(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term mult(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public Term mult(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term div(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	@Override
	public Term div(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support integer values");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term and(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term and(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term and(final Object exp1, final Object exp2) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term or(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term or(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term or(final Object exp1, final Object exp2) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term xor(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term xor(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term xor(final Object exp1, final Object exp2) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term shiftL(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftL(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftL(final Object exp1, final Object exp2) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftR(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftR(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftR(final Object exp1, final Object exp2) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftUR(final long value, final Object exp) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftUR(final Object exp, final long value) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	@Override
	public Term shiftUR(final Object exp1, final Object exp2) {
		throw new UnsupportedOperationException("## Error: dReal does not support bitwise operations");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term round(final Object exp) {
		throw new RuntimeException("## Error: Math.round not supported by proteus (discontinuous function)");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Term mixed(final Object exp1, final Object exp2) {
		throw new RuntimeException("## Error: dReal does not support integer arithmetic");
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public long getIntValue(final Object dpVar) {
		throw new RuntimeException("## Error: dReal does not support integer variables");
	}

	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public void postLogicalOR(final Object[] constraint) {
		switch (constraint.length) {
		case 0:
			post(new FalseFormula());
			break;
		case 1:
			post(constraint[0]);
			break;
		default:
			dLFormula fml = (dLFormula) constraint[0];
			for (int i = 1; i < constraint.length; i++)
				fml = new OrFormula(fml, (dLFormula) constraint[i]);
			post(fml);
		}
	}

	@Override
	public void post(final Object constraint) {
		formulas.add((dLFormula) constraint);
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	public Boolean solve() {
		if (state != State.INIT)
			throw new IllegalStateException();

		final int counter;
		synchronized (ProblemDReal.class) {
			counter = ProblemDReal.counter++;
		}
		System.out.println("Calling dReal: " + counter);

		final dRealInterface dReal = precision <= 0 ? new dRealInterface() : new dRealInterface(precision);
		if (timeBound > 0)
			dReal.setTimeBound(timeBound);
    System.out.println(formulas);
    System.out.println("--------------------------------");
		try {
			final LogicSolverResult sol = dReal.findInstance(formulas);
			// for (final Object fml : formulas)
			// System.out.println(fml);
			// System.out.println("-----------------------------------------------------------------------");
			if ("delta-sat".equals(sol.satisfiability) || "sat".equals(sol.satisfiability)) {
				valuation = sol.valuation;
				state = State.SAT;
				return Boolean.TRUE;
			} else if ("unsat".equals(sol.satisfiability) || "delta-unsat".equals(sol.satisfiability)) {
				state = State.UNSAT;
				return Boolean.FALSE;
			} else {
				state = State.UNKNOWN;
				return null;
			}
		} catch (final Exception e) {
			throw new RuntimeException("Unknown error while solving the constraints", e);
		}
	}

	// ------------------------------------------------------------------------------------------------------------------

	@Override
	/**@return a lower bound on the minimum possible value of the input variable that solve the given constraints.*/
	public double getRealValueInf(final Object dpVar) {
		return getRealValue(dpVar) - precision;
	}

	@Override
	/**@return an upper bound on the maximum possible value of the input variable that solve the given constraints.*/
	public double getRealValueSup(final Object dpVar) {
		return getRealValue(dpVar) + precision;
	}

	@Override
	public double getRealValue(final Object dpVar) {
		if (state != State.SAT)
			throw new IllegalStateException("State of the problem is not SAT");
		final RealVariable v = (RealVariable) dpVar;
		if (valuation.containsVariable(v))
			try {
				return valuation.get(v).toDouble();
			} catch (final Exception e) {
				/* Right now this happen if dpVar has an arbitrary assignment. One can return an arbitrary value instead of
				 * re-throwing the exception. If we want to do that, I recommend that the exception be specialized. */
				throw new RuntimeException(e);
			}
		throw new IllegalArgumentException("Variable is undefined");
	}

	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------

	public static ProblemDReal createInstance(final gov.nasa.jpf.Config conf) {
		final Mode mode = Mode.valueOf(conf.getString("dreal.mode", "STRICTIFIED").toUpperCase());
		final double precision = conf.getDouble("dreal.precision", 0.00001);
		final int timeBound = conf.getInt("dreal.timeBound", 0);
		return createInstance(mode, precision, timeBound);
	}

	public static ProblemDReal createInstance(final Mode mode, final double precision, final int timeBound) {
		if (mode == Mode.RELAXED)
			return new ProblemDRealRelaxed(precision, timeBound);
		return new ProblemDRealStrict(precision, timeBound);
	}

	// ------------------------------------------------------------------------------------------------------------------

	protected ProblemDReal(final Mode mode, final double precision, final int timeBound) {
		this.mode = mode;
		this.precision = precision;
		this.timeBound = timeBound;
		checkMode(mode);
		checkPrecision(mode, precision);
		checkTimeBound(timeBound);
	}

	// ------------------------------------------------------------------------------------------------------------------
	// ------------------------------------------------------------------------------------------------------------------

	private void checkMode(final Mode mode) {
		if (mode == null)
			throw new IllegalArgumentException("'mode' cannot be null");
	}

	private void checkPrecision(final Mode mode, final double precision) {
		if (mode == Mode.RELAXED && precision < 0)
			throw new IllegalArgumentException("precision must be non-negative");
		else if (mode == Mode.STRICTIFIED && precision <= 0)
			throw new IllegalArgumentException("precision must be positive");
		if (!Double.isFinite(precision))
			throw new IllegalArgumentException("precision must be finite");
		if (Double.isNaN(precision))
			throw new IllegalArgumentException("precision must be a number");
	}

	private void checkTimeBound(final int timeBound) {
		if (timeBound < 0)
			throw new IllegalArgumentException("'timeBound' must be non-negative");
	}

	public double getPrecision() {
		return precision;
	}

	// ------------------------------------------------------------------------------------------------------------------

	public Mode getMode() {
		return mode;
	}

	// ------------------------------------------------------------------------------------------------------------------

	/** precision must be a non-negative number. Zero means use default value of the interface. */
	private final double precision;

	/** millisecond, it must be a non-negative number. Zero means no time-bound. */
	private final int timeBound;

	private final Mode mode;
	private final List<dLFormula> formulas = new ArrayList<>();
	private State state = State.INIT;
	private Valuation valuation = null;

	private static final Real ZERO = new Real(0.0d);
	private static final Real ZERO2 = new Real(-0.0d);
	private static final Real ONE = new Real(1.0d);

	/** number of time dReal has been called to solve constraint (Performance metric) */
	private static int counter = 0;

	/** Possible states of the problem */
	public static enum State {
		INIT, SAT, UNSAT, UNKNOWN
	}

	/** Modes of the problem */
	public static enum Mode {
		RELAXED, STRICTIFIED
	}
}
