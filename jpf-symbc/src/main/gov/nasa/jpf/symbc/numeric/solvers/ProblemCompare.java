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

import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.numeric.PCParser;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import symlib.SymLiteral;
import symlib.SymNumber;
import symlib.Util;
import coral.PC;
import coral.solvers.Env;
import coral.solvers.Result;
import coral.solvers.SolverKind;

/**
 *
 * This class runs all solvers for each query.  Please,
 * keep in mind that, for some queries, some solvers can
 * break (for example, yices and cvc3 does not support
 * trigonometric functions and cvc cannot handle mixed
 * int and float equality constraint).  In those cases,
 * we try to continue execution assigning that query to
 * that solver as unsolved.  The goal of this class is to
 * generate a matrix M where each cell M[i,j] denotes the
 * number of queries that solver i could solve and j
 * could not.
 *
 * We also noted that some solutions reported by choco and
 * yices where incorrect.  To handle those cases, we check
 * whether the answer is actually sat with CORAL.  If not,
 * we mark that query as unsolved to that solver.
 *
 * @author Matheus Arrais (mbas@cin.ufpe.br)
 * @author Mateus Araujo (mab@cin.ufpe.br)
 * @author Marcelo d'Amorim damorim
 *
 */
public class ProblemCompare extends ProblemGeneral {

	private ProblemGeneral[] probs;
	private int numSolvers;
	private boolean alwaysPrint;
	private PathCondition p;
	private SymbolicConstraintsGeneral scg;
	private boolean[] solutions;
	private int selected = 0;
	private static SolvingDiff solvingDiff = new SolvingDiff();
	private Map<String, SolverObjects> intVars; // JPF symbolicInteger varname -> SolverObjects var list
	private Map<String, SolverObjects> realVars; // JPF symbolicReal varname -> SolverObjects var list
	private boolean[] ignoredSolvers; //marks solvers that don't support an operation present in the pc (like exp for choco)


	public ProblemCompare(PathCondition pc,SymbolicConstraintsGeneral scg) {
		p = pc;
		this.scg = scg;

		alwaysPrint = false;
		numSolvers = 7;
		solutions = new boolean[numSolvers];
		probs = new ProblemGeneral[numSolvers];
		intVars = new HashMap<String, SolverObjects>();
		realVars = new HashMap<String, SolverObjects>();

//		probs[0] = new ProblemCoral(SolverKind.PSO_OPT4J, true);
//		probs[1] = new ProblemCoral(SolverKind.PSO_OPT4J, false);
//		probs[2] = new ProblemCoral(SolverKind.RANDOM, true);
//		probs[3] = new ProblemCoral(SolverKind.RANDOM, false);
		probs[4] = new ProblemChoco();
		probs[5] = new ProblemCVC3();
		probs[6] = new ProblemYices();

		solvingDiff.init(numSolvers);
		ignoredSolvers = new boolean[numSolvers];
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
			try {
				so.setConstraint(i,
						probs[i].and(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object and(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].and(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object and(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].and(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object div(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].div(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object div(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].div(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object div(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].div(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object div(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].and(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object div(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].div(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object eq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].eq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object eq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].eq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object eq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].eq(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object eq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].eq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object eq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].eq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object geq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].geq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object geq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].geq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object geq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].geq(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object geq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].geq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object geq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].geq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public long getIntValue(Object dpVar) {
		return probs[selected].getIntValue(((SolverObjects) dpVar).getConstraint(selected));
	}

	@Override
	public double getRealValue(Object dpVar) {
		return probs[selected].getRealValue(((SolverObjects) dpVar).getConstraint(selected));
	}

	@Override
	public double getRealValueInf(Object dpVar) {
		//return probs[0].getRealValueInf(((SolverObjects) dpVar).getConstraint(0));
		return -1;
	}

	@Override
	public double getRealValueSup(Object dpVar) {
//		return probs[0].getRealValueSup(((SolverObjects) dpVar).getConstraint(0));
		return -1;
	}

	@Override
	public Object gt(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].gt(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object gt(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].gt(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object gt(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].gt(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object gt(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].gt(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object gt(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].gt(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object leq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].leq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object leq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].leq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object leq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].leq(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object leq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].leq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object leq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].leq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object lt(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].lt(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object lt(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].lt(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object lt(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].lt(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object lt(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].lt(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object lt(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].lt(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object makeIntVar(String name, long min, long max) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].makeIntVar(name, min, max));
		}
		//store [varName:varList]
		intVars.put(name, so);
		return so;
	}

	@Override
	public Object makeRealVar(String name, double min, double max) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			so.setConstraint(i, probs[i].makeRealVar(name, min, max));
		}
		//store [varName:varList]
		realVars.put(name, so);
		return so;
	}

	@Override
	public Object minus(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
		    try {
			so.setConstraint(i, probs[i].minus(value, ((SolverObjects) exp)
					.getConstraint(i)));
		    } catch(Exception e) {
			ignoredSolvers[i] = true;
		    }
		}
		return so;
	}

	@Override
	public Object minus(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
		    try {
			so.setConstraint(i, probs[i].minus(((SolverObjects) exp)
					.getConstraint(i), value));
		    } catch(Exception e) {
			ignoredSolvers[i] = true;
		    }
		}
		return so;
	}

	@Override
	public Object minus(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
		    try {
			so
			.setConstraint(i, probs[i].minus(((SolverObjects) exp1)
					.getConstraint(i), ((SolverObjects) exp2)
					.getConstraint(i)));
		    } catch(Exception e) {
			ignoredSolvers[i] = true;
		    }
		}
		return so;
	}

	@Override
	public Object minus(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
		    try {
			so.setConstraint(i, probs[i].minus(value, ((SolverObjects) exp)
					.getConstraint(i)));
		    } catch(Exception e) {
			ignoredSolvers[i] = true;
		    }
		}
		return so;
	}

	@Override
	public Object minus(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
		    try {
			so.setConstraint(i, probs[i].minus(((SolverObjects) exp)
					.getConstraint(i), value));
		    } catch(Exception e) {
			ignoredSolvers[i] = true;
		    }
		}
		return so;
	}

	@Override
	public Object mixed(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
		    try {
			so.setConstraint(i, probs[i].mixed(((SolverObjects) exp1)
					.getConstraint(i), ((SolverObjects) exp2)
					.getConstraint(i)));
		    } catch(Exception e){
					ignoredSolvers[i] = true;
		    }
		}
		return so;
	}

	@Override
	public Object mult(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].mult(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object mult(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].mult(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object mult(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].mult(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object mult(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].mult(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object mult(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].mult(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object neq(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].neq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object neq(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].neq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object neq(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].neq(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object neq(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].neq(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object neq(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].neq(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object or(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].or(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object or(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].or(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object or(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].or(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object plus(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].plus(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object plus(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].plus(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object plus(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].plus(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object plus(double value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].plus(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object plus(Object exp, double value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].plus(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public void post(Object constraint) {
		for (int i = 0; i < numSolvers; i++) {
			if(ignoredSolvers[i]) {
				System.out.println("not posting constraint to " + probs[i] + " : ignored ");
			} else {
				probs[i].post(((SolverObjects) constraint).getConstraint(i));
			}
		}
	}

	@Override
	public Object shiftL(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].shiftL(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftL(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].shiftL(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftL(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].shiftL(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftR(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].shiftR(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftR(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].shiftR(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftR(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].shiftR(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftUR(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].shiftUR(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftUR(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].shiftUR(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object shiftUR(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].shiftUR(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object xor(long value, Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].xor(value, ((SolverObjects) exp).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object xor(Object exp, long value) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].xor(((SolverObjects) exp).getConstraint(i), value));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	@Override
	public Object xor(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].xor(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (Exception e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	// trigonometric exps

	public Object sin(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].sin(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object cos(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].cos(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object round(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].round(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object exp(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].exp(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object asin(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].asin(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;

	}

	public Object acos(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].acos(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;

	}

	public Object atan(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].atan(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;

	}

	public Object log(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].log(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object tan(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].tan(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object sqrt(Object exp) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].sqrt(((SolverObjects) exp).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object power(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].power(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object power(Object exp1, double exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].power(((SolverObjects) exp1).getConstraint(i), exp2));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object power(double exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].power(exp1, ((SolverObjects) exp2).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object atan2(Object exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i, probs[i].atan2(
						((SolverObjects) exp1).getConstraint(i),
						((SolverObjects) exp2).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object atan2(Object exp1, double exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].atan2(((SolverObjects) exp1).getConstraint(i), exp2));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	public Object atan2(double exp1, Object exp2) {
		SolverObjects so = new SolverObjects();
		for (int i = 0; i < numSolvers; i++) {
			try {
				so.setConstraint(i,
						probs[i].atan2(exp1, ((SolverObjects) exp2).getConstraint(i)));
			} catch (RuntimeException e) {
				ignoredSolvers[i] = true;
			}
		}
		return so;
	}

	//pbToCheck >= 1 (posicao 0 reservada para coral)
	public Env check(Map<String, SolverObjects> intVars, Map<String, SolverObjects> realVars, int pbToCheck) {

		ProblemGeneral pb = probs[pbToCheck];
		Map<SymLiteral,SymNumber> coralMap = new HashMap<SymLiteral,SymNumber>();
		Env env = new Env(coralMap, Result.UNK, SolverKind.RANDOM);
		boolean validSolution = true;

		//extracting int values
		for(Entry<String,SolverObjects> entry : intVars.entrySet()) {
			SolverObjects valueList = entry.getValue();
			Object coralLiteral = valueList.getConstraint(0);
			Object otherLiteral = valueList.getConstraint(pbToCheck);
			long val = pb.getIntValue(otherLiteral);
			coralMap.put((SymLiteral) coralLiteral, Util.createConstant(val));
			//System.out.println(literal + " : " + val);
		}

		//extract real values
		try {
			for(Entry<String,SolverObjects> entry : realVars.entrySet()) {
				SolverObjects valueList = entry.getValue();
				Object coralLiteral = valueList.getConstraint(0);
				Object otherLiteral = valueList.getConstraint(pbToCheck);
					double val = pb.getRealValue(otherLiteral);
					coralMap.put((SymLiteral) coralLiteral, Util.createConstant(val));
				//System.out.println(literal + " : " + val);
			}
		} catch(Exception exp) { //reproducing hack to get the value of undefined variables in choco (and possibly others)
			//if constraint contains real variables, use choco hack to find them
			if(realVars.size() > 0) {
				Map<SymbolicReal,Object> realVarsChoco = extractProblemVars(PCParser.symRealVar,pbToCheck);
				Map<SymbolicReal,Object> reprocessedRealVarsChoco = scg.catchBody(realVarsChoco,pb,p);

				if(reprocessedRealVarsChoco != null) {
					Map<String,Double> realValuesChoco = extractValues(reprocessedRealVarsChoco);
					for(Entry<String,Double> entry : realValuesChoco.entrySet()) {
						Object coralLiteral = realVars.get(entry.getKey()).getConstraint(0);
						double val = entry.getValue();
						coralMap.put((SymLiteral) coralLiteral, Util.createConstant(val));
						//System.out.println(literal + " : " + val);
					}
				} else { //pb could not find a solution
					validSolution = false;
				}
			}
		}

		if(validSolution) {
	    PC pcTmp = ((ProblemCoral) probs[0]).getPc().replaceVars(env);
	    if (pcTmp.eval()) {
	      env.setResult(Result.SAT);
	      System.out.println("### Check - SAT");
	    }
		}

		return env;
	}



	private Map<String, Double> extractValues(
			Map<SymbolicReal, Object> vars) {
		Map<String, Double> vals = new HashMap<String,Double>();

		for(SymbolicReal entry : vars.keySet()) {
			String name = entry.getName();
			Double val = entry.solution;
			vals.put(name,val);
		}
		return vals;
	}

	private Map<SymbolicReal, Object> extractProblemVars(Map<SymbolicReal, Object> symRealVar, int pbToCheck) {
		Map<SymbolicReal, Object> extractedVars = new HashMap<SymbolicReal, Object>();

		for(Entry<SymbolicReal, Object> entry : symRealVar.entrySet()) {
			Object var = ((SolverObjects)entry.getValue()).getConstraint(pbToCheck);
			extractedVars.put(entry.getKey(), var);
		}

		return extractedVars;
	}

	@Override
	public Boolean solve() {

		for (int i = 0; i < numSolvers; i++) {
			try{
				if (ignoredSolvers[i]) {
					System.out.println("ignoring solver " + probs[i].toString() + ": unsupported operation");
				} else {
					Boolean s = probs[i].solve();
					if (i > 0 && s != null && s) { // skip coral
						Env check = this.check(intVars, realVars, i);
						boolean s2 = (check.getResult() == Result.SAT) ? true : false;
						if (s2) {
							solutions[i] = s;
						} else {
							System.out
									.println("## Symlib of Coral does not agree with  " + i + " posted solution");
							solutions[i] = false;
						}
					} else {
						solutions[i] = (s == null) ? false : s;
					}
					// if (s == null) {
					// solutions[i] = false;
					// } else {
					// solutions[i] = s;
					// }
				}
			}
			catch(Exception e){
				solutions[i] = false;
				System.out.println("Solver " + i + " threw an exception");
				e.printStackTrace();
			}

			if (alwaysPrint) {
				System.out.println("Solver " + Integer.toString(i) + ": " + Boolean.toString(solutions[i]));
			}
		}

		// matrix update
		solvingDiff.update(solutions);

		if (!alwaysPrint) {
			boolean first = solutions[0];
			boolean print = false;
			for (int j = 1; j < numSolvers; j++) {
				if (solutions[j] != first) {
					print = true;
					break;
				}
			}
			if (print) {
				System.out.println("---- SOLVERS DISAGREE! ------");
				System.out.println(p.toString());
				for (int i = 0; i < numSolvers; i++) {
					System.out.println("   Solver " + Integer.toString(i) + ": "
							+ Boolean.toString(solutions[i]));
				}
			}
		}
		for (int i = 0; i < numSolvers; i++){
			if(solutions[i]){
				selected = i;
				break;
			}
		}

		return solutions[selected];
	}

	public static void dump(Search search) {
		solvingDiff.print();
		try {
			String targetName = search.getConfig().getStringArray("target")[0];
			String solverName = ProblemCompare.class.getSimpleName();
			String fileName = TablePrinter.TABLE_DIR + targetName + "." + solverName + ".ser";
			SolvingDiff.writeToFile(fileName, solvingDiff);
		} catch (IOException e) {
			throw new RuntimeException(TablePrinter.ERR_MSG);
		}
	}

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