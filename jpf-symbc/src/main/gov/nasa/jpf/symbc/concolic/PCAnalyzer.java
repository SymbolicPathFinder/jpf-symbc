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

package gov.nasa.jpf.symbc.concolic;

import java.util.ArrayList;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.*;

public class PCAnalyzer {

	// this one will hold the parts that are easy to solve
	PathCondition simplePC;
	// this is the part that contains functions/operations
	// that we cannot solve with our DPs and hence want to use
	// concrete values on
	PathCondition concolicPC;

	//static public int MAX_TRIES = 1;

	// extraPC encodes extra EQ constraints of the form x == solution, where solution is obtained by solving simplePC
	PathCondition extraPC; // spaghetti code; TODO this better

	ArrayList<PathCondition> partitionPCs; // collects conditions for partition heuristic; for now works only for one external function


	PathCondition getEQExtraConstraints() { return extraPC; }

	// first we split the PC into the easy and concolic parts
	// concolic refers to the parts that we cannot handle with a DP and instead use concrete values for.

	public boolean mixedIsSatisfiable(PathCondition working_pc,SymbolicConstraintsGeneral solver) {
		boolean result = false;
		splitPathCondition(working_pc);
		if (simplePC.solve() == false) return false;
		if(concolicPC == null || concolicPC.header == null) return true;

		createSimplifiedPC();
		result = solver.isSatisfiable(getSimplifiedPC());

		if (SymbolicInstructionFactory.debugMode) {
			if(result)
				System.out.println("combined PC satisfiable");
			else
				System.out.println("combined PC not satisfiable");
		}

		return(result);
	}

	public boolean isSatisfiable(PathCondition pc, SymbolicConstraintsGeneral solver) {
		//System.out.println("PC "+pc);
		if (pc == null || pc.header == null) return true;
		boolean result = false;
		PathCondition working_pc = pc.make_copy();
		Constraint working_pc_last = working_pc.last();

		// reset the values of the various helper PCs
		simplePC = null;
		concolicPC = null;
		extraPC = null;
		partitionPCs = null;

		int tries = 0;// heuristic to try different solutions up to some counter given by the user
		int MAX_TRIES = SymbolicInstructionFactory.MaxTries;

		if (SymbolicInstructionFactory.debugMode) {
			System.out.println("--------original PC------------"+tries);
			System.out.println("original pc " + pc);
			System.out.println("--- end printing original PC ---");
		}

		if(!SymbolicInstructionFactory.heuristicPartitionMode) {

			while(tries < MAX_TRIES) {

				result = mixedIsSatisfiable(working_pc, solver);

				if(result) {
					//solver.solve(getSimplifiedPC());
					return true;
				}

				if(!SymbolicInstructionFactory.heuristicRandomMode) {
					// Heuristic 1: systematically try different solutions
					// add to beginning of working_pc extra constraints obtained from negating the constraints in extraPC
					// assume for now we'll have only one EQ constraint;
					// i.e. we can only handle one external function with only one parameter


					if(extraPC == null || extraPC.header == null) return false;
					if (SymbolicInstructionFactory.debugMode) {
						System.out.println("--------extra PC------------"+tries);
						System.out.println("extra pc " + extraPC);
						System.out.println("--- end printing extra PC ---");
					}

					Constraint cRef = extraPC.header;
					int length = extraPC.count();
					while (cRef != null) {
						cRef.setComparator(Comparator.GT); // TODO: should be NE but choco can not handle it
						cRef=cRef.and;
					}
					working_pc.prependAllConjuncts(extraPC.header);
				}
				else {
					System.out.println("Heuristic random mode!");
				}
				tries ++;
				if (SymbolicInstructionFactory.debugMode) {
					System.out.println("--------working PC------------"+tries);
					System.out.println("working pc " + working_pc);
					System.out.println("--- end printing working PC ---");
				}
			}
		}
		else { // heuristicPartitionMode

			if (SymbolicInstructionFactory.debugMode)
				System.out.println("--------start Partition Heuristic------------"+tries);

				// Heuristic 3: systematically try different solutions in the PC attached to the function expression
				// add to beginning of working_pc extra constraints obtained from negating the constraints in extraPC
				// assume for now we'll have only one external function that has associated a set of partitions;

			//if(partitionPCs == null) return false; // we can not progress because we have no partitions to choose from

			    result = mixedIsSatisfiable(working_pc, solver);

				if(result)
					//solver.solve(getSimplifiedPC());
					return true;


				if(partitionPCs == null) {
					System.out.println("Partition PC is null");
					return false; // we can not progress because we have no partitions to choose from
				}


				// otherwise, try to use the partitions to search for solutions and repeat
				//Constraint old_header = working_pc.header;
				//working_pc = pc.make_copy();

				for(int i = 0; i < partitionPCs.size(); i++) {

					PathCondition partitionPC = partitionPCs.get(i);
					System.out.println("partitionPC "+partitionPC);
					// the idea is that the working pc is different every time.
					//working_pc.header = old_header;


//					if (SymbolicInstructionFactory.debugMode) {
//						System.out.println("--------Partition Heuristic working PC------------"+tries);
//						System.out.println("working pc " + working_pc);
//						System.out.println("partition pc " + partitionPC);
//						System.out.println("--- end printing Partition Heuristic working PC ---");
//					}
					//working_pc.prependAllConjuncts(partitionPC.header);
					working_pc.appendAllConjuncts(partitionPC.header);

					if (SymbolicInstructionFactory.debugMode) {
						System.out.println("--------Partition Heuristic working PC------------"+tries);
						System.out.println("working pc " + working_pc);
						System.out.println("--- end printing Partition Heuristic working PC ---");
					}

					result = mixedIsSatisfiable(working_pc, solver);

					if(working_pc_last!=null)
						working_pc_last.and = null; // remove the conjuncts added from the partitions

					if(result)
						//solver.solve(getSimplifiedPC());
						return true;


				}
		}
		assert !result;
		return result;
	}

	// called only for satisfiable pc: could be simplified
	// not in synch with the heuristics
	public boolean solve(PathCondition pc, SymbolicConstraintsGeneral solver) {
		if (pc == null || pc.header == null) return true;
			splitPathCondition(pc);
			simplePC.solve();
			if(concolicPC == null || concolicPC.header == null) return true;
			createSimplifiedPC();
			return solver.solve(getSimplifiedPC());
	}

	/*
	 * Walks the PC and splits it into simplePC and concolicPC
	 */
	public void splitPathCondition(PathCondition pc) {
		PathCondition newPC = pc.make_copy();
		Constraint cRef = newPC.header;
		simplePC = new PathCondition();
		concolicPC = new PathCondition();

		while (cRef != null) {
			if (cRef instanceof RealConstraint) {
				if (isComplex((RealConstraint)cRef))
				// this will be the only one that goes to concolicPC for now
					concolicPC.prependUnlessRepeated(new RealConstraint((RealConstraint)cRef));
				else
					simplePC.prependUnlessRepeated(new RealConstraint((RealConstraint)cRef));
			} else if (cRef instanceof LinearIntegerConstraint) {
				simplePC.prependUnlessRepeated(new LinearIntegerConstraint((LinearIntegerConstraint)cRef));
			} else if (cRef instanceof MixedConstraint) {
				simplePC.prependUnlessRepeated(new MixedConstraint((MixedConstraint)cRef));
			} else if (cRef instanceof LogicalORLinearIntegerConstraints) {
				simplePC.prependUnlessRepeated(new LogicalORLinearIntegerConstraints(((LogicalORLinearIntegerConstraints)cRef).getList()));
			} else if (cRef instanceof NonLinearIntegerConstraint){
				concolicPC.prependUnlessRepeated(new NonLinearIntegerConstraint((NonLinearIntegerConstraint)cRef));
			} else	{
				throw new RuntimeException("## Error: Constraint not handled " + cRef);
			}
			cRef = cRef.and;
		}
		if (SymbolicInstructionFactory.debugMode) {
			System.out.println("--------begin after splitting------------");
			System.out.println("originalPC " + pc);
			System.out.println("concolicPC " + concolicPC);
			System.out.println("simplePC " + simplePC);
			System.out.println("--------end after splitting------------");
		}
	}

	boolean isComplex(RealExpression eRef) {
		if (eRef instanceof SymbolicReal || eRef instanceof RealConstant)
			return false;

		if(eRef instanceof MathRealExpression || eRef instanceof FunctionExpression)
			return true;

		return isComplex(((BinaryRealExpression)eRef).getLeft()) ||  isComplex(((BinaryRealExpression)eRef).getRight());
	}

    boolean isComplex(RealConstraint cRef) {
    	return isComplex(cRef.getLeft()) ||  isComplex(cRef.getRight());
    }


	// for now assume only real expressions
	Constraint eqConcolicConstraint(Expression eRef) {
		if(eRef instanceof MathRealExpression) {
			MathFunction funRef;
			RealExpression	e_arg1Ref;
			RealExpression	e_arg2Ref;

			funRef = ((MathRealExpression)eRef).op;
			e_arg1Ref = ((MathRealExpression)eRef).arg1;
			e_arg2Ref = ((MathRealExpression)eRef).arg2;

			switch(funRef){
			case SIN:
			case COS:
			case EXP:
			case ASIN:
			case ACOS:
			case ATAN:
			case LOG:
			case TAN:
			case SQRT:return new RealConstraint(e_arg1Ref, Comparator.EQ, new RealConstant(e_arg1Ref.solution()));
			case POW:
			case ATAN2: {
				RealConstraint c1 = new RealConstraint(e_arg1Ref, Comparator.EQ, new RealConstant(e_arg1Ref.solution()));
				RealConstraint c2 = new RealConstraint(e_arg2Ref, Comparator.EQ, new RealConstant(e_arg2Ref.solution()));
				c1.and = c2;
				return c1;
			}
			default:
				throw new RuntimeException("## Error: Expression " + eRef);
			}
		}
		else if (eRef instanceof FunctionExpression) {
			Expression [] sym_args = ((FunctionExpression)eRef).sym_args;
			assert(sym_args != null && sym_args.length > 0);
			RealExpression e = (RealExpression)sym_args[0];// for now assume only real expressions; TODO the integer expressions
			RealConstraint c = new RealConstraint(e, Comparator.EQ, new RealConstant(e.solution()));
			for(int i=1; i<sym_args.length; i++) {
					RealExpression e2 = (RealExpression)sym_args[i];
					RealConstraint c2 = new RealConstraint(e2, Comparator.EQ, new RealConstant(e2.solution()));
					c2.and = c;
					c = c2;
			}
			return c;
		}
		else if (eRef instanceof BinaryNonLinearIntegerExpression) {

			IntegerExpression	e_arg1Ref;
			IntegerExpression	e_arg2Ref;

			e_arg1Ref = ((BinaryNonLinearIntegerExpression)eRef).left;
			e_arg2Ref = ((BinaryNonLinearIntegerExpression)eRef).right;
			LinearIntegerConstraint c1 = new LinearIntegerConstraint(e_arg1Ref, Comparator.EQ, new IntegerConstant(e_arg1Ref.solution()));
			LinearIntegerConstraint c2 = new LinearIntegerConstraint(e_arg2Ref, Comparator.EQ, new IntegerConstant(e_arg2Ref.solution()));
			c1.and = c2;
			return c1;
		}
		throw new RuntimeException("## Error: Expression " + eRef);
	}



	Expression getExpression(Expression eRef) {
		assert eRef != null;
		//assert !(eRef instanceof RealConstant);

		if (eRef instanceof SymbolicReal || eRef instanceof RealConstant) {
			return eRef;
		}
		if (eRef instanceof SymbolicInteger || eRef instanceof IntegerConstant) {
			return eRef;
		}

		if(eRef instanceof BinaryRealExpression) {
			Operator    opRef = ((BinaryRealExpression)eRef).getOp();
			RealExpression	e_leftRef = ((BinaryRealExpression)eRef).getLeft();
			RealExpression	e_rightRef = ((BinaryRealExpression)eRef).getRight();

			return new BinaryRealExpression((RealExpression)getExpression(e_leftRef),opRef,(RealExpression)getExpression(e_rightRef));
		}


		if(eRef instanceof MathRealExpression || eRef instanceof FunctionExpression) {
			extraPC.prependUnlessRepeated(eqConcolicConstraint(eRef));
			if(eRef instanceof FunctionExpression && ((FunctionExpression)eRef).conditions !=null) {
				//if(SymbolicInstructionFactory.debugMode)
					System.out.println("found partitions for "+((FunctionExpression)eRef).method_name);
				if(partitionPCs==null) {// be careful because we can only handle one function for now
				   partitionPCs =  ((FunctionExpression)eRef).conditions;
				}
			}
			return new RealConstant(((RealExpression)eRef).solution());
		}

		if(eRef instanceof BinaryNonLinearIntegerExpression) {
			extraPC.prependUnlessRepeated(eqConcolicConstraint(eRef));
			return new IntegerConstant(((BinaryNonLinearIntegerExpression)eRef).solution());
		}

		throw new RuntimeException("## Error: Expression " + eRef);
	}


//	RealConstraint traverseRealConstraint(RealConstraint cRef) {
//		Comparator c_compRef = cRef.getComparator();
//		RealExpression c_leftRef = (RealExpression)cRef.getLeft();
//		RealExpression c_rightRef = (RealExpression)cRef.getRight();
//
//		return new RealConstraint(getExpression(c_leftRef),c_compRef,getExpression(c_rightRef));
//	}
	Constraint traverseConstraint(Constraint cRef) {
		Comparator c_compRef = cRef.getComparator();
		Expression c_leftRef = cRef.getLeft();
		Expression c_rightRef = cRef.getRight();

		//return new Constraint(getExpression(c_leftRef),c_compRef,getExpression(c_rightRef));
		if(cRef instanceof RealConstraint)
			return new RealConstraint((RealExpression)(getExpression(c_leftRef)),c_compRef,(RealExpression)(getExpression(c_rightRef)));
		if(cRef instanceof NonLinearIntegerConstraint)
			return new LinearIntegerConstraint((IntegerExpression)(getExpression(c_leftRef)),c_compRef,(IntegerExpression)(getExpression(c_rightRef)));
		throw new RuntimeException("## Error: Constraint " + cRef);


	}
	public void createSimplifiedPC() {
		// first solve the simplePC and then use the results to update concolicPC

		if (SymbolicInstructionFactory.debugMode) {
			System.out.println("........................START SOLVING");
			System.out.println("--------------------");
			System.out.println("simplePC " + simplePC);
			System.out.println("--------------------");
		}

		// now replace all math functions in concolicPC
		// with their execution results with simplePC arguments

		//PathCondition simplifiedPC = new PathCondition();
		Constraint cRef = concolicPC.header;

		extraPC = new PathCondition();
		while (cRef != null) {
			simplePC.prependUnlessRepeated(traverseConstraint(cRef));
			cRef = (RealConstraint)cRef.and;
		}
		if(SymbolicInstructionFactory.debugMode) System.out.println("new PC " + simplePC);
		if(extraPC.header!=null) {
			if(SymbolicInstructionFactory.debugMode) System.out.println("extraPC constraints" + extraPC);
			simplePC.appendAllConjuncts(extraPC.header);
		}

		if(SymbolicInstructionFactory.debugMode){
			if (true /*SymbolicInstructionFactory.debugMode*/) {
				System.out.println("--------------------");
				System.out.println("before solving combined PC " + simplePC);
				System.out.println("--------------------");
			}

		simplePC.flagSolved = false;

//		if (true /*SymbolicInstructionFactory.debugMode*/) {
//			System.out.println("--------------------");
//			System.out.println("simplifiedPC " + simplePC);
//			System.out.println("--------------------");
//		}
		}

	}

	public PathCondition getSimplifiedPC() {
		return simplePC;
	}


}
