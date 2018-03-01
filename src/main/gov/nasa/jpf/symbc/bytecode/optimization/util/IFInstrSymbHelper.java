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

/**
 * 
 */
package gov.nasa.jpf.symbc.bytecode.optimization.util;


import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.jvm.bytecode.LCMP;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;

public class IFInstrSymbHelper {
	
	public static Instruction getNextInstructionAndSetPCChoice(ThreadInfo ti, 
															   LCMP instr, 
															   IntegerExpression sym_v1,
															   IntegerExpression sym_v2,
															   Comparator firstComparator,
															   Comparator secondComparator,
															   Comparator thirdComparator) {
		int conditionValue = -3; //bogus value
		if(!ti.isFirstStepInsn()) { // first time around
			PCChoiceGenerator prevPcGen;
			ChoiceGenerator<?> cg = ti.getVM().getChoiceGenerator();
			if(cg instanceof PCChoiceGenerator)
				prevPcGen = (PCChoiceGenerator)cg;
			else 
				prevPcGen = (PCChoiceGenerator)cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
		
			PathCondition pc;
			if(prevPcGen!=null)
				pc = prevPcGen.getCurrentPC();
			else
				pc = new PathCondition();
			
			PathCondition firstPC = pc.make_copy();
			PathCondition secPC = pc.make_copy();
			PathCondition thirdPC = pc.make_copy();
			
			long v1 = ti.getModifiableTopFrame().peekLong();
			long v2 = ti.getModifiableTopFrame().peekLong(2);
			
			if(sym_v1 != null){
				if(sym_v2 != null){ //both are symbolic values
					firstPC._addDet(firstComparator,sym_v2,sym_v1);
					secPC._addDet(secondComparator,sym_v1,sym_v2);
					thirdPC._addDet(thirdComparator,sym_v2,sym_v1);
				} else {
					firstPC._addDet(firstComparator,v2,sym_v1);
					secPC._addDet(secondComparator,sym_v1,v2);
					thirdPC._addDet(thirdComparator,v2,sym_v1);
				}
			} else {
				firstPC._addDet(firstComparator,sym_v2,v1);
				secPC._addDet(secondComparator,v1,sym_v2);
				thirdPC._addDet(thirdComparator,sym_v2,v1);
			}
			
			boolean firstSat = firstPC.simplify();
			boolean secSat = secPC.simplify();
			boolean thirdSat = thirdPC.simplify();
			
			if(firstSat) {
				if(secSat) {
					PCChoiceGenerator newPCChoice;
					if(thirdSat) {
						newPCChoice = new PCChoiceGenerator(3);
					} else {
						//LE (choice 0) == true, EQ (choice 1)== true
						newPCChoice = new PCChoiceGenerator(2);
					}
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else if(thirdSat) {
					//LE (choice 0) == true, GT (choice 2)== true
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(0, 2, 2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					prevPcGen.setCurrentPC(firstPC);
					conditionValue = -1;
				}
			} else if(secSat) {
				if(thirdSat) {
					//EQ (choice 1) == true, GT (choice 2)== true
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(1, 2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					conditionValue = 0;
				}
			} else if(thirdSat) {
				conditionValue = 1;
			} else {
				System.err.println("***********Warning: everything false");
				ti.getVM().getSystemState().setIgnored(true);
			}
			
		} else { //This branch will only be taken if there is a choice
			
			long v1 = ti.getModifiableTopFrame().peekLong();
			long v2 = ti.getModifiableTopFrame().peekLong(2);
			PathCondition pc;
			PCChoiceGenerator curCg = (PCChoiceGenerator)ti.getVM().getSystemState().getChoiceGenerator();
			
			PCChoiceGenerator prevCg = curCg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
			
			if(prevCg == null )
				pc = new PathCondition();
			else
				pc = ((PCChoiceGenerator)prevCg).getCurrentPC();
			
			conditionValue = ((PCChoiceGenerator) curCg).getNextChoice() -1;
			if (conditionValue == -1) {
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(firstComparator, sym_v2, sym_v1);
					} else
						pc._addDet(firstComparator, v2, sym_v1);
				} else
					pc._addDet(firstComparator, sym_v2, v1);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
			} else if (conditionValue == 0){
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(secondComparator, sym_v1, sym_v2);
					} else
						pc._addDet(secondComparator, sym_v1, v2);
				} else
					pc._addDet(secondComparator, v1, sym_v2);
					((PCChoiceGenerator) curCg).setCurrentPC(pc);
			} else {// 1
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(thirdComparator, sym_v2, sym_v1);
					} else
						pc._addDet(thirdComparator, v2, sym_v1);
				} else
					pc._addDet(thirdComparator, sym_v2, v1);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
			}
		}
		ti.getModifiableTopFrame().popLong();
		ti.getModifiableTopFrame().popLong();
		ti.getModifiableTopFrame().push(conditionValue, false);
		return instr.getNext(ti);
	}
	
	public static Instruction getNextInstructionAndSetPCChoiceFloat(ThreadInfo ti, 
																   Instruction instr, 
																   RealExpression sym_v1,
																   RealExpression sym_v2,
																   Comparator firstComparator,
																   Comparator secondComparator,
																   Comparator thirdComparator) {
		int conditionValue = -3; //bogus value
		if(!ti.isFirstStepInsn()) { // first time around
			PCChoiceGenerator prevPcGen;
			ChoiceGenerator<?> cg = ti.getVM().getChoiceGenerator();
			if(cg instanceof PCChoiceGenerator)
				prevPcGen = (PCChoiceGenerator)cg;
			else 
				prevPcGen = (PCChoiceGenerator)cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
		
			PathCondition pc;
			if(prevPcGen!=null)
				pc = prevPcGen.getCurrentPC();
			else
				pc = new PathCondition();
			
			PathCondition firstPC = pc.make_copy();
			PathCondition secPC = pc.make_copy();
			PathCondition thirdPC = pc.make_copy();
			
			float v1 = Types.intToFloat(ti.getModifiableTopFrame().peek());
			float v2 = Types.intToFloat(ti.getModifiableTopFrame().peek(1));
			
			if(sym_v1 != null){
				if(sym_v2 != null){ //both are symbolic values
					firstPC._addDet(firstComparator,sym_v2,sym_v1);
					secPC._addDet(secondComparator,sym_v1,sym_v2);
					thirdPC._addDet(thirdComparator,sym_v2,sym_v1);
				} else {
					firstPC._addDet(firstComparator,v2,sym_v1);
					secPC._addDet(secondComparator,sym_v1,v2);
					thirdPC._addDet(thirdComparator,v2,sym_v1);
				}
			} else {
				firstPC._addDet(firstComparator,sym_v2,v1);
				secPC._addDet(secondComparator,v1,sym_v2);
				thirdPC._addDet(thirdComparator,sym_v2,v1);
			}
			
			boolean firstSat = firstPC.simplify();
			boolean secSat = secPC.simplify();
			boolean thirdSat = thirdPC.simplify(); 
			
			if(firstSat) {
				if(secSat) {
					PCChoiceGenerator newPCChoice;
					if(thirdSat) {
						newPCChoice = new PCChoiceGenerator(3);
					} else {
						//LE (choice 0) == true, EQ (choice 1)== true
						newPCChoice = new PCChoiceGenerator(2);
					}
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else if(thirdSat) {
					//LE (choice 0) == true, GT (choice 2)== true
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(0, 2, 2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					prevPcGen.setCurrentPC(firstPC);
					conditionValue = -1;
				}
			} else if(secSat) {
				if(thirdSat) {
					//EQ (choice 1) == true, GT (choice 2)== true
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(1, 2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					conditionValue = 0;
				}
			} else if(thirdSat) {
				conditionValue = 1;
			} else {
				System.err.println("***********Warning: everything false");
				ti.getVM().getSystemState().setIgnored(true);
			}
		} else { //This branch will only be taken if there is a choice
			
			float v1 = Types.intToFloat(ti.getModifiableTopFrame().peek());
			float v2 = Types.intToFloat(ti.getModifiableTopFrame().peek(1));
			PathCondition pc;
			PCChoiceGenerator curCg = (PCChoiceGenerator)ti.getVM().getSystemState().getChoiceGenerator();
			
			PCChoiceGenerator prevCg = curCg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
			
			if(prevCg == null )
				pc = new PathCondition();
			else
				pc = prevCg.getCurrentPC();
			
			conditionValue = ((PCChoiceGenerator) curCg).getNextChoice() -1;
			if (conditionValue == -1) {
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(firstComparator, sym_v2, sym_v1);
					} else
						pc._addDet(firstComparator, v2, sym_v1);
				} else
					pc._addDet(firstComparator, sym_v2, v1);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
			} else if (conditionValue == 0){
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(secondComparator, sym_v1, sym_v2);
					} else
						pc._addDet(secondComparator, sym_v1, v2);
				} else
					pc._addDet(secondComparator, v1, sym_v2);
					((PCChoiceGenerator) curCg).setCurrentPC(pc);
			} else {// 1
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(thirdComparator, sym_v2, sym_v1);
					} else
						pc._addDet(thirdComparator, v2, sym_v1);
				} else
					pc._addDet(thirdComparator, sym_v2, v1);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
			}
		}
		ti.getModifiableTopFrame().pop();
		ti.getModifiableTopFrame().pop();
		ti.getModifiableTopFrame().push(conditionValue, false);
		return instr.getNext(ti);
		
	}
	
	public static Instruction getNextInstructionAndSetPCChoiceDouble(ThreadInfo ti, 
															   Instruction instr, 
															   RealExpression sym_v1,
															   RealExpression sym_v2,
															   Comparator firstComparator,
															   Comparator secondComparator,
															   Comparator thirdComparator) {
		int conditionValue = -3; //bogus value
		
		if(!ti.isFirstStepInsn()) { // first time around
			PCChoiceGenerator prevPcGen;
			ChoiceGenerator<?> cg = ti.getVM().getChoiceGenerator();
			if(cg instanceof PCChoiceGenerator)
				prevPcGen = (PCChoiceGenerator)cg;
			else 
				prevPcGen = (PCChoiceGenerator)cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
		
			PathCondition pc;
			if(prevPcGen!=null)
				pc = prevPcGen.getCurrentPC();
			else
				pc = new PathCondition();
			
			PathCondition firstPC = pc.make_copy();
			PathCondition secPC = pc.make_copy();
			PathCondition thirdPC = pc.make_copy();
			
			double v1 = Types.longToDouble(ti.getModifiableTopFrame().peekLong());
			double v2 = Types.longToDouble(ti.getModifiableTopFrame().peekLong(2));
			
			if(sym_v1 != null){
				if(sym_v2 != null){ //both are symbolic values
					firstPC._addDet(firstComparator,sym_v2,sym_v1);
					secPC._addDet(secondComparator,sym_v1,sym_v2);
					thirdPC._addDet(thirdComparator,sym_v2,sym_v1);
				} else {
					firstPC._addDet(firstComparator,v2,sym_v1);
					secPC._addDet(secondComparator,sym_v1,v2);
					thirdPC._addDet(thirdComparator,v2,sym_v1);
				}
			} else {
				firstPC._addDet(firstComparator,sym_v2,v1);
				secPC._addDet(secondComparator,v1,sym_v2);
				thirdPC._addDet(thirdComparator,sym_v2,v1);
			}
			
			boolean firstSat = firstPC.simplify();
			boolean secSat = secPC.simplify();
			boolean thirdSat = thirdPC.simplify();
			
			if(firstSat) {
				if(secSat) {
					PCChoiceGenerator newPCChoice;
					if(thirdSat) {
						newPCChoice = new PCChoiceGenerator(3);
					} else {
						//LE (choice 0) == true, EQ (choice 1)== true
						newPCChoice = new PCChoiceGenerator(2);
					}
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else if(thirdSat) {
					//LE (choice 0) == true, GT (choice 2)== true
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(0, 2, 2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					conditionValue = -1;
				}
			} else if(secSat) {
				if(thirdSat) {
					//EQ (choice 1) == true, GT (choice 2)== true
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(1, 2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					conditionValue = 0;
				}
			} else if(thirdSat) {
				conditionValue = 1;
			} else {
				System.err.println("***********Warning: everything false");
				ti.getVM().getSystemState().setIgnored(true);
			}
		} else { //This branch will only be taken if there is a choice
			
			double v1 = Types.longToDouble(ti.getModifiableTopFrame().peekLong());
			double v2 = Types.longToDouble(ti.getModifiableTopFrame().peekLong(2));
			
			PathCondition pc;
			PCChoiceGenerator curCg = (PCChoiceGenerator)ti.getVM().getSystemState().getChoiceGenerator();
			
			PCChoiceGenerator prevCg = curCg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
			
			if(prevCg == null )
				pc = new PathCondition();
			else
				pc = prevCg.getCurrentPC();
			
			conditionValue = ((PCChoiceGenerator) curCg).getNextChoice() -1;
			if (conditionValue == -1) {
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(firstComparator, sym_v2, sym_v1);
					} else
						pc._addDet(firstComparator, v2, sym_v1);
				} else
					pc._addDet(firstComparator, sym_v2, v1);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
			} else if (conditionValue == 0){
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(secondComparator, sym_v1, sym_v2);
					} else
						pc._addDet(secondComparator, sym_v1, v2);
				} else
					pc._addDet(secondComparator, v1, sym_v2);
					((PCChoiceGenerator) curCg).setCurrentPC(pc);
			} else {// 1
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(thirdComparator, sym_v2, sym_v1);
					} else
						pc._addDet(thirdComparator, v2, sym_v1);
				} else
					pc._addDet(thirdComparator, sym_v2, v1);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
			}
		}
		ti.getModifiableTopFrame().popLong();
		ti.getModifiableTopFrame().popLong();
		ti.getModifiableTopFrame().push(conditionValue, false);
		return instr.getNext(ti);
	}
	
	
	
	public static Instruction getNextInstructionAndSetPCChoice(ThreadInfo ti, 
															   IfInstruction instr, 
															   IntegerExpression sym_v,
															   Comparator trueComparator,
															   Comparator falseComparator) {
		
		//TODO: fix conditionValue
		if(!ti.isFirstStepInsn()) { // first time around
			PCChoiceGenerator prevPcGen;
			ChoiceGenerator<?> cg = ti.getVM().getChoiceGenerator();
			if(cg instanceof PCChoiceGenerator)
				prevPcGen = (PCChoiceGenerator)cg;
			else 
				prevPcGen = (PCChoiceGenerator)cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
		
			PathCondition pc;
			if(prevPcGen!=null)
				pc = prevPcGen.getCurrentPC();
			else
				pc = new PathCondition();
			
			PathCondition eqPC = pc.make_copy();
			PathCondition nePC = pc.make_copy();
			eqPC._addDet(trueComparator, sym_v, 0);
			nePC._addDet(falseComparator, sym_v, 0);
			
			boolean eqSat = eqPC.simplify();
			boolean neSat = nePC.simplify();
			
			if(eqSat) {
				if(neSat) {
					PCChoiceGenerator newPCChoice;
					newPCChoice = new PCChoiceGenerator(2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					ti.getModifiableTopFrame().pop();
					return instr.getTarget();
				}
			} else {
				ti.getModifiableTopFrame().pop();
				return instr.getNext(ti);
			}	
		} else {
			ti.getModifiableTopFrame().pop();
			PathCondition pc;
			PCChoiceGenerator curCg = (PCChoiceGenerator)ti.getVM().getSystemState().getChoiceGenerator();
			
			PCChoiceGenerator prevCg = curCg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
			
			if(prevCg == null )
				pc = new PathCondition();
			else
				pc = prevCg.getCurrentPC();
			boolean conditionValue = (Integer)curCg.getNextChoice()==1 ? true: false;
			if(conditionValue) {
				pc._addDet(trueComparator, sym_v, 0);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
				return instr.getTarget();
			} else {
				pc._addDet(falseComparator, sym_v, 0);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
				return instr.getNext(ti);
			}
		}	
	}
	
	public static Instruction getNextInstructionAndSetPCChoice(ThreadInfo ti, 
															   IfInstruction instr, 
															   IntegerExpression sym_v1, 
															   IntegerExpression sym_v2,
															   Comparator trueComparator,
															   Comparator falseComparator) {
		
		//TODO: fix conditionValue
		if(!ti.isFirstStepInsn()) { // first time around
			PCChoiceGenerator prevPcGen;
			ChoiceGenerator<?> cg = ti.getVM().getChoiceGenerator();
			if(cg instanceof PCChoiceGenerator)
				prevPcGen = (PCChoiceGenerator)cg;
			else 
				prevPcGen = (PCChoiceGenerator)cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
		
			PathCondition pc;
			if(prevPcGen!=null)
				pc = prevPcGen.getCurrentPC();
			else
				pc = new PathCondition();
			
			PathCondition eqPC = pc.make_copy();
			PathCondition nePC = pc.make_copy();
			
			int	v2 = ti.getModifiableTopFrame().peek();
			int	v1 = ti.getModifiableTopFrame().peek(1);
			
			if(sym_v1 != null){
				if(sym_v2 != null){ //both are symbolic values
					eqPC._addDet(trueComparator,sym_v1,sym_v2);
					nePC._addDet(falseComparator,sym_v1,sym_v2);
				} else {
					eqPC._addDet(trueComparator,sym_v1,v2);
					nePC._addDet(falseComparator,sym_v1,v2);
				}
			} else {
				eqPC._addDet(trueComparator, v1, sym_v2);
				nePC._addDet(falseComparator, v1, sym_v2);
			}

			boolean eqSat = eqPC.simplify();
			boolean neSat = nePC.simplify();
			
			if(eqSat) {
				if(neSat) {
					PCChoiceGenerator newPCChoice = new PCChoiceGenerator(2);
					newPCChoice.setOffset(instr.getPosition());
					newPCChoice.setMethodName(instr.getMethodInfo().getFullName());
					ti.getVM().getSystemState().setNextChoiceGenerator(newPCChoice);
					return instr;
				} else {
					ti.getModifiableTopFrame().pop();
					ti.getModifiableTopFrame().pop();
					return instr.getTarget();
				}
			} else {
				ti.getModifiableTopFrame().pop();
				ti.getModifiableTopFrame().pop();
				return instr.getNext(ti);
			}	
		} else { //This branch will only be taken if there is a choice
			
			int	v2 = ti.getModifiableTopFrame().pop();
			int	v1 = ti.getModifiableTopFrame().pop();
			PathCondition pc;
			PCChoiceGenerator curCg = (PCChoiceGenerator)ti.getVM().getSystemState().getChoiceGenerator();
			
			PCChoiceGenerator prevCg = curCg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
			
			if(prevCg == null )
				pc = new PathCondition();
			else
				pc = prevCg.getCurrentPC();
			
			boolean conditionValue = (Integer)curCg.getNextChoice()==1 ? true: false;
			if(conditionValue) {
				if(sym_v1 != null){
					if(sym_v2 != null){ //both are symbolic values
						pc._addDet(trueComparator,sym_v1,sym_v2);
					} else
						pc._addDet(trueComparator,sym_v1,v2);
				} else
					pc._addDet(trueComparator, v1, sym_v2);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
				return instr.getTarget();
			} else {
				if(sym_v1 != null){
					if (sym_v2 != null){ //both are symbolic values
						pc._addDet(falseComparator,sym_v1,sym_v2);
					} else
						pc._addDet(falseComparator,sym_v1,v2);
				} else
					pc._addDet(falseComparator, v1, sym_v2);
				((PCChoiceGenerator) curCg).setCurrentPC(pc);
				return instr.getNext(ti);
			}
		}		
	}
}
