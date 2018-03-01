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

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.PathCondition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.EXECUTENATIVE;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.vm.AnnotationInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

public class ConcreteExecutionListener extends PropertyListenerAdapter {

	Config config;
	public static boolean debug = false;
	long ret;
	Object resultAttr;
	String[] partitions;

	public enum type {
		INT, DOUBLE, FLOAT, BYTE,
		SHORT, LONG, BOOLEAN, CHAR
	}

	public ConcreteExecutionListener(Config conf, JPF jpf) {
		jpf.addPublisherExtension(ConsolePublisher.class, this);
		this.config = conf;
	}

	@Override
	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {

		Instruction lastInsn =  executedInstruction;
		MethodInfo mi = executedInstruction.getMethodInfo();
		if(lastInsn != null && lastInsn instanceof JVMInvokeInstruction) {
			boolean foundAnote = checkConcreteAnnotation(mi);
			if(foundAnote) {
				ThreadInfo ti = vm.getCurrentThread();
				StackFrame sf = ti.popAndGetModifiableTopFrame();
				FunctionExpression result =
					generateFunctionExpression(mi, (JVMInvokeInstruction)
													lastInsn, ti);
				checkReturnType(ti, mi, result);
				Instruction nextIns = sf.getPC().getNext();
			    vm.getCurrentThread().skipInstruction(nextIns);
			}
		}
	}


	private boolean checkConcreteAnnotation(MethodInfo mi) {
		AnnotationInfo[] ai = mi.getAnnotations();
		boolean retVal = false;
		if(ai == null || ai.length == 0)  return retVal;
		for(int aIndex = 0; aIndex < ai.length; aIndex++) {
			AnnotationInfo annotation = ai[aIndex];
			if(annotation.getName().equals
							("gov.nasa.jpf.symbc.Concrete")) {
				if(annotation.valueAsString().
									equalsIgnoreCase("true"))
					retVal = true;
				else
					retVal = false;
			} else if (annotation.getName().equals
					("gov.nasa.jpf.symbc.Partition"))	 {

				partitions = annotation.getValueAsStringArray();
//				if (SymbolicInstructionFactory.debugMode)
//					for(int i = 0; i < partitions.length; i++)
//						System.out.println("discovered partition "+partitions[i]);
			}
		}
		return retVal;
	}

	private FunctionExpression generateFunctionExpression(MethodInfo mi,
			JVMInvokeInstruction ivk, ThreadInfo ti){
		Object [] attrs = ivk.getArgumentAttrs(ti);
		Object [] values = ivk.getArgumentValues(ti);
		String [] types = mi.getArgumentTypeNames();

		assert (attrs != null);

		assert (attrs.length == values.length &&
						values.length == types.length);
		int size = attrs.length;

		Class<?>[] args_type = new Class<?> [size];
		Expression[] sym_args = new Expression[size];

		Map<String,Expression> expressionMap =
			new HashMap<String, Expression>();
		LocalVarInfo[] localVars = mi.getLocalVars();

		for(int argIndex = 0; argIndex < size; argIndex++) {
			Object attribute = attrs[argIndex];
			if(attribute == null) {
				sym_args[argIndex] = this.generateConstant(
								types[argIndex],
								values[argIndex]);
			} else {
				sym_args[argIndex] = (Expression) attribute;
				if(localVars.length > argIndex)
					expressionMap.put(localVars[argIndex].getName(),
						sym_args[argIndex]);


			}
			args_type[argIndex] = checkArgumentTypes(types[argIndex]);
		}

		ArrayList<PathCondition> conditions = Partition.
							createConditions(partitions, expressionMap);


		FunctionExpression result = new FunctionExpression(
				  mi.getClassName(),
				  mi.getName(), args_type, sym_args, conditions);

		return result;
	}


	private void checkReturnType(ThreadInfo ti, MethodInfo mi, Object resultAttr) {
		String retTypeName = mi.getReturnTypeName();
		StackFrame sf = ti.getModifiableTopFrame();
		sf.removeArguments(mi);
		if(retTypeName.equals("double") || retTypeName.equals("long")) {
			sf.pushLong(0);
			sf.setLongOperandAttr(resultAttr);
		} else {
			sf.push(0);
			sf.setOperandAttr(resultAttr);
		}
	}



	private Class<?> checkArgumentTypes(String typeVal) {
		if(typeVal.equals("int")) {
			return Integer.TYPE;
		} else if (typeVal.equals("double")) {
			return Double.TYPE;
		} else if (typeVal.equals("float")) {
			return Float.TYPE;
		} else if (typeVal.equals("long")) {
			return Long.TYPE;
		} else if (typeVal.equals("short")) {
			return Short.TYPE;
		}  else if (typeVal.equals("boolean")) {
			return Boolean.TYPE;
		} else {
			throw new RuntimeException("the type not handled :" + typeVal);
		}
	}

	private Expression generateConstant(String typeVal, Object value) {
		if(typeVal.equals("int")) {
			return new IntegerConstant(Integer.parseInt
					(value.toString()));
		} else if (typeVal.equals("double")) {
			return new RealConstant(Double.parseDouble
					(value.toString()));
		} else if (typeVal.equals("float")) {
			return new RealConstant(Float.parseFloat
					(value.toString()));
		} else if (typeVal.equals("long")) {
			return new IntegerConstant((int) Long.parseLong
					(value.toString()));
		} else if (typeVal.equals("short")) {
			return new IntegerConstant((int) Short.parseShort
					(value.toString()));
		} else if (typeVal.equals("boolean")) {
			if(value.toString().equals("true")) {
				return new IntegerConstant(1);
			} else {
				return new IntegerConstant(0);
			}
		} else {
			throw new RuntimeException("the type not handled :" + typeVal);
		}
	}

}