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

//TODO: needs to be simplified; not to use string representation

//
//Copyright (C) 2007 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
package gov.nasa.jpf.symbc.heap;

// does not work well for static methods:summary not printed for errors
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.DoubleFieldInfo;
import gov.nasa.jpf.vm.DynamicElementInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Fields;
import gov.nasa.jpf.vm.FloatFieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.IntegerFieldInfo;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.VM;

import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.LongFieldInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ReferenceFieldInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.SystemState;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;
import gov.nasa.jpf.jvm.bytecode.ARETURN;
import gov.nasa.jpf.jvm.bytecode.IRETURN;

import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.bytecode.INVOKESTATIC;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.util.Pair;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Vector;


public class HeapSymbolicListener extends PropertyListenerAdapter implements PublisherExtension {



	private Map<String,MethodSummary> allSummaries;
	private String currentMethodName = "";
	private int refDepth = -1;


	// probably we do not need this!
	private Map<Integer, SymbolicInteger> nameMap =
											new HashMap<Integer,SymbolicInteger>();

	// what are these fields?
	private Set<String> definedFields = new HashSet<String>();

	public HeapSymbolicListener(Config conf, JPF jpf) {
		jpf.addPublisherExtension(ConsolePublisher.class, this);
		allSummaries = new HashMap<String, MethodSummary>();
		System.out.println("---->Heap Listener");

		// why is refDepth necessary?
		if (conf.containsKey("symbolic.refDepth"))
			refDepth = conf.getInt("symbolic.refDepth");
	}

	//Writes the method summaries to a file for use in another application
//	private void writeTable(){
//	  try {
//	        BufferedWriter out = new BufferedWriter(new FileWriter("outFile.txt"));
//		    Iterator it = allSummaries.entrySet().iterator();
//		    String line = "";
//		    while (it.hasNext()){
//		    	Map.Entry me = (Map.Entry)it.next();
//		    	String methodName = (String)me.getKey();
//		    	MethodSummary ms = (MethodSummary)me.getValue();
//		    	line = "METHOD: " + methodName + "," +
//		    		ms.getMethodName() + "(" + ms.getArgValues() + ")," +
//		    		ms.getMethodName() + "(" + ms.getSymValues() + ")";
//		    	out.write(line);
//		    	out.newLine();
//		    	Vector<Pair> pathConditions = ms.getPathConditions();
//				  if (pathConditions.size() > 0){
//					  Iterator it2 = pathConditions.iterator();
//					  while(it2.hasNext()){
//						  Pair pcPair = (Pair)it2.next();
//						  String pc = (String)pcPair.a;
//						  String errorMessage = (String)pcPair.b;
//						  line = pc;
//						  if (!errorMessage.equalsIgnoreCase(""))
//							  line = line + "$" + errorMessage;
//						  out.write(line);
//						  out.newLine();
//					  }
//				  }
//		    }
//	        out.close();
//	    } catch (Exception e) {
//	    }
//	}

	/*
	 * Recursive method to "dereference" an object and collect their values
	 * for use in the effects/result constraint
	 */

	Set<Integer> seenSet;
	int currentDepth=0;

	private void expandReferenceObject(PathCondition pc,ThreadInfo ti,
										ClassInfo ci,  int objNum){

		if ((currentDepth<=refDepth || refDepth == -1) &&
					!seenSet.contains(new Integer(objNum))){
			seenSet.add(new Integer(objNum));
			currentDepth++;
			String name = "";
			FieldInfo[] fields = ci.getDeclaredInstanceFields();
			ElementInfo ei = ti.getElementInfo(objNum);
			Integer ref = new Integer(objNum);
			if (null != ei && fields.length >0){
				for (int i = 0; i < fields.length; i++) {
					if (!fields[i].getName().contains("this")){
						SymbolicInteger temp = nameMap.get(ref);
						String fullType = fields[i].getType();
						String type = "";
						// C: why is this done???
					    if (fullType.contains("$"))
						  type = fullType.substring(fullType.indexOf('$')+1);
					    else
						  type = fullType.substring(fullType.lastIndexOf('.')+1);
						if (null != temp)
							name = nameMap.get(ref) + "." + type + ":" + fields[i].getName();
						else{ //this case is still not quite right
							name = ci.getName();
						    name = name.substring(name.lastIndexOf('.')+1) + ":#" + objNum + "." + fields[i].getName();
						}
						if (!definedFields.contains(name)){
							definedFields.add(name);
							Object attr = ei.getFieldAttr(fields[i]);
							if (fields[i] instanceof IntegerFieldInfo ||
														fields[i] instanceof LongFieldInfo) {
								IntegerExpression symField = new SymbolicInteger(name);
								if (null != attr)
									pc._addDet(Comparator.EQ, symField, (IntegerExpression)attr);
								else{
									int val;
									if (fields[i] instanceof IntegerFieldInfo)
										val = ei.getFields().getIntValue(i);
									else  //WARNING: downcasting to an int
										val = (int)ei.getFields().getLongValue(i);
									pc._addDet(Comparator.EQ, symField, new IntegerConstant(val));
								}
							} else if (fields[i] instanceof FloatFieldInfo ||
										fields[i] instanceof DoubleFieldInfo) {
								RealExpression symField = new SymbolicReal(name);
								if (null != attr)
									pc._addDet(Comparator.EQ, symField, (RealExpression)attr);
								else{
									double val;
									if (fields[i] instanceof FloatFieldInfo)
										val = ei.getFields().getFloatValue(i);
									else
										val = ei.getFields().getDoubleValue(i);
									pc._addDet(Comparator.EQ, symField, new RealConstant(val));
								}
							}else if (fields[i] instanceof ReferenceFieldInfo){
								IntegerExpression symField= new SymbolicInteger(name);
								Fields f = ei.getFields();
								Object val = f.getFieldAttr(i);
								int objIndex = f.getReferenceValue(i);
								if (null == val){
									IntegerExpression exp = null;
									if (objIndex == MJIEnv.NULL){
										exp = new IntegerConstant(objIndex);
										pc._addDet(Comparator.EQ, symField, exp);
									}else{
										exp = nameMap.get(new Integer(objIndex));
										if (null == exp)
											exp = new IntegerConstant(objIndex);
										pc._addDet(Comparator.EQ, symField, exp);
										if (objIndex != objNum && !seenSet.contains(objIndex) && objIndex != MJIEnv.NULL)
											expandReferenceObject(pc,ti,ci,objIndex);
									}
								}else{
									//pc._addDet(Comparator.EQ, symField, new IntegerConstant(objIndex));
									pc._addDet(Comparator.EQ, symField, (SymbolicInteger)val);
									if (objIndex != objNum && !seenSet.contains(objIndex) && objIndex != MJIEnv.NULL)
										expandReferenceObject(pc,ti,ci,objIndex);
								}
							}
						}
					}
				}
			}
			FieldInfo[] staticFields = ci.getDeclaredStaticFields();
			if (staticFields.length > 0 ) {
				for (int i = 0; i < staticFields.length; i++) {
					String type = "";
					SymbolicInteger tmp = nameMap.get(ref);
					if (null != tmp)
						type = nameMap.get(ref).toString();
					else{
						type = ci.getName();
					    type = name.substring(name.lastIndexOf('.')+1) ;
					}
					//strip the instance info
					if (type.contains(":"))
						type = type.substring(0,type.lastIndexOf(':'));
					name = type + "." + staticFields[i].getName();
					if (!definedFields.contains(name)){
						definedFields.add(name);
						Object attr = ci.getStaticElementInfo().getElementAttr(i);
						if (staticFields[i] instanceof IntegerFieldInfo ||
								staticFields[i] instanceof LongFieldInfo) {
							IntegerExpression symStatic = new SymbolicInteger(name);
							if (null != attr)
								pc._addDet(Comparator.EQ, symStatic, (IntegerExpression)attr);
							else{
								int val;
								if (staticFields[i] instanceof IntegerFieldInfo){
									val = ci.getStaticElementInfo().getIntField(staticFields[i]);
								}else  //WARNING: downcasting to an int
									val = (int)ci.getStaticElementInfo().getLongField(staticFields[i]);;
								//System.out.println("intVal: " + val);
								pc._addDet(Comparator.EQ, symStatic, new IntegerConstant(val));
							}
						} else if (staticFields[i] instanceof FloatFieldInfo
								|| staticFields[i] instanceof DoubleFieldInfo) {
							RealExpression symStatic = new SymbolicReal(name);
							if (null != attr)
								pc._addDet(Comparator.EQ, symStatic, (RealExpression)attr);
							else{
								double val;
								if (fields[i] instanceof FloatFieldInfo)
									val = ci.getStaticElementInfo().getFloatField(staticFields[i]);
								else
									val = ci.getStaticElementInfo().getDoubleField(staticFields[i]);;
								pc._addDet(Comparator.EQ, symStatic, new RealConstant(val));
							}
						}else if (staticFields[i] instanceof ReferenceFieldInfo){
							IntegerExpression symStatic = new SymbolicInteger(name);
							if (null != attr){
								pc._addDet(Comparator.EQ, symStatic, (IntegerExpression)attr);
							}else{
								ReferenceFieldInfo rfi = (ReferenceFieldInfo)staticFields[i];
								Integer objIndex = ci.getStaticElementInfo().getReferenceField(rfi);
								IntegerExpression exp = null;
								if (objIndex == MJIEnv.NULL){
									exp = new IntegerConstant(objIndex);
									pc._addDet(Comparator.EQ, symStatic,exp);
								}else{
									exp = nameMap.get(new Integer(objIndex));
									if (null == exp){
										String nm = ci.getName();
									    nm = name.substring(name.lastIndexOf('.')+1) + "@" + objNum ;
										exp = new SymbolicInteger(nm);
									}
									pc._addDet(Comparator.EQ, symStatic,exp);
									if (objIndex != objNum && !seenSet.contains(objIndex))
											expandReferenceObject(pc, ti, ci, objNum);
								}
							}
						}
					}
				}
			}
		}
	}

	/*
	 * Add the values (symbolic or concrete) of instance and static fields to the
	 * effects/result
	 * use refDepth configuration value to determine how far to "unwind" -- why is this necessary?
	 * object references
	 */
	private void getFieldValues(PathCondition returnPC, ThreadInfo ti,
										MethodInfo mi, Instruction insn){
		ClassInfo ci = mi.getClassInfo();
		JVMReturnInstruction ret = (JVMReturnInstruction)insn;
		StackFrame sf = ret.getReturnFrame();
		int thisRef = sf.getThis();

		// C: why is this string manipulation necessary?
		String name = sf.getClassName() + ":#" + thisRef;
		  if (name.contains("$"))
			  name = name.substring(name.indexOf('$')+1);
		  else
			  name = name.substring(name.lastIndexOf('.')+1);
		  String tmpName = name.substring(0,name.lastIndexOf('#')-1) + ":this";
		  returnPC._addDet(Comparator.EQ, new SymbolicInteger(tmpName),
				  new SymbolicInteger(name));
		seenSet = new HashSet<Integer>();
		definedFields = new HashSet<String>();

		nameMap.put(new Integer(thisRef), new SymbolicInteger(name)); // why is this necessary

		// adds constraints representing this

		expandReferenceObject(returnPC, ti, ci, thisRef);
		if (insn instanceof ARETURN){
			ARETURN areturn = (ARETURN)insn;
			int returnValue = areturn.getReturnValue();
			if (returnValue != thisRef)
				// adds constraints representing the return values
				expandReferenceObject(returnPC, ti, ci, returnValue);
		}
	}

	//not yet tested
	@Override
	public void propertyViolated (Search search){
		//System.out.println("--------->property violated");
		VM vm = search.getVM();
		HeapChoiceGenerator heapCG = vm.getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);
		PCChoiceGenerator pcCG = vm.getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
		PathCondition pc = (pcCG==null ? null : pcCG.getCurrentPC());
		PathCondition heapPC = (heapCG==null ? null : heapCG.getCurrentPCheap());
		
		String error = search.getLastError().getDetails();
		error = "\"" + error.substring(0,error.indexOf("\n")) + "...\"";
		PathCondition result = new PathCondition();
		nameMap = new HashMap<Integer,SymbolicInteger>();
		if (null != heapCG){
			SymbolicInputHeap symInputHeap =
			((HeapChoiceGenerator)heapCG).getCurrentSymInputHeap();
			HeapNode node = symInputHeap.header;
			while (null != node){
				nameMap.put(new Integer(node.getIndex()), node.getSymbolic());
				node = node.getNext();
			}
		}
		//getFieldValues(result,vm.getLastThreadInfo(),vm.getLastMethodInfo(), vm.getNextInstruction());
		IntegerExpression sym_err = new SymbolicInteger("ERROR");
		IntegerExpression sym_value = new SymbolicInteger(error);
		result._addDet(Comparator.EQ, sym_err, sym_value);
		//solve the path condition, then print it
		if(pc!=null) {
			pc.solve();
			String pcString =  pc.stringPC();
			Pair<String,String> pcPair = new Pair<String,String>(pcString,error);//(pc.toString(),error);
			//String methodName = vm.getLastInstruction().getMethodInfo().getName();
			MethodSummary methodSummary = allSummaries.get(currentMethodName);
			methodSummary.addPathCondition(pcPair);
			methodSummary.addHeapPC(String.valueOf(heapPC));
			allSummaries.put(currentMethodName,methodSummary);
		}
		System.out.println("Property Violated: ");
		System.out.println("Numeric PC is "+pc);
		System.out.println("Heap PC is "+heapPC);
		System.out.println("result is  "+result);
		System.out.println("****************************");
	}


	@Override
	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {

		if (!vm.getSystemState().isIgnored()) {
			Instruction insn = executedInstruction;
			SystemState ss = vm.getSystemState();
			ThreadInfo ti = currentThread;
			Config conf = vm.getConfig();

			if (insn instanceof JVMInvokeInstruction) {
				JVMInvokeInstruction md = (JVMInvokeInstruction) insn;
				String methodName = md.getInvokedMethodName();
				int numberOfArgs = md.getArgumentValues(ti).length;

				MethodInfo mi = md.getInvokedMethod();
				ClassInfo ci = mi.getClassInfo();
				String className = ci.getName();

				 StackFrame sf = ti.getTopFrame();
                 String shortName = methodName;
                 String longName = mi.getLongName();
                 if (methodName.contains("("))
                         shortName = methodName.substring(0,methodName.indexOf("("));

                 if(!mi.equals(sf.getMethodInfo()))
                         return;

				if ((BytecodeUtils.isClassSymbolic(conf, className, mi, methodName))
						|| BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null)){


					MethodSummary methodSummary = new MethodSummary();
					methodSummary.setMethodName(shortName);
					Object [] argValues = md.getArgumentValues(ti);

					String argValuesStr = "";
					for (int i=0; i<argValues.length; i++){
						argValuesStr = argValuesStr + argValues[i];
						if ((i+1) < argValues.length)
							argValuesStr = argValuesStr + ",";
					}
					methodSummary.setArgValues(argValuesStr);

					 byte [] argTypes = mi.getArgumentTypes();
                     String argTypesStr = "";
                     for (int i=0; i<argTypes.length; i++){
                             argTypesStr = argTypesStr + argTypes[i];
                             if ((i+1) < argTypes.length)
                                     argTypesStr = argTypesStr + ",";
                     }
                     methodSummary.setArgTypes(argTypesStr);



					//get the symbolic values (changed from constructing them here)
					String symValuesStr = "";
					String symVarNameStr = "";


					String[] names = null;//mi.getLocalVariableNames();
					LocalVarInfo[] argsInfo = mi.getArgumentLocalVars();

					int sfIndex = 1;//do not consider implicit param "this"
					int namesIndex=1;

					boolean usingTypes = false;
					//if debug option was not used when compiling the class,
					//then we do not have names of the locals and need to
					//use a different naming scheme
					if (argsInfo != null){
						//use local names
						if (md instanceof INVOKESTATIC){
							sfIndex=0; // no "this" for static
                            namesIndex =0;
						}
					}else{
						//use argument types for names (plus a unique index number)
						names = mi.getArgumentTypeNames();
						namesIndex = 0; //argument types does not contain "this"
						if (md instanceof INVOKESTATIC)
							sfIndex = 1;
						usingTypes = true;
					}
// TODO: fix names
					for (int i=0; i< numberOfArgs; i++){
						Expression expLocal = (Expression)sf.getLocalAttr(sfIndex);
						if (expLocal != null){ // symbolic
							symVarNameStr = expLocal.toString();

						}else{
								if (usingTypes)
									symVarNameStr = names[namesIndex] + "_" + namesIndex + "_CONCRETE";
									//symVarNameStr = "CONCRETE";
								else
									symVarNameStr = argsInfo[namesIndex].getName() + "_CONCRETE";
									//symVarNameStr = "CONCRETE";
						}
						symValuesStr = symValuesStr + symVarNameStr + ",";
						namesIndex++;
						sfIndex++;
						 if(argTypes[i] == Types.T_LONG || argTypes[i] == Types.T_DOUBLE)
                             sfIndex++;
					}
					if (symValuesStr.endsWith(",")) {
						symValuesStr = symValuesStr.substring(0,symValuesStr.length()-1);
					}
					methodSummary.setSymValues(symValuesStr);

					currentMethodName = longName;
					allSummaries.put(longName,methodSummary);
				}
			}else if (insn instanceof JVMReturnInstruction){
				MethodInfo mi = insn.getMethodInfo();
				ClassInfo ci = mi.getClassInfo();
				if (null != ci){
					String className = ci.getName();
					String methodName = mi.getName();
					String longName = mi.getLongName();
					int numberOfArgs = mi.getNumberOfArguments();
					//int numberOfArgs = mi.getArgumentsSize() - 1;
					//neha: changed invoked method name to full name
					if (((BytecodeUtils.isClassSymbolic(conf, className, mi, methodName))
							|| BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null))){



						HeapChoiceGenerator heapCG = vm.getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);
						PCChoiceGenerator pcCG = vm.getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
						PathCondition pc = (pcCG==null ? null : pcCG.getCurrentPC());
						PathCondition heapPC = (heapCG==null ? null : heapCG.getCurrentPCheap());

						if(pc!=null) {
							pc.solve(); //we only solve the pc
							PathCondition result = new PathCondition();
							//after the following statement is executed, the pc loses its solution
							IntegerExpression sym_result = new SymbolicInteger("RETURN");
							nameMap = new HashMap<Integer,SymbolicInteger>();
							if (null != heapCG){
								SymbolicInputHeap symInputHeap =
								 ((HeapChoiceGenerator)heapCG).getCurrentSymInputHeap();
								HeapNode node = symInputHeap.header;
								while (null != node){
									// why is this map necessary?
									nameMap.put(new Integer(node.getIndex()), node.getSymbolic());
									node = node.getNext();
								}
							}
							getFieldValues(result,ti,mi, insn);
							String pcString = pc.stringPC();

							Pair<String,String> pcPair = null;

/* TODO: to review this part
							String returnString = "";
							if (insn instanceof IRETURN){
								IRETURN ireturn = (IRETURN)insn;
								int returnValue = ireturn.getReturnValue();
								IntegerExpression returnAttr = (IntegerExpression) ireturn.getReturnAttr(ti);
								if (returnAttr != null){
										returnString = "Return Value: " + String.valueOf(returnAttr.toString());
								}else // concrete
									returnString = "Return Value: " + String.valueOf(returnValue);
								if (returnAttr != null){
									result._addDet(Comparator.EQ, sym_result, returnAttr);
								}else{ // concrete
									result._addDet(Comparator.EQ, sym_result, new IntegerConstant(returnValue));
								}
							}else if (insn instanceof ARETURN){
								ARETURN areturn = (ARETURN)insn;
								IntegerExpression returnAttr = (IntegerExpression) areturn.getReturnAttr(ti);
								if (returnAttr != null)
									returnString = "Return Value: " + String.valueOf(returnAttr.solution());
								else {// concrete
									Object val = areturn.getReturnValue(ti);
									String tmp = val.toString();
									System.out.println("tmp "+tmp);
									tmp = tmp.substring(tmp.indexOf('@')+1);
									System.out.println("tmp "+tmp);
									Integer index = new Integer(Integer.parseInt(tmp));
									if (nameMap.containsKey(index))
										returnString = "Return Value: " + nameMap.get(index);
									else
										returnString = "Return Value: " + String.valueOf(val.toString());
								}
								if (returnAttr != null){
									result._addDet(Comparator.EQ, sym_result, returnAttr);
								}else{ // concrete
									DynamicElementInfo val = (DynamicElementInfo)areturn.getReturnValue(ti);
									Integer objRef = val.getObjectRef();
									if (nameMap.containsKey(objRef)){
										SymbolicInteger name = nameMap.get(objRef);
										assert(name != null);
										result._addDet(Comparator.EQ, sym_result,  name);
									}else{
										String tmp = val.toString();
										tmp = tmp.substring(tmp.lastIndexOf('.')+1);
										result._addDet(Comparator.EQ, sym_result,  new SymbolicInteger(tmp));
									}
								}
							}
							*/
							String returnString = "TODO";
							pc.solve();
							pcString = pc.toString();
							pcPair = new Pair<String,String>(pcString,returnString);
							MethodSummary methodSummary = allSummaries.get(longName);
							Vector<Pair> pcs = methodSummary.getPathConditions();
							if ((!pcs.contains(pcPair)) && (pcString.contains("SYM"))) {
								methodSummary.addPathCondition(pcPair);
								
								methodSummary.addHeapPC(String.valueOf(heapPC));
							}
							allSummaries.put(longName,methodSummary);
						}
						System.out.println("Numeric PC "+pc);
						System.out.println("Heap PC "+heapPC);
						System.out.println("****************************");
						}
					}
				}
			}
		}



	  /*
	   * Save the method summaries to a file for use by others
	   */
//	  public void searchFinished(Search search) {
//		  writeTable();
//	  }

	  /*
	   * The way this method works is specific to the format of the methodSummary
	   * data structure
	   */

	  //TODO:  needs to be changed not to use String representations
	  private void printMethodSummary(PrintWriter pw, MethodSummary methodSummary){
		  Vector<Pair> pathConditions = methodSummary.getPathConditions();
		  if (pathConditions.size() > 0){
			  Iterator it = pathConditions.iterator();
			  String allTestCases = "";
			  while(it.hasNext()){
				  String testCase = methodSummary.getMethodName() + "(";
				  Pair pcPair = (Pair)it.next();
				  String pc = (String)pcPair._1;
				  String errorMessage = (String)pcPair._2;
				  String symValues = methodSummary.getSymValues();
				  String argValues = methodSummary.getArgValues();
				  String argTypes = methodSummary.getArgTypes();

				  StringTokenizer st = new StringTokenizer(symValues, ",");
				  StringTokenizer st2 = new StringTokenizer(argValues, ",");
				  StringTokenizer st3 = new StringTokenizer(argTypes, ",");
				  while(st2.hasMoreTokens()){
					  String token = "";
					  String actualValue = st2.nextToken();
					  String actualType = st3.nextToken();
					  if (st.hasMoreTokens())
						  token = st.nextToken();
					  if (pc.contains(token)){
						  String temp = pc.substring(pc.indexOf(token));
						  String val = temp.substring(temp.indexOf("[")+1,temp.indexOf("]"));
						  if (actualType.equalsIgnoreCase("int") ||
								  actualType.equalsIgnoreCase("float") ||
								  actualType.equalsIgnoreCase("long") ||
								  actualType.equalsIgnoreCase("double"))
							  testCase = testCase + val + ",";
						  else{ //translate boolean values represented as ints
							  //to "true" or "false"
							  if (val.equalsIgnoreCase("0"))
								  testCase = testCase + "false" + ",";
							  else
								  testCase = testCase + "true" + ",";
						  }
					  }else{
						  //need to check if value is concrete
						  if (token.contains("CONCRETE"))
							  testCase = testCase + actualValue + ",";
						  else
							  testCase = testCase + "don't care,";
					  }
				  }
				  if (testCase.endsWith(","))
					  testCase = testCase.substring(0,testCase.length()-1);
				  testCase = testCase + ")";
				  //process global information and append it to the output

				  if (!errorMessage.equalsIgnoreCase(""))
					  testCase = testCase + "  --> " + errorMessage;
				  //do not add duplicate test case
				  if (!allTestCases.contains(testCase))
					  allTestCases = allTestCases + "\n" + testCase;
			  }
			  pw.println(allTestCases);
		  }else{
			  pw.println("No path conditions for " + methodSummary.getMethodName() +
					  "(" + methodSummary.getArgValues() + ")");
		  }
	  }


	  private void printMethodSummaryHTML(PrintWriter pw, MethodSummary methodSummary){
		  pw.println("<h1>Test Cases Generated by Symbolic Java Path Finder for " +
				  methodSummary.getMethodName() + " (Path Coverage) </h1>");

		  Vector<Pair> pathConditions = methodSummary.getPathConditions();
		  if (pathConditions.size() > 0){
			  Iterator it = pathConditions.iterator();
			  String allTestCases = "";
			  String symValues = methodSummary.getSymValues();
			  StringTokenizer st = new StringTokenizer(symValues, ",");
			  while(st.hasMoreTokens())
				  allTestCases = allTestCases + "<td>" + st.nextToken() + "</td>";
			  allTestCases = "<tr>" + allTestCases + "</tr>";
			  while(it.hasNext()){
				  String testCase = "<tr>";
				  Pair pcPair = (Pair)it.next();
				  String pc = (String)pcPair._1;
				  String errorMessage = (String)pcPair._2;
				  //String symValues = methodSummary.getSymValues();
				  String argValues = methodSummary.getArgValues();
				  String argTypes = methodSummary.getArgTypes();
				  //StringTokenizer
				  st = new StringTokenizer(symValues, ",");
				  StringTokenizer st2 = new StringTokenizer(argValues, ",");
				  StringTokenizer st3 = new StringTokenizer(argTypes, ",");
				  while(st2.hasMoreTokens()){
					  String token = "";
					  String actualValue = st2.nextToken();
					  String actualType = st3.nextToken();
					  if (st.hasMoreTokens())
						  token = st.nextToken();
					  if (pc.contains(token)){
						  String temp = pc.substring(pc.indexOf(token));
						  String val = temp.substring(temp.indexOf("[")+1,temp.indexOf("]"));
						  if (actualType.equalsIgnoreCase("int") ||
								  actualType.equalsIgnoreCase("float") ||
								  actualType.equalsIgnoreCase("long") ||
								  actualType.equalsIgnoreCase("double"))
							  testCase = testCase + "<td>" + val + "</td>";
						  else{ //translate boolean values represented as ints
							  //to "true" or "false"
							  if (val.equalsIgnoreCase("0"))
								  testCase = testCase + "<td>false</td>";
							  else
								  testCase = testCase + "<td>true</td>";
						  }
					  }else{
						  //need to check if value is concrete
						  if (token.contains("CONCRETE"))
							  testCase = testCase + "<td>" + actualValue + "</td>";
						  else
							  testCase = testCase + "<td>don't care</td>";
					  }
				  }

				 //testCase = testCase + "</tr>";
				  //process global information and append it to the output


				  if (!errorMessage.equalsIgnoreCase(""))
					  testCase = testCase + "<td>" + errorMessage + "</td>";
				  //do not add duplicate test case
				  if (!allTestCases.contains(testCase))
					  allTestCases = allTestCases + testCase + "</tr>\n";
			  }
			  pw.println("<table border=1>");
			  pw.print(allTestCases);
			  pw.println("</table>");
		  }else{
			  pw.println("No path conditions for " + methodSummary.getMethodName() +
					  "(" + methodSummary.getArgValues() + ")");
		  }

	  }



      //	-------- the publisher interface
	  public void publishFinished (Publisher publisher) {
	    PrintWriter pw = publisher.getOut();
/*
	    publisher.publishTopicStart("Method Summaries");
	    Iterator it = allSummaries.entrySet().iterator();
	    while (it.hasNext()){
	    	Map.Entry me = (Map.Entry)it.next();
	    	MethodSummary methodSummary = (MethodSummary)me.getValue();
	    	printMethodSummary(pw, methodSummary);
	    }

	    publisher.publishTopicStart("Method Summaries (HTML)");
	    it = allSummaries.entrySet().iterator();
	    while (it.hasNext()){
	    	Map.Entry me = (Map.Entry)it.next();
	    	MethodSummary methodSummary = (MethodSummary)me.getValue();
	    	printMethodSummaryHTML(pw, methodSummary);
	    }
	    */
	  }

	  protected class MethodSummary{
			private String methodName = "";
			private String argTypes = "";
			private String argValues = "";
			private String symValues = "";
			private Vector<Pair> pathConditions;
			private String heapPC = "";

			public MethodSummary(){
			 	pathConditions = new Vector<Pair>();
			}

			public void setMethodName(String mName){
				this.methodName = mName;
			}

			public String getMethodName(){
				return this.methodName;
			}

			public void setArgTypes(String args){
				this.argTypes = args;
			}

			public String getArgTypes(){
				return this.argTypes;
			}

			public void setArgValues(String vals){
				this.argValues = vals;
			}

			public String getArgValues(){
				return this.argValues;
			}

			public void setSymValues(String sym){
				this.symValues = sym;
			}

			public String getSymValues(){
				return this.symValues;
			}

			public void addPathCondition(Pair pc){
				pathConditions.add(pc);
			}

			public Vector<Pair> getPathConditions(){
				return this.pathConditions;
			}

			public void addHeapPC(String pc){
				this.heapPC = pc;
			}

			public String getHeapPC(){
				return this.heapPC;
			}
	  }
}
