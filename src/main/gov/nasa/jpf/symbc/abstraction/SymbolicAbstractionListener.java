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

package gov.nasa.jpf.symbc.abstraction;

// does not work well for static methods:summary not printed for errors
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.IRETURN;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.jvm.bytecode.VirtualInvocation;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.bytecode.INVOKESTATIC;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.sequences.SequenceChoiceGenerator;
import gov.nasa.jpf.util.Pair;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ReferenceFieldInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.SystemState;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;
import gov.nasa.jpf.vm.VM;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Vector;

/**
 *
 *
 * @author Mithun Acharya
 *
 * Note that all the methods of interest should be specified in +symbolic.method option.
 * if a method is not specified in +symbolic.method it will not be printed.
 * even if the method, foo(int i) is invoked concretely always, we should have
 * foo(con) in +symbolic.method option
 *
 *
 * Works for DFS order. Haven't checked or proved for other search orders.
 *
 * Algorithm for maintaining OSM graph at method granularity
 * (edge always drawn between lastRecordedState--->newState
 *  while newState can be determined on instruction return,
 *  the main challenge is to maintain the lastRecordedState correctly)
 *
 * 		0. Note down the initialState (first time when an instruction is invoked)
 * 		lastRecordedState = initialState
 *
 * 		1. At instructionExecuted->JVMInvokeInstruction, remember invoked method with
 * 		SequenceChoiceGenerator. Same as SymbolicSequenceListener
 *
 * 		2. On stateBacktracked, update lastRecordedState = getAbstractedState(...)
 *
 * 		3. On instructionExecuted->JVMReturnInstruction,
 * 		newState = getAbstractedState(...)
 * 		add the edge lastRecordedState-----lastInvokedMethod----->newState
 * 		update lastRecordedState = newState
 *
 * 		4. On propertyViolated,
 * 		add the edge lastRecordedState-----lastInvokedMethod----->error-string
 * 		(property violation state will not be explored further)
 *
 * Algorithm for maintaining OSM graph at sequence granularity
 * (edge always drawn between initialState--->lastRecordedState
 *  while initialState can be determined at start, the main challenge
 *  is to maintain the lastRecordedState correctly)
 *
 * 		0. Note down the initial state (first time when an instruction is invoked)
 * 		lastRecordedState = initialState
 *
 * 		1. At instructionExecuted->JVMInvokeInstruction, remember invoked method with
 * 		SequenceChoiceGenerator. Same as SymbolicSequenceListener
 *
 * 		2. On instructionExecuted->JVMReturnInstruction,
 * 		newState = getAbstractedState(...)
 * 		update lastRecordedState = newState
 * 		add the edge initialState-----lastInvokedSequence----->lastRecordedState
 *
 * 		3. On propertyViolated,
 * 		update lastRecordedState = error-string
 * 		add the edge initialState-----lastInvokedSequence----->lastRecordedState
 *
 * OSM for sequence length n contains OSM for all lengths less than n
 *
 * TODO
 *
 * KNOWN PROBLEMS
 *
 * 1) slight problem when matchAbstractState and OSM generation are simultaneously used.
 * When matchAbstractState is turned ON, special care needs to be taken for ignored states.
 * I think this is not done. However, matchAbstractState works with
 * sequence generation (SymbolicSequenceListener)
 *
 * 2) configuration parameters (abstraction and edge label printing options) hardcoded.
 *
 * 3) make exception state specific to exception. Right now all exception states are "EXCEPTION"
 * 		solution: just derive the state from error string.
 *
 * 4) Observer abstraction not general. hard coded currently.
 *
 * 5) Field abstraction limited to *ALL* integer fields only. Should be made general.
 *
 * REFACTOR
 * Can those state querying/manipulating methods be MJI lowered?
 *
 *
 */
public class SymbolicAbstractionListener extends PropertyListenerAdapter{

	// maintains both method and sequence OSMs.
	private static OSM osm;

	// Should be made configuration option
	//############################################################################
	//#########################CONFIG PARAMETERS##################################
	//############################################################################
	// Abstraction used
	private static final int HEAP_SHAPE_ABSTRACTION = 1;
	private static final int FIELD_ABSTRACTION = 2;
	private static final int OBSERVER_ABSTRACTION = 3;
	private static final int BRANCH_ABSTRACTION = 4;
	// by default, the abstraction is based on heap shape.
	private static final int ABSTRACTION = HEAP_SHAPE_ABSTRACTION;

	// what to print on edge labels?
	// concrete parameters in method attributes; path condition with concrete solutions.
	private static final int CONCRETE = 1;
	// only symbolic values in method attributes and path condition
	private static final int SYMBOLIC = 2;
	private static final int EDGE_LABEL_TYPE = SYMBOLIC;

	// Decides if the path-condition needs to be appended to edge labels or not.
	private static final boolean APPENDPC = true;
	//############################################################################
	//#########################CONFIG PARAMETERS##################################
	//############################################################################


	// to record initial state when an instruction is executed for the first time.
	boolean firstTime = true;

	public SymbolicAbstractionListener(Config conf, JPF jpf) {
		jpf.addPublisherExtension(ConsolePublisher.class, this);
	}

	//--- the SearchListener interface
	@Override
	public void searchStarted(Search search) {
		osm = OSM.getSingletonOSMInstance(); // singleton instance
		osm.beginDot_method();
		osm.beginDot_sequence();
	}

	@Override
	public void searchFinished(Search search) {
		osm.endDot_method();
		osm.endDot_sequence();
	}

	/**
	 *
	 * Exception can occur in any abstraction!
	 *
	 * On property violation, get the last invoked method.
	 * the abstracted state is derived from the error string.
	 *
	 *  Update method part of OSM
	 *
	 *
	 *  Update last recorded state for sequences
	 *  Update sequence part of OSM
	 *
	 */
	@Override
	public void propertyViolated (Search search){
		VM vm = search.getVM();
		SystemState ss = vm.getSystemState();
		ChoiceGenerator cg = vm.getChoiceGenerator();

		String lastInvokedMethod = null;
		String pcString = null;

		if (!(cg instanceof PCChoiceGenerator)){
			ChoiceGenerator prev_cg = cg.getPreviousChoiceGenerator();
			while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
				prev_cg = prev_cg.getPreviousChoiceGenerator();
			}
			cg = prev_cg;
		}

		// get the error string
		String error = search.getLastError().getDetails();
		error = "\"" + error.substring(0,error.indexOf("\n")) + "...\"";

		String lastInvokedSequence = null;
		if ((cg instanceof PCChoiceGenerator) &&
				      ((PCChoiceGenerator) cg).getCurrentPC() != null){

			PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
			//solve the path condition
			pc.solve();
			pcString = pc.stringPC();
			// remove the newline character - graphviz does not like it.
			pcString = pcString.substring(pcString.indexOf("\n")+1, pcString.length());
			// get the chain of choice generators.
			ChoiceGenerator [] cgs = ss.getChoiceGenerators();

			if(EDGE_LABEL_TYPE == CONCRETE){
				lastInvokedMethod = getLastInvokedMethod(cgs);
				lastInvokedSequence = getMethodSequence(cgs);
			}
			else if (EDGE_LABEL_TYPE == SYMBOLIC){
				pcString = removeConcreteValues(pcString);
				lastInvokedMethod = getLastInvokedMethodWithSymbolicAttr(cgs);
				lastInvokedSequence = getMethodSequenceWithSymbolicAttr(cgs);
			}
		}

		// Replace this with the specific exception in the error String later.
		String abstractedState = "EXCEPTION";

		// update method part of OSM
		// the exception state wont be explored further...
		// so there is no need to record it.
		osm.update_method(abstractedState, lastInvokedMethod, pcString, APPENDPC);

		// update the last recorded state for sequences and update the sequence part of OSM
		osm.setLastRecordedState_sequence(abstractedState);
		osm.update_sequence(lastInvokedSequence, pcString, APPENDPC);

	}



	/**
	 * backtracking might change the last recorded state of the OSM wrt method
	 * so update it.
	 *
	 * For sequence part of OSM, we have nothing to do.
	 *
	 */
	@Override
	public void stateBacktracked(Search search){

		VM vm = search.getVM();
		Instruction insn = vm.getChoiceGenerator().getInsn();
		SystemState ss = vm.getSystemState();
		ThreadInfo ti = vm.getChoiceGenerator().getThreadInfo();
		MethodInfo mi = insn.getMethodInfo();
		//neha: changed to full name
		String methodName = mi.getFullName();
		int numberOfArgs = mi.getArgumentsSize() - 1;

		Config conf = ti.getVM().getConfig(); // Corina: added fix
		if (BytecodeUtils.isMethodSymbolic(conf, methodName, numberOfArgs, null)){

			String abstractedState = null;
			// JPF has backtracked.
			// So update the last recorded state for method part of OSM.
			int ref = ti.getThis();
			MJIEnv env = ti.getEnv();
			// get the abstracted state
			abstractedState = getAbstractedState(env, ref);
			// update the last recorded state
			osm.setLastRecordedState_method(abstractedState);

		}
	}


	//--- the VMListener interface
	@Override
	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {

		if (!vm.getSystemState().isIgnored()) {
			Instruction insn = executedInstruction;
			SystemState ss = vm.getSystemState();
			ThreadInfo ti = currentThread;


			if (insn instanceof JVMInvokeInstruction && insn.isCompleted(ti)) {
				JVMInvokeInstruction md = (JVMInvokeInstruction) insn;
				String methodName = md.getInvokedMethodName();
				// get number of arguments.
				int numberOfArgs = md.getArgumentValues(ti).length;
				MethodInfo mi = md.getInvokedMethod();
				Config conf = ti.getVM().getConfig(); // Corina: added fix
				//neha: changed invoked method to the full name
				if ((BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null))){
					// if it is JVMInvokeInstruction, just keep track of what
					// method got invoked in the SequenceChoiceGenerator.
					// if it is the first time, record the initial state

					// Do this only once - records initial state
					String abstractedState = null;
					if(firstTime == true){
						MJIEnv env = ti.getEnv();
						int ref = ti.getThis();
						abstractedState = getAbstractedState(env, ref);
						// update the initial state
						// this also updates the last recorded state
						osm.setInitialState_method(abstractedState);
						osm.setInitialState_sequence(abstractedState);
						firstTime = false;
					}

					// get method name
					String shortName = methodName;
					String longName = mi.getLongName();
					if (methodName.contains("("))
						shortName = methodName.substring(0,methodName.indexOf("("));

					// get arg values
					Object [] argValues = md.getArgumentValues(ti);

					// get symbolic attributes
					// concretely executed method will have null attributes.
					byte[] argTypes = mi.getArgumentTypes();
					Object[] attributes = new Object[numberOfArgs];
					StackFrame sf = ti.getTopFrame();
					int count = 1 ; // we do not care about this
					if (md instanceof INVOKESTATIC)
						count = 0;  //no "this" reference
					for (int i = 0; i < numberOfArgs; i++) {
						attributes[i] = sf.getLocalAttr(count);
						count++;
						if(argTypes[i]== Types.T_LONG || argTypes[i] == Types.T_DOUBLE)
							count++;
					}

					// Create a new SequenceChoiceGenerator.
					// this is just to store the information
					// regarding the executed method.
					SequenceChoiceGenerator cg = new SequenceChoiceGenerator(shortName);
					cg.setArgValues(argValues);
					cg.setArgAttributes(attributes);
					// Does not actually make any choice
					ss.setNextChoiceGenerator(cg);
					// nothing to do as there are no choices.
				}
			}
			// get the new state caused by return
			// get the method that just returned and PC.
			// update method part of OSM
			// update last recorded state for methods
			// get the sequence
			// update last recorded state for sequence
			// update sequence part of OSM
			else if (insn instanceof JVMReturnInstruction){
				MethodInfo mi = insn.getMethodInfo();
				String methodName = mi.getName();
				String longName = mi.getLongName();
				int numberOfArgs = mi.getNumberOfArguments();

				Config conf = ti.getVM().getConfig(); // Corina: added fix
				//neha: changed invoked method to fullname
				if (BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null)){

					// get the abstracted state caused by method return
					String abstractedState = null;
					JVMReturnInstruction JVMReturnInstruction = (JVMReturnInstruction)insn;
					int ref = JVMReturnInstruction.getReturnFrame().getThis();
					MJIEnv env = ti.getEnv();
					abstractedState = getAbstractedState(env, ref);

					// get the method that just returned = last invoked method
					// and the pc string.
					String lastInvokedMethod = null;
					String lastInvokedSequence = null;
					String pcString = null;
					ChoiceGenerator cg = vm.getChoiceGenerator();
					if (!(cg instanceof PCChoiceGenerator)){
						ChoiceGenerator prev_cg = cg.getPreviousChoiceGenerator();
						while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
							prev_cg = prev_cg.getPreviousChoiceGenerator();
						}
						cg = prev_cg;
					}
					if ((cg instanceof PCChoiceGenerator) &&
							      ((PCChoiceGenerator) cg).getCurrentPC() != null){

						PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
						//solve the path condition
						pc.solve();
						pcString = pc.stringPC();
						// remove the newline character - graphviz does not like it.
						pcString = pcString.substring(pcString.indexOf("\n")+1, pcString.length());
						// get the chain of choice generators.
						ChoiceGenerator [] cgs = ss.getChoiceGenerators();

						if(EDGE_LABEL_TYPE == CONCRETE){
							lastInvokedMethod = getLastInvokedMethod(cgs);
							lastInvokedSequence = getMethodSequence(cgs);
						}
						else if (EDGE_LABEL_TYPE == SYMBOLIC){
							pcString = removeConcreteValues(pcString);
							lastInvokedMethod = getLastInvokedMethodWithSymbolicAttr(cgs);
							lastInvokedSequence = getMethodSequenceWithSymbolicAttr(cgs);
						}
					}

					// update the OSM graph wrt methods.
					// edge will be drawn between the last recorded state and this new state
					// represented by abstractedState
					osm.update_method(abstractedState, lastInvokedMethod, pcString, APPENDPC);

					// now update the last recorded state wrt methods.
					osm.setLastRecordedState_method(abstractedState);

					// update the last recorded state for sequences
					osm.setLastRecordedState_sequence(abstractedState);
					// update the sequence part of OSM
					// edge will be drawn between initial state and the
					// last recorded state
					osm.update_sequence(lastInvokedSequence, pcString, APPENDPC);
				}
			}
		}
	}


	//---some helper methods

	/**
	 * gets the last invoked method.
	 * explores the SequenceChoiceGenerator chain
	 * and gets the last one in the chain.
	 */
	
	private String getLastInvokedMethod(ChoiceGenerator [] cgs){
		// explore the choice generator chain - unique for a given path.
		ChoiceGenerator cg = null;
		String lastInvokedMethod = null;
		for (int i=cgs.length-1; i>=0; i--){
			cg = cgs[i];
			if ((cg instanceof SequenceChoiceGenerator)){
				lastInvokedMethod = getInvokedMethod((SequenceChoiceGenerator)cg);
				break;
			}
		}
		return lastInvokedMethod;
	}


	/**
	 *
	 * same as getLastInvokedMethod except the attributes are symbolic
	 */
	private String getLastInvokedMethodWithSymbolicAttr(ChoiceGenerator [] cgs){
		// explore the choice generator chain - unique for a given path.
		ChoiceGenerator cg = null;
		String lastInvokedMethodWithSymbolicAttr = null;
		for (int i=cgs.length-1; i>=0; i--){
			cg = cgs[i];
			if ((cg instanceof SequenceChoiceGenerator)){
				lastInvokedMethodWithSymbolicAttr = getInvokedMethodWithSymbolicAttr((SequenceChoiceGenerator)cg);
				break;
			}
		}
		return lastInvokedMethodWithSymbolicAttr;
	}



	/**
	 *
	 * traverses the ChoiceGenerator chain to get the method sequence
	 * looks for SequenceChoiceGenerator in the chain
	 * SequenceChoiceGenerators have information about the methods
	 * executed and hence the method sequence can be obtained.
	 * A single 'methodSequence' is a vector of invoked 'method's along a path
	 * A single invoked 'method' is represented as a String.
	 *
	 */
	private String getMethodSequence(ChoiceGenerator [] cgs){
		// A method sequence is a vector of strings
		Vector<String> methodSequence = new Vector<String>();
		ChoiceGenerator cg = null;
		// explore the choice generator chain - unique for a given path.
		for (int i=0; i<cgs.length; i++){
			cg = cgs[i];
			if ((cg instanceof SequenceChoiceGenerator)){
				methodSequence.add(getInvokedMethod((SequenceChoiceGenerator)cg));
			}
		}
		if (methodSequence == null) return null;
		return methodSequence.toString();
	}


	/**
	 *
	 * same as getMethodSequence except attributes are symbolic
	 */
	private String getMethodSequenceWithSymbolicAttr(ChoiceGenerator [] cgs){
		// A method sequence is a vector of strings
		Vector<String> methodSequenceWithSymbolicAttr = new Vector<String>();
		ChoiceGenerator cg = null;
		// explore the choice generator chain - unique for a given path.
		for (int i=0; i<cgs.length; i++){
			cg = cgs[i];
			if ((cg instanceof SequenceChoiceGenerator)){
				methodSequenceWithSymbolicAttr.add(getInvokedMethodWithSymbolicAttr((SequenceChoiceGenerator)cg));
			}
		}
		if (methodSequenceWithSymbolicAttr == null) return null;
		return methodSequenceWithSymbolicAttr.toString();
	}




	/**
	 * A single invoked 'method' is represented as a String.
	 * information about the invoked method is got from the SequenceChoiceGenerator
	 */
	private static String getInvokedMethod(SequenceChoiceGenerator cg){
		String invokedMethod = "";

		// get method name
		String shortName = cg.getMethodShortName();
		invokedMethod +=  shortName + "(";

		// get argument values
		Object[] argValues = cg.getArgValues();

		// get number of arguments
		int numberOfArgs = argValues.length;

		// get symbolic attributes
		Object[] attributes = cg.getArgAttributes();

		// get the solution
		for(int i=0; i<numberOfArgs; i++){
			Object attribute = attributes[i];
			if (attribute != null){ // parameter symbolic
				IntegerExpression e = (IntegerExpression)attributes[i];
				invokedMethod += e.solution() + ",";
			}
			else { // parameter concrete - for a concrete parameter, the symbolic attribute is null
				invokedMethod += argValues[i];
			}
		}

		// remove the extra comma
		if (invokedMethod.endsWith(","))
			invokedMethod = invokedMethod.substring(0,invokedMethod.length()-1);
		invokedMethod += ")";

		return invokedMethod;
	}


	/**
	 *
	 * Similar to getInvokedMethod except that the arguments are symbolic.
	 *
	 */
	private static String getInvokedMethodWithSymbolicAttr(SequenceChoiceGenerator cg){
		String invokedMethodWithSymbolicAttr = "";

		// get method name
		String shortName = cg.getMethodShortName();
		invokedMethodWithSymbolicAttr +=  shortName + "(";

		// get argument values
		Object[] argValues = cg.getArgValues();

		// get number of arguments
		int numberOfArgs = argValues.length;

		// get symbolic attributes
		Object[] attributes = cg.getArgAttributes();


		// insert the symbolic attributes
		for(int i=0; i<numberOfArgs; i++){
			Object attribute = attributes[i];
			if (attribute != null){ // parameter symbolic
				String attributeString = attribute.toString();
				// remove concrete value.
				attributeString = removeConcreteValues(attributeString);
				invokedMethodWithSymbolicAttr += attributeString + ",";
			}
			else { // parameter concrete - for a concrete parameter, the symbolic attribute is null
				invokedMethodWithSymbolicAttr += argValues[i];
			}
		}

		// remove the extra comma
		if (invokedMethodWithSymbolicAttr.endsWith(","))
			invokedMethodWithSymbolicAttr = invokedMethodWithSymbolicAttr.substring(0,invokedMethodWithSymbolicAttr.length()-1);
		invokedMethodWithSymbolicAttr += ")";

		return invokedMethodWithSymbolicAttr;
	}

	/**
	 * removes all concrete values.
	 * for example,
	 * X_1_SYMINT[-10000] < X_2_SYMINT[-9999] becomes X_1 < X_2
	 *
	 */
	private static String removeConcreteValues(String string){
		// regex matching
		string = string.replaceAll("_SYMINT\\[[-0-9]*\\]", "");
		return string;
	}




	//---state query/manipulation methods
	// Shouldn't these lowered with MJI?
	// the heap shape is captured in the sequence
	private static String sequence;
	// set to keep track of objects already visited; avoids revisiting
	private static HashSet<Integer> discovered;
	/**
	 * Assumes rooted heap.
	 * A rooted heap is a pair <r, h> of a root object r and
	 * a heap h such that all objects in h are reachable from r
	 *
	 * Performs a DFS over objects reachable from the root, recursively.
	 *
	 * Note:
	 * 	In DFS, discovery and finish time of nodes have parenthesis structure.
	 *
	 *
	 */
	private static String traverseRootedHeapAndGetSequence(MJIEnv env, int n){
		// lets call the current vertex v
		if (n==-1) { // vertex v is null
			// for null vertex, discovery and finish time are the same
			// so open and close the bracket all in one place.
			sequence += "{";
			sequence += "-1";
			sequence += "}";
		}
		else{ // vertex v, is not null
			if (!discovered.contains(new Integer(n))){ // vertex v just discovered
				// discovery time for v - so put v into the hashset and open paranthesis
				discovered.add(new Integer(n));
				sequence += "{";
				sequence += "0";

				// Now start traversing all undiscovered successors of v
				ClassInfo ci = env.getClassInfo(n);
				FieldInfo[] fields = ci.getDeclaredInstanceFields();
				for (int i = 0; i < fields.length; i++)
				if (fields[i] instanceof ReferenceFieldInfo) {
					String fname = fields[i].getName();
					//System.out.println("field name " + fname);
					int temp = env.getReferenceField(n, fname);
					// null (short-circuited) OR successor yet undiscovered
					if(temp==-1 || !discovered.contains(new Integer(temp))){
						traverseRootedHeapAndGetSequence(env, temp);
					}
				}
				// All undiscovered successors of v are discovered. We are finished with v.
				// finish time for v - so, close parenthesis.
				sequence += "}";
			}
			else{ // vertex v is already discovered - do nothing
			}
		}
		return sequence;
	}


	/**
	 *
	 * Linearizes the heap.
	 *
	 */
	private static String linearizeRootedHeap(MJIEnv env, int rootRef){
		// create a new map to store ids of visited objects
		// storing is done to avoid revisiting.
		discovered = new HashSet<Integer>();
		// "empty" the sequence
		sequence="";
		// get the sequence for this rooted heap.
		sequence = traverseRootedHeapAndGetSequence(env, rootRef);
		return sequence;
	}


 	/**
 	 * Abstraction based on heap shape
 	 */
 	private static String getHeapShapeAbstractedState(MJIEnv env, int objvRef){
 		// get the sequence for the rooted heap through heap linearization
		String sequence = linearizeRootedHeap(env, objvRef);
		return sequence;
 	}



 	/**
 	 * sequence is value of the field or combination of fields.
	 * right now, I will include all non-reference fields which are integers.
	 * for now, state is represented by the concatenation of all non-reference integer fields
 	 */
 	private static String getFieldAbstractedState(MJIEnv env, int objvRef){
 		String sequence = "";
 		ClassInfo ci = env.getClassInfo(objvRef);
		FieldInfo[] fields = ci.getDeclaredInstanceFields();
		for (int i = 0; i < fields.length; i++)
		if (!(fields[i] instanceof ReferenceFieldInfo)) {
			String fname = fields[i].getName();
			//System.out.println("field name " + fname);
			String type = fields[i].getType();
			if (type.equals("int")){
				sequence = sequence + env.getIntField(objvRef, fname);
			}
		}
		return sequence;
 	}



 	/**
 	 * Abstraction is based on user-provided observer method.
 	 * Right now, hardcoded implementation wrt isZero() observer method of IncDec.java
 	 * Hence it works only with IncDecDriverAbstraction.java
 	 * Find out how to invoke observer method on the object here!
 	 *
 	 */
 	private static String getObserverAbstractedState(MJIEnv env, int objvRef) {
 		ClassInfo ci = env.getClassInfo(objvRef);
		FieldInfo[] fields = ci.getDeclaredInstanceFields();
		String fname = fields[0].getName(); // should be global
		int global = env.getIntField(objvRef, fname);
 		if(global==0) return "isZero()==true";
 		else return "isZero()==false";
 	}


 	/**
 	 *
 	 * currently, not sure what to do
 	 */
 	private static String getBranchAbstractedState(MJIEnv env, int objvRef){
 		return null;
 	}



 	/**
 	 * Simply gets the abstracted state (as a String sequence)
 	 * depending on user-defined abstraction
 	 */
	private static String getAbstractedState(MJIEnv env, int objvRef){
		// get the abstract state as a string sequence based on the abstraction
		String abstractedState = null;
		switch(ABSTRACTION){ // the abstraction for the object state machine.
			case HEAP_SHAPE_ABSTRACTION:
				abstractedState = getHeapShapeAbstractedState(env, objvRef);
				break;
			case FIELD_ABSTRACTION:
				abstractedState = getFieldAbstractedState(env, objvRef);
				break;
			case OBSERVER_ABSTRACTION:
				abstractedState = getObserverAbstractedState(env, objvRef);
				break;
			case BRANCH_ABSTRACTION:
				abstractedState = getBranchAbstractedState(env, objvRef);
				break;
			default:
				break;
		}
		return abstractedState;
	}
}
