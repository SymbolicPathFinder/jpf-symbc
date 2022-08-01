PREREQS

Java PathFinder (JPF): http://javapathfinder.sourceforge.net/
GraphViz: http://www.graphviz.org/

DIRECTORY STRUCTURE

*** src folder ***

There are two listeners -- SymbolicSequenceListener and SymbolicAbstractionListener, both under src folder. 
SymbolicSequenceListener will print the non-redundant method sequences of given sequence length (independent of search order).
SymbolicSequenceListener will also output the JUnit test to execute the method sequences on the class. 

SymbolicAbstractionListener will output the Object State Machine (OSM) for user-specified abstractions (heap-shape, field, branch, and observer)
SymbolicAbstractionListener needs GraphViz to visualize the OSM (http://www.graphviz.org/) and produces two .dot files - osm_method.dot and osm_Sequence.dot

*** examples and launch folder ***

To invoke the listeners on the example drivers (examples folder), use the launch configurations (launch folder)

*** others folder ***

Browse through the different OSMs created under others folder. 


NOTES on SymbolicSequenceListener

  
  Note that all the methods of interest should be specified in +symbolic.method option.
  if a method is not specified in +symbolic.method it will not be printed.
  even if the method, foo(int i) is invoked concretely always, we should have
  foo(con) in +symbolic.method option
  
  Works independent of search order

  Sequence length can be changed in the drivers (examples folder)
  

NOTES on SymbolicAbstractionListener


  Note that all the methods of interest should be specified in +symbolic.method option.
  if a method is not specified in +symbolic.method it will not be printed.
  even if the method, foo(int i) is invoked concretely always, we should have
  foo(con) in +symbolic.method option
  
  OSM (Object State Machine) for sequence length n contains OSM for all lengths less than n

  Sequence length can be changed in the drivers (examples folder)  

Configuration parameters for SymbolicAbstractionListener (these are member attributes of SymbolicAbstractionListener class)
(these will be moved as config option)

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


SOURCE FILES

package gov.nasa.jpf.symbc, /extensions/symbc/src/gov/nasa/jpf/symbc/

gov.nasa.jpf.symbc.Debug.java
gov.nasa.jpf.symbc.JPF_gov_nasa_jpf_symbc_Debug.java

package gov.nasa.jpf.symbc.sequences, /extensions/symbc/src/gov/nasa/jpf/symbc/sequences


gov.nasa.jpf.symbc.sequences.SymbolicSequenceListener.java
gov.nasa.jpf.symbc.sequences.SequenceChoiceGenerator.java

package gov.nasa.jpf.symbc.abstraction, /extensions/symbc/src/gov/nasa/jpf/symbc/abstraction


gov.nasa.jpf.symbc.abstraction.SymbolicAbstractionListener.java
gov.nasa.jpf.symbc.abstraction.OSM.java

EXAMPLES

BST.java
BSTDriverAbstraction.java
BSTDriverSequences.java
BankAccount.java
BankAccountDriverSequences.java
BinTree.java
IncDec.java
IncDecDriverAbstraction.java
IncDecDriverSequences.java
LinkedList.java
MethodSequenceGeneratorTao.java
MySymbolicDriverForBST.java
Stack.java
StackDriverAbstraction.java
StackDriverSequences.java
TaoSymbolicDriverForBST.java
TestBinTree.java

LAUNCH CONFIGURATIONS

BSTDriverAbstraction.launch
BSTDriverSymbolic.launch
BSTDriverSymbolicHeuristic.launch
BankAccountDriverSymbolic.launch
IncDecDriverAbstraction.launch
IncDecDriverConcrete.launch
IncDecDriverStateSpaceDot.launch
IncDecDriverSymbolic.launch
IncDecDriverSymbolicHeuristic.launch
StackDriverAbstraction.launch
StackDriverSymbolic.launch
TaoSymbolicDriverForBST.launch

Symbolic Labels (.jpg files showing Object State Machines)

BST-SeqLen2-AddOnly-MethodOSM-SymbolicLabels.jpg
BST-SeqLen2-AddOnly-SequenceOSM-SymbolicLabels.jpg
BST-SeqLen2-MethodOSM-SymbolicLabels.jpg
BST-SeqLen2-SequenceOSM-SymbolicLabels.jpg
BST-SeqLen3-AddOnly-MethodOSM-SymbolicLabels.jpg
IncDec-Field-SeqLen2-MethodOSM-SymbolicLabels.jpg
IncDec-Field-SeqLen2-SequenceOSM-SymbolicLabels.jpg
Stack-SeqLen2-MethodOSM-SymbolicLabels.jpg
Stack-SeqLen3-MethodOSM-SymbolicLabels.jpg

Concrete Labels (.jpg files showing Object State Machines)

BST-SeqLen1-MethodOSM-ConcreteLabels.jpg
BST-SeqLen2-AddOnly-MethodOSM-ConcreteLabels.jpg
BST-SeqLen2-AddOnly-SequenceOSM-ConcreteLabels.jpg
BST-SeqLen2-MethodOSM-ConcreteLabels.jpg
BST-SeqLen2-MethodOSM-ConcreteLabelsNoPC.jpg
BST-SeqLen2-SequenceOSM-ConcreteLabels.jpg
IncDec-SeqLen1-Field-MethodOSM-ConcreteLabels.jpg
IncDec-SeqLen1-Observer-MethodOSM-ConcreteLabels.jpg
IncDec-SeqLen2-Field-MethodOSM-ConcreteLabels.jpg
IncDec-SeqLen2-Field-SequenceOSM-ConcreteLabels.jpg
IncDec-SeqLen2-HeapShape-MethodOSM-ConcreteLabels.jpg
IncDec-SeqLen2-HeapShape-SequenceOSM-ConcreteLabels.jpg
IncDec-SeqLen2-Observer-MethodOSM-ConcreteLabels.jpg
IncDec-SeqLen2-Observer-SequenceOSM-ConcreteLabels.jpg
IncDec-SeqLen3-Field-MethodOSM-ConcreteLabels.jpg
IncDec-SeqLen4-Field-MethodOSM-ConcreteLabels.jpg
Stack-SeqLen1-MethodOSM-ConcreteLabels.jpg
Stack-SeqLen2-SequenceOSM-ConcreteLabels.jpg
Stack-SeqLen3-SequenceOSM-ConcreteLabels.jpg
stack-SeqLen2-MethodOSM-ConcreteLabels.jpg
stack-SeqLen3-MethodOSM-ConcreteLabels.jpg







