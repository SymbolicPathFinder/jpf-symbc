string-solver-integration.md

## String Constraint Solvers in SPF ##

These are general notes on integrating string solvers into SPF. While there are many ways this can be accomplished, these notes present a straightforward approach that can be adapted to most any solver.

### Accessing the solver from Java ###

First, the solver must be accessible through Java, ideally through a .jar file placed in the lib directory. In the case of a solver that is written in a language other than Java, this .jar file acts as a wrapper around the native language solver methods and objects using the Java Native Interface, JNI. These methods will be called by the solver translation code developed specifically for the given solver.

Example .jar files:  
__com.microsoft.z3.jar__  
__automaton.jar__  

If a .jar file does not exist for a solver, JNI code can be placed directly in the translation class as an alternative. In both cases, the native libraries needed to support JNI for a specific platform need to be accessible in the lib directory.

Example JNI code:  
__edu.ucsb.cs.vlab.DriverProxy.java__  

### Translating SPF constructs to solver inputs ###

Second, a translation class needs to be created in SPF that provides the method _isSat()_ that returns the satisfiability of a given string path condition. It takes as parameters the SPF global graph and a path condition. The translation class is responsible for interpreting the path condition and global graph and translating them into a set of constructs compatible with the given solver. The translation class accesses the solver using the methods and objects provided in the .jar file, or with JNI code accessing the solver libraries directly.

If the solver returns a solution for variables in addition to satisfiability, the translation class is responsible for populating the string path condition solution property with the solution values. This allows SPF to access the solution values.

Location:  
__gov.nasa.jpf.symbc.string.translate__  

Examples:  
__gov.nasa.jpf.symbc.string.translate.TranslateToIGEN.java__  
__gov.nasa.jpf.symbc.string.translate.TranslateToABC.java__  
__edu.ucsb.cs.vlab.versions.Z3String3Processor.java__

### Identifying the solver, executing the translation isSat() method

Third, the __SymbolicStringConstraintsGeneral__ class needs to be modified to include the identity and actions for the new solver. The solver identity is provided by a class property that is a unique string identifier for the solver (public static final String _identifier_). This identifier is used to specify the string solver in the .jpf file at runtime. The class instance variable solver is set to the correct identifier at the start of the _inner_isSatisfiable()_ method.

Finally, the solver needs to be added to the section in the _inner_isSatisfiable()_ method that contains the set of conditionals that execute the correct actions for a given solver. Typically this action will be setting the _decisionProcedure_ variable to the output of the translation classes _isSat()_ method.

Location:  
__gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral__  

### Alternative to JNI or .jar files ###

If a solver does not have a .jar file exposing the required functionality, it may be possible to interface the solver if it has command line functionality that can return results that a translation class can interpret. For example, a translation class can create an  instance of a binary executable and redirect the input and output of the instance in order to issue commands and receive results.

### Setting solver properties in the .jpf file ###

If a solver accommodates or requires special settings, these can be specified at runtime through the .jpf file if modifications are made to SPF. Properties specified in the .jpf file are exposed to classes in SPF through static public properties of the __SymbolicInstructionFactory__ class. The static public properties need to be declared in the class, and subsequently set in the constructor method. Properties in the .jpf file are discovered by interrogating the __Config__ object passed to the constructor.

Once the __SymbolicInstructionFactory__ class has been modified to set the solver properties, they can be accessed within the solver translation code by importing the __SymbolicInstructionFactory__ class and accessing its public static properties.

Location:  
__gov.nasa.jpf.symbc.SymbolicInstructionFactory__

Example in .jpf file:  
__symbolic.z3str3_aggressive_length_testing=true__  

Accessible in translator class as:   
__SymbolicInstructionFactory.z3str3_aggressive_length_testing__
