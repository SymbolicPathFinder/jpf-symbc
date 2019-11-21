Symbolic (Java) PathFinder:
---------------------------

Created new branch that contains many updates to SPF;
in particular, interfacing with Z3 is robust; 
also SPF now has a "symcrete" mode that executes paths 
triggered by concrete inputs and collects constraints along the paths

This JPF extension provides symbolic execution for Java bytecode.
It performs a non-standard interpretation of byte-codes.
Currently, it allows symbolic execution on methods with arguments of basic types
(int, long, double, boolean, etc.). Symbolic input globals and method
pre-conditions are specified via user annotations (see symbc/examples and
symbc/test).

A paper describing Symbolic PathFinder appeared at ISSTA'08:

Title: Combining Unit-level Symbolic Execution and System-level Concrete
Execution for Testing NASA Software,
Authors: C. S. Pasareanu, P. C. Mehlitz, D. H. Bushnell, K. Gundy-Burlet,
M. Lowry, S. Person, M. Pape.

Getting Started
----------------

First of all please use Java 8 (I am afraid our tools do not work with newer versions of Java).

Then please download jpf-core from here:
https://github.com/yannicnoller/jpf-core/tree/0f2f2901cd0ae9833145c38fee57be03da90a64f

And jpf-symbc from here:
https://github.com/SymbolicPathFinder/jpf-symbc/tree/b64ab6a0c8dde218b34969b46ee526ece7ddee44

Import them in Eclipse as 2 Java projects.
Also create a .jpf dir in your home directory and create in it a file  called "site.properties" with the following content:

jpf-core = ${user.home}/.../path-to-jpf-core-folder/jpf-core
jpf-symbc = ${user.home}/.../path-to-jpf-core-folder/pf-symbc
extensions=${jpf-core},${jpf-symbc}


You can then try to run some examples by selecting a .jpf file from the "examples" directory and then selecting a run configuration from the "Run" menu in Eclipse. 
In particular you should select: "run-JPF-symbc" to run Symbolic PathFinder on your example (configuration "run-JPF-symbc-mac" is tailored for Mac).

Good luck!
