Symbolic (Java) PathFinder:
---------------------------



This JPF extension provides symbolic execution for Java bytecode.
It performs a non-standard interpretation of byte-codes.
It allows symbolic execution on methods with arguments of basic types
(int, long, double, boolean, etc.). It also supports symbolic strings, arrays, 
and user-defined data structures.

SPF now has a "symcrete" mode that executes paths 
triggered by concrete inputs and collects constraints along the paths

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
or here
https://github.com/corinus/jpf-core

And jpf-symbc from here:
https://github.com/SymbolicPathFinder/jpf-symbc

Import them in Eclipse as 2 Java projects.
Also create a .jpf dir in your home directory and create in it a file  called "site.properties" with the following content:

jpf-core = ${user.home}/.../path-to-jpf-core-folder/jpf-core

jpf-symbc = ${user.home}/.../path-to-jpf-core-folder/jpf-symbc

extensions=${jpf-core},${jpf-symbc}


You can then try to run some examples by selecting a .jpf file from the "examples" directory and then selecting a run configuration from the "Run" menu in Eclipse. 
In particular you should select: "run-JPF-symbc" to run Symbolic PathFinder on your example (configuration "run-JPF-symbc-mac" is tailored for Mac).

Good luck!
