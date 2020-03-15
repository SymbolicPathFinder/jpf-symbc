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

And jpf-symbc from here:
https://github.com/SymbolicPathFinder/jpf-symbc

Import them in Eclipse as 2 Java projects.
Also create a .jpf dir in your home directory and create in it a file  called "site.properties" with the following content:

jpf-core = ${user.home}/.../path-to-jpf-core-folder/jpf-core

jpf-symbc = ${user.home}/.../path-to-jpf-core-folder/jpf-symbc

extensions=${jpf-core},${jpf-symbc}

Importing Project in IntelliJ-IDEA
-----

<details>
 
<summary>click here </summary>

 **Importing jpf-core on IntelliJ Idea** 
  1. Launch the New Project wizard. If no project is currently opened in IntelliJ IDEA, click **Import 		Project** on the welcome screen. Otherwise, select File > Open > Project from Existing Sources from the main menu.    
    
2. Choose the project root directory containing the build.gradle file. Click OK    
    
3. On the first page of the Import Project wizard, in Import Project from External model, select Gradle and click Next.    
    
4. On the next page of the Import Project wizard, specify Gradle project settings:  Check **Use auto-import** Check **Create separate module per source set** 
5. Click Finish.    
> Make sure that Use default gradle wrapper (recommended) is checked.    
    
    
    
 **Importing jpf-symbc on  IntelliJ Idea**
 
6. After opening jpf-core select **File** > **Project Structure** > **Modules**.    
     
7. Click on **"+"** > Select **Import module from external model** > Select **Eclipse** and click **Next**.    
    
8. Select the root directory > In choose project code style select **default project code style** and click Finish.    
    
> Also make sure you have selected the correct JDK version.    
    
 You should be good to go now. 

</details>


You can then try to run some examples by selecting a .jpf file from the "examples" directory and then selecting a run configuration from the "Run" menu in Eclipse. 
In particular you should select: "run-JPF-symbc" to run Symbolic PathFinder on your example (configuration "run-JPF-symbc-mac" is tailored for Mac).

Good luck!
