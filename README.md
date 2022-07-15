- [About Symbolic PathFinder](#About-Symbolic-PathFinder)
- [Wiki of SPF](#Wiki-of-SPF)
- [Installing SPF](#Installing-SPF)
  - [Java](#Java)
  - [Git](#Git)
  - [Ant](#Ant)
  - [Java PathFinder (jpf-core)](#Java-PathFinder-jpf-core)
  - [Symbolic PathFinder (jpf-symbc)](#Symbolic-PathFinder-jpf-symbc)
- [Running SPF](#Running-SPF)
  - [Example using choco-solver](#Example-using-choco-solver)
  - [Example using Z3](#Example-using-Z3)
  - [Example using CVC3](#Example-using-CVC3)
  - [Other examples](#Other-examples)
- [Running SPF within Eclipse](#Running-SPF-within-Eclipse)
- [Using SPF](#Using-SPF)
  - [Compile Java app](#Compile-Java-app)
  - [Properties file](#Properties-file)
- [Questions about SPF](#Questions-about-SPF)
- [Contributing to SPF](#Contributing-to-SPF)
  - [Tackle reported issues](#Tackle-reported-issues)
  - [Add tests](#Add-tests)
  - [Document code](#Document-code)

## About Symbolic PathFinder

> Symbolic PathFinder (SPF) combines symbolic execution with model checking and constraint solving for automated test case generation and error detection in Java programs with unspecified inputs.  In this tool, programs are executed on symbolic inputs representing multiple concrete inputs. Values of variables are represented as constraints generated from the analysis of Java bytecode. The constraints are solved using off-the shelf solvers to generate test inputs guaranteed to achieve complex coverage criteria.  SPF has been used successfully at NASA, in academia, and in industry.

Corina S. Păsăreanu and Neha Rungta.  [Symbolic PathFinder: symbolic execution of Java bytecode.](https://doi.org/10.1145/1858996.1859035)

A video of a talk by Corina Păsăreanu on SPF can be found at [YouTube](https://www.youtube.com/watch?v=4lcNyc6_t4U).

### Wiki of SPF

Additional information can be found on the [Wiki of SPF](https://github.com/SymbolicPathFinder/jpf-symbc/wiki).

## Installing SPF

### Java

Use [Java](https://www.oracle.com/ca-en/java/technologies/javase/javase8-archive-downloads.html)'s version 8.  To check which version of Java (if any) is currently in use, issue the following command.
```
> java -version
java version "1.8.0_241"
Java(TM) SE Runtime Environment (build 1.8.0_241-b07)
Java HotSpot(TM) 64-Bit Server VM (build 25.241-b07, mixed mode)
```

### Git

To check if any version of [Git](https://git-scm.com/downloads) is currently in use, issue the following command.
```
> git --version
git version 2.26.2.windows.1
```

### Ant

To check if any version of [Ant](https://ant.apache.org/) is currently in use, issue the following command.
```
> ant -version
Apache Ant(TM) version 1.9.16 compiled on July 10 2021
```

### Java PathFinder (jpf-core)

It is convenient, yet not essential, to put the directories of jpf-core and jpf-symbc in a common directory.  Assume that this common directory is called jpf.

```
jpf/
| jpf-core/
| jpf-symbc/
```

1. Clone jpf-core and switch to the java-8 branch using Git: go the directory where you want to put jpf-core (the above mentioned jpf directory) and issue the following commands.
```
>  git clone https://github.com/javapathfinder/jpf-core.git
Cloning into 'jpf-core'...
remote: Enumerating objects: 3868, done.
remote: Counting objects: 100% (333/333), done.
remote: Compressing objects: 100% (192/192), done.
remote: Total 3868 (delta 105), reused 245 (delta 62), pack-reused 3535
Receiving objects: 100% (3868/3868), 2.26 MiB | 1.17 MiB/s, done.
Resolving deltas: 100% (1865/1865), done.
> cd jpf-core
> git checkout -b java-8 origin/java-8
Switched to a new branch 'java-8'
Branch 'java-8' set up to track remote branch 'java-8' from 'origin'.
> git branch
* java-8
  master
```
2. Build jpf-core with Ant: inside the jpf-core directory, issue the following command.
```
> ant build
Buildfile: C:\Users\someone\Documents\jpf\jpf-core\build.xml

[lots of text deleted]

BUILD SUCCESSFUL
Total time: 7 seconds
```
3. Optional (but needed for step 5): to run the tests, you need JUnit 4.  Download a jar file for JUnit 4 from [junit-team](https://github.com/junit-team/junit4/wiki/Download-and-Install).  Save the jar file.
4. Optional (but needed for step 5): set the environment variable JUNIT_HOME to the path to the directory that contains the JUnit 4 jar file.  In a Windows 10 PowerShell this can be done by issuing the following command (do not forget the double quotes).
```
> $Env:JUNIT_HOME = "/path/to/directory/with/junit-jar-file/"
```
In a Linux sh this can be done by issuing the following command.
```
> export JUNIT_HOME=/path/to/directory/with/junit-jar-file/
```
In a Linux csh this can be done by issuing the following command.
```
> setenv JUNIT_HOME /path/to/directory/with/junit-jar-file/
```
5. Optional: run the tests with Ant: inside the jpf-core directory, issue the following command (note that this may take half an hour).
```
> ant test
Buildfile: C:\Users\someone\Documents\jpf\jpf-core\build.xml

[lots of text deleted]

test:
    [junit] Running TypeNameTest
    [junit] Tests run: 1, Failures: 0, Errors: 0, Skipped: 0, Time elapsed: 0.616 sec
    [junit] Running gov.nasa.jpf.ConfigTest
    [junit] Tests run: 9, Failures: 0, Errors: 0, Skipped: 0, Time elapsed: 0.22 sec
    [junit] Running gov.nasa.jpf.jvm.ClassInfoTest

[lots of text deleted]

    [junit] Running java8.TypeAnnotationTest
    [junit] Tests run: 1, Failures: 0, Errors: 0, Skipped: 0, Time elapsed: 0.577 sec

BUILD FAILED
C:\Users\someone\Documents\jpf\jpf-core\build.xml:453: if=test.failed

Total time: 27 minutes 35 seconds
```
Although some tests may fail, you should still be able to run Java PathFinder.

6. Create a directory named .jpf inside your home directory.  To find your home directory, run the following Java app.
```java
public class PrintUserHome {
  public static void main(String[] args) {
    System.out.println(System.getProperty("user.home"));
  }
}
```
7. Inside the .jpf directory, create a file named site.properties with the following content.
```
# JPF site configuration
jpf-core=/path/to/directory/of/jpf-core/
extensions=${jpf-core}
```
8. Add the path to the bin directory of jpf-core to the environment variable PATH. For example, in a Windows 10 PowerShell this can be done by issuing the following command (do not forget the double quotes).
```
> $Env:PATH = "/path/to/bin/directory/of/jpf-core/;" + $Env:PATH
```
In a Linux sh this can be done by issuing the following command.
```
> PATH=/path/to/bin/directory/of/jpf-core/:$PATH
```
In a Linux csh this can be done by issuing the following command.
```
> set path=(/path/to/bin/directory/of/jpf-core/ $path)
```
9. Run jpf-core on the example HelloWorld, that comes with jpf-core, by issuing the following command.
```
> jpf HelloWorld
JavaPathfinder core system v8.0 - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
HelloWorld.main()

====================================================== search started: 30/06/22 8:39 AM
I won't say it!

====================================================== results
no errors detected

====================================================== statistics
elapsed time:       00:00:00
states:             new=1,visited=0,backtracked=1,end=1
search:             maxDepth=1,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=0
heap:               new=353,released=11,maxLive=0,gcCycles=1
instructions:       3278
max memory:         489MB
loaded code:        classes=60,methods=1338

====================================================== search finished: 30/06/22 8:39 AM
```

A video showing the above steps can be found at [YouTube](https://www.youtube.com/watch?v=8ME-AubKKMo).

### Symbolic PathFinder (jpf-symbc)

1. Clone jpf-symbc using Git: go the directory where you want to put jpf-symbc (the above mentioned jpf directory) and issue the following command.
```
> git clone https://github.com/SymbolicPathFinder/jpf-symbc.git
Cloning into 'jpf-symbc'...
remote: Enumerating objects: 1786, done.
remote: Total 1786 (delta 0), reused 0 (delta 0), pack-reused 1786
Receiving objects: 100% (1786/1786), 62.48 MiB | 947.00 KiB/s, done.
Resolving deltas: 100% (922/922), done.
Updating files: 100% (1045/1045), done.
warning: the following paths have collided (e.g. case-sensitive paths
on a case-insensitive filesystem) and only one from the same
colliding group is in the working tree:

  'doc/SymExe.PNG'
  'doc/SymExe.png'
```
2. Build jpf-core with Ant: inside the jpf-symbc directory, issue the following command.
```
> ant build

Buildfile: C:\Users\someone\Documents\jpf\jpf-symbc\build.xml

-init:
    [mkdir] Created dir: C:\Users\someone\Documents\jpf\jpf-symbc\build

[lots of text deleted]

BUILD SUCCESSFUL
Total time: 1 minute 6 seconds
```
3. Optional: run the tests with Ant: inside the jpf-symbc directory, issue the following command.
```
> ant test
Buildfile: C:\Users\someone\Documents\jpf\jpf-symbc\build.xml

[lots of text deleted]

    [junit] ====================================================== system under test
    [junit] gov.nasa.jpf.symbc.TestTermination.runTestMethod()
    [junit]
    [junit] ====================================================== search started: 30/06/22 8:49 AM
    [junit] here
    [junit]
    [junit] ====================================================== results
    [junit] no errors detected
    [junit]
    [junit] ====================================================== search finished: 30/06/22 8:49 AM
    [junit] ------------- ---------------- ---------------
    [junit]
    [junit] Testcase: mainTest took 0.67 sec

BUILD SUCCESSFUL
Total time: 3 minutes 17 seconds
```
4. Inside the .jpf directory, modify the file named site.properties as follows.
```
# JPF site configuration
jpf-core=/path/to/directory/of/jpf-core/
jpf-symbc=/path/to/directory/of/jpf-symbc/
extensions=${jpf-core},${jpf-symbc}
```

A video showing the above steps can be found at [YouTube](https://www.youtube.com/watch?v=dyapiIEAr1k).

## Running SPF

The following Java app will be used as running example.
```java
public class Example {

  /**
   * Returns the minimum of the given integers.
   *
   * @param x an integer
   * @param y an integer
   * @return the minimum of x and y
   */
  private static int min(int x, int y) {
    if (x > y) {
      // swap x and y
      x = x + y;
      y = x - y;
      x = x - y;
    }
    if (x > y) {
      assert false;
    }
    return x;
  }

  public static void main(String[] args) {
    Example.min(0, 1);
  }
}
```
This example can be found in the src/examples/ directory of jpf-symbc.

### Example using choco-solver

To run SPF, you need (the bytecode of) a Java app as well as a file that configures JPF and SPF.  The file is a Java properties file, that is, a file containing keys and corresponding values.  To run SPF with the [choco-solver](https://choco-solver.org/) on the above Java app, you can use the following properties file.
```
# fully qualified name of the Java app
target = Example

# path to the bytecode of the target (and classes used by the target)
classpath = ${jpf-symbc}/build/examples/

# path to the Java code of the target (and classes used by the target)
sourcepath = ${jpf-symbc}/src/examples/

# method and its parameters
symbolic.method = Example.min(sym#sym)

# solver used (default)
symbolic.dp = choco

# listener that generates JUnit test cases
listener = gov.nasa.jpf.symbc.sequences.SymbolicSequenceListener
```
The properties file is called ExampleChoco.jpf and can be found in the src/examples/ directory of jpf-symbc.  To run SPF, go to the src/examples/ directory of jpf-symbc and issue the following command.
```
> jpf ExampleChoco.jpf
symbolic.min_int=-2147483648
symbolic.min_long=-9223372036854775808
symbolic.min_short=-32768
symbolic.min_byte=-128
symbolic.min_char=0
symbolic.max_int=2147483647
symbolic.max_long=9223372036854775807
symbolic.max_short=32767
symbolic.max_byte=127
symbolic.max_char=65535
symbolic.min_double=4.9E-324
symbolic.max_double=1.7976931348623157E308
JavaPathfinder core system v8.0 - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
Example.main()

====================================================== search started: 7/14/22 9:20 PM
--------->property violated
pc 1 constraint # = 1
x_1_SYMINT > y_2_SYMINT

====================================================== error 1
gov.nasa.jpf.vm.NoUncaughtExceptionsProperty
java.lang.AssertionError
        at Example.min(Example.java:40)
        at Example.main(Example.java:46)


====================================================== snapshot #1
thread java.lang.Thread:{id:0,name:main,status:RUNNING,priority:5,isDaemon:false,lockCount:0,suspendCount:0}
  call stack:
        at Example.min(Example.java:40)
        at Example.main(Example.java:46)


====================================================== Method Sequences
[(expected = java.lang.AssertionError.class), min(-2147483647,-2147483648), ##EXCEPTION## "java.lang.AssertionError..."]

====================================================== JUnit 4.0 test class
import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;

public class ExampleTest {

        private Example example;

        @Before
        public void setUp() throws Exception {
                example = new Example();
        }

        @Test(expected = java.lang.AssertionError.class)
        public void test0() {
                example.min(-2147483647,-2147483648);
                //should lead to ##EXCEPTION## "java.lang.AssertionError..."
        }
}

====================================================== results
error #1: gov.nasa.jpf.vm.NoUncaughtExceptionsProperty "java.lang.AssertionError  at Example.min(Example.j..."

====================================================== statistics
elapsed time:       00:00:00
states:             new=3,visited=0,backtracked=0,end=0
search:             maxDepth=3,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=2
heap:               new=367,released=2,maxLive=0,gcCycles=1
instructions:       3271
max memory:         236MB
loaded code:        classes=64,methods=1333

====================================================== search finished: 7/14/22 9:20 PM
```

### Example using Z3

For examples that use [Z3](https://github.com/Z3Prover/z3/wiki), dynamic libraries/shared libraries for Z3 need to be linked.  These libraries can be found in the lib directory of jpf-symbc.  For example, in a Windows 10 PowerShell this can be done by issuing the following command (do not forget the double quotes).
```
>  $Env:PATH = "/path/to/lib/directory/of/jpf-symbc/;" + $Env:PATH
```
In a Linux sh this can be done by issuing the following command.
```
> export LD_LIBRARY_PATH=/path/to/lib/directory/of/jpf-symbc/
```
In a Linux csh this can be done by issuing the following command.
```
> setenv LD_LIBRARY_PATH /path/to/lib/directory/of/jpf-symbc/
```
In a macOS sh this can be done by issuing the following command.
```
> export DYLD_LIBRARY_PATH=/path/to/lib/directory/of/jpf-symbc/
```

The properties file for this example is called ExampleZ3.jpf and can be found in the src/examples/ directory of jpf-symbc.  To run SPF, go to the src/examples/ directory of jpf-symbc and issue the following command.
```
> jpf ExampleZ3.jpf
symbolic.min_int=-2147483648
symbolic.min_long=-9223372036854775808
symbolic.min_short=-32768
symbolic.min_byte=-128
symbolic.min_char=0
symbolic.max_int=2147483647
symbolic.max_long=9223372036854775807
symbolic.max_short=32767
symbolic.max_byte=127
symbolic.max_char=65535
symbolic.min_double=4.9E-324
symbolic.max_double=1.7976931348623157E308
JavaPathfinder core system v8.0 - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
Example.main()

====================================================== search started: 7/14/22 9:21 PM

====================================================== Method Sequences
[min(0,-1)]
[min(0,0)]

====================================================== JUnit 4.0 test class
import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;

public class ExampleTest {

        private Example example;

        @Before
        public void setUp() throws Exception {
                example = new Example();
        }

        @Test
        public void test0() {
                example.min(0,-1);
        }

        @Test
        public void test1() {
                example.min(0,0);
        }
}

====================================================== results
no errors detected

====================================================== statistics
elapsed time:       00:00:00
states:             new=4,visited=0,backtracked=4,end=2
search:             maxDepth=3,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=2
heap:               new=351,released=20,maxLive=349,gcCycles=3
instructions:       3259
max memory:         236MB
loaded code:        classes=60,methods=1292

====================================================== search finished: 7/14/22 9:21 PM
```

### Example using CVC3

For examples that use [CVC3](https://cs.nyu.edu/acsys/cvc3/), dynamic libraries/shared libraries for CVC3 need to be linked. The dynamic libraries for Windows 64-bit machines are not readily available.  As a result, SPF cannot be run with CVC3 on Windows 64-bit machines.

To link the 64-bit shared library files, in a Linux sh issue the following command.
```
> export LD_LIBRARY_PATH=/path/to/lib/64bit/subdirectory/of/jpf-symbc/
```
In a Linux csh issue the following command.
```
> setenv LD_LIBRARY_PATH /path/to/lib/64bit/subdirectory/of/jpf-symbc/
```
In a macOS sh issue the following command.
```
> export DYLD_LIBRARY_PATH=/path/to/lib/64bit/subdirectory/of/jpf-symbc/
```

The properties file for this example is called ExampleCVC3.jpf and can be found in the src/examples/ directory of jpf-symbc.  To run SPF, go to the src/examples/ directory of jpf-symbc and issue the following command.
```
> jpf ExampleCVC3.jpf
symbolic.min_int=-2147483648
symbolic.min_long=-9223372036854775808
symbolic.min_short=-32768
symbolic.min_byte=-128
symbolic.min_char=0
symbolic.max_int=2147483647
symbolic.max_long=9223372036854775807
symbolic.max_short=32767
symbolic.max_byte=127
symbolic.max_char=65535
symbolic.min_double=4.9E-324
symbolic.max_double=1.7976931348623157E308
JavaPathfinder core system v8.0 - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
Example.main()

====================================================== search started: 7/14/22 9:22 PM

====================================================== Method Sequences
[min(-2147483647,-2147483648)]
[min(-2147483648,-2147483648)]

====================================================== JUnit 4.0 test class
import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;

public class ExampleTest {

        private Example example;

        @Before
        public void setUp() throws Exception {
                example = new Example();
        }

        @Test
        public void test0() {
                example.min(-2147483647,-2147483648);
        }

        @Test
        public void test1() {
                example.min(-2147483648,-2147483648);
        }
}

====================================================== results
no errors detected

====================================================== statistics
elapsed time:       00:00:00
states:             new=4,visited=0,backtracked=4,end=2
search:             maxDepth=3,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=2
heap:               new=351,released=20,maxLive=349,gcCycles=3
instructions:       3259
max memory:         236MB
loaded code:        classes=60,methods=1292

====================================================== search finished: 7/14/22 9:22 PM
```

### Other examples

In the src/examples/ directory of jpf-symbc, also examples that use [Coral](https://pan.cin.ufpe.br/coral/) and [IASolver](https://www.cs.brandeis.edu/~tim/Applets/IAsolver.html) can be found.  Their properties files ExampleCoral.jpf and ExampleIASolver.jpf can be found in that directory.

## Running SPF within Eclipse

1. Install jpf-core and jpf-symbc as described above.
2. Start Eclipse and create a new Eclipse workspace or use an existing one.  
3. Configure Eclipse so that it uses Java 8
   1. Go to `Window > Preferences > Java > Compiler` and set the "Compiler compliance level" to 1.8.
   2. Go to `Window > Preferences > Java > Installed JREs`.  Go to "Add...", select "Standard VM", then select "Directory..." next to "JRE home" and browse to find the jdk1.8.0_xxx directory for the desired JDK.  Once selected, hit "Finish" and "Apply and Close".
4. To import jpf-core and jpf-symbc into Eclipse, go to ``File > Import > General > Existing Projects into Workspace`` and set "Select root directory" to the jpf directory that contains jpf-core and jpf-symbc.  Select jpf-core and jpf-symbc.
5. Set environment variables in Eclipse.  Go to `Run > Run Configurations...`. Under the "Java Application" dropdown, there should be several run configurations.  Select `run-JPF-symbc` and go to the Environment tab along the top.  
   1. If using Linux, then change the value of the variable `LD_LIBRARY_PATH` to /path/to/lib/directory/of/jpf-symbc/.
   2. If using Windows, then add the variable `PATH` and set its value to /path/to/lib/directory/of/jpf-symbc/.
   3. If using macOS, then add the variable `DYLD_LIBRARY_PATH` and set its value to /path/to/lib/directory/of/jpf-symbc/.
6. Open the jpf-symbc project in the package explorer of Eclipse.  Open src/examples.  
   1. Right click on a properties file, for example, ExampleChoco.jpf.  Select "Run as" and "Run Configurations..."  Select "Java Application" and "run-JPF-symbc" and hit "Run".
   2. Select a properties file, for example, ExampleChoco.jpf.  Click on the run button and select "run-JPF-symbc".

A video showing the above steps can be found at [YouTube](https://www.youtube.com/watch?v=zGVde_uU724).

## Using SPF

### Compile Java app

The Java app needs be be compiled with the debug flag -g.  For example, to compile the above class Example use
```
javac -g Example.java 
```

### Properties file

As we already mentioned above, to run SPF also a properties file is needed.  This file specifies how to run SPF.  It includes the fully qualified name of the Java app (target), the location where the bytecode of the app can be found (classpath), and the location where the Java code of the app can be found (sourcepath).  One can also specify which parameters of methods are concrete and which are symbolic.  For example,
```
symbolic.method = Example.min(con#sym)
```
specifies that the first parameter of the min method of the Example class is concrete, whereas the second one is symbolic.  Putting it altogether, we arrive at the following properties file, named, for example, Example.jpf.  (The name of the properties file should end with .jpf.)

```
# fully qualified name of the Java app
target = Example

# path to the bytecode of the target (and classes used by the target)
classpath = ${jpf-symbc}/build/examples/

# path to the Java code of the target (and classes used by the target)
sourcepath = ${jpf-symbc}/src/examples/

# method and its parameters
symbolic.method = Example.min(con#sym)
```

For more details, see the [Wiki of SPF](https://github.com/SymbolicPathFinder/jpf-symbc/wiki).

## Questions about SPF

If you have any questions about SPF, check the [JPF Google group](https://groups.google.com/g/java-pathfinder/).  If you cannot find the answer, post your question there.

## Contributing to SPF

First install JPF and SPF, as described above.  Next, run the examples found in the src/examples directory of jpf-symbc and its subdirectories.

### Tackle reported issues

Tackle one of the reported [issues](https://github.com/SymbolicPathFinder/jpf-symbc/issues/).

### Add tests

Add tests to the src/tests/ directory of jpf-symbc.

### Document code

Add javadoc comments to the Java code of jpf-symbc.
