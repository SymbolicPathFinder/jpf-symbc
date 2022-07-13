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

> NOTE: It is strongly recommended to use Eclipse.

### Configuring Files

You can download jpf-core from one of the links below:
- https://github.com/corinus/jpf-core
- https://github.com/yannicnoller/jpf-core/tree/0f2f2901cd0ae9833145c38fee57be03da90a64f

And download jpf-symbc from here:
- https://github.com/SymbolicPathFinder/jpf-symbc

> Note: You can use `git clone <url>` to download the projects as git repositories

Put them in the same directory. In this example, we'll call the parent directory `spf-files`. It should look like this:

```
spf-files/
| jpf-core/
| jpf-symbc/
```

Create a new Eclipse workspace in the `spf-files` directory, then import `jpf-core` and `jpf-symbc` into the workspace as Java projects. To do this in Eclipse, go to `File > Import > General > Existing Projects into Workspace` and hit next. Select `spf-files` as the root directory, then select both projects to import and hit finish.

On Mac or Linux, create a `.jpf` directory in your home directory. On Windows, create it in your User folder (i.e. `C:\Users\<your username>\.jpf`). In `.jpf`, create a file called `site.properties` and add the following:

```
jpf-core = /path/to/.../jpf-core/
jpf-symbc = /path/to/.../jpf-symbc/

extensions = ${jpf-core}, ${jpf-symbc}
```

> **NOTE FOR WINDOWS USERS:** Instead of using `/` for the file path like above, or `\` like in Windows Explorer, you need to use `\\` (i.e. `C:\\Users\\<username>\\spf-files\\jpf-symbc`)

### Configuring Eclipse

We need to force Eclipse to use Java 8, as newer versions of Java are not yet supported. In Elcipse, go to `Window > Preferences > Java > Compiler` and set the "Compiler compliance level" to 1.8.

Next we need to tell Eclipse where to find the Java 8 JDK. Go to `Window > Preferences > Java > Installed JREs`. If you do not already have a Java 8 compliant JDK, then you will need to download one. Once you do, go to "Add...", select "Standard VM", then select "Directory..." next to "JRE home" and browse to find the `jre` directory for the desired JDK (i.e. `/path/to/jdk/.../jre`). Once selected, hit "Finish" and "Apply and Close".

Lastly, we need to point Eclipse to the necessary dependencies. Go to `Run > Run Configurations...`. Under the "Java Application" dropdown, there should be several run configurations. Select `run-JPF-symbc` and go to the Environment tab along the top. There should be two variables: `LD_LIBRARY_PATH` for Mac and Linux, and `PATH` for Windows. Change each to point to `jpf-symbc/lib` (i.e. `/path/to/.../jpf-symbc/lib`). Windows users should use `\\` as described above.

### Building and Running

Now you should be able to build the project successfully. In `Project > Clean`, check "Clean all projects" and hit "Clean". If that works, find an example `.jpf` file in `jpf-symbc/src/examples`. Right click on it and go to `Run As > Run Configurations...` in the popup menu, or click the file and go to `Run > Run Configurations...` in the Eclipse toolbar. Click `run-JPF-symbc`, hit "Run" in the bottom right, and you should see the example run without errors!

Have fun!
