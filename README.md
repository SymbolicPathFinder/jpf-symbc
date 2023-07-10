# Symbolic PathFinder (SPF)
![build SPF](https://github.com/gaurangkudale/SPF/actions/workflows/main.yml/badge.svg)

This JPF extension provides symbolic execution for Java bytecode. It performs a non-standard interpretation of byte-codes. It allows symbolic execution on methods with arguments of basic types (int, long, double, boolean, etc.). It also supports symbolic strings, arrays, and user-defined data structures.

<br>

## General Information about SPF
All the latest developments, changes, documentation can be found on our
[wiki](https://github.com/SymbolicPathFinder/jpf-symbc/wiki) page.

<br>

## Directory Structure of SPF
**The current directory structure is as follow.**

```{bash}
     SPF (Gradle Root Project)
        ---| jpf-core (Git-Submodule + Gradle Sub-Project)
        ---| jpf-symbc (Gradle Sub-Project)
```

As of August 2022, we migrated our build workflow to `Gradle`. While migrating the SPF to `Gradle`, we have introduced `Gradle Multi-Project build` and `GitHub Submodule` to SPF.

* **Gradle Multi-Project Build:** A multi-project build in Gradle consists of one root project, and one or more subprojects. In our case, `jpf-core` and `jpf-symbc` are two subprojects. More information can be found at the official documentation of [Gradle Multi-Project Build](https://docs.gradle.org/current/userguide/multi_project_builds.html).
 
* **Git-Submodule:** Git submodules allow you to keep a Git repository as a subdirectory of another Git repository. Git submodules are simply a reference to another repository at a particular snapshot in time. Git submodules enable a Git repository  to incorporate and track version history of external code. Git submodules are a powerful way to leverage Git as an external dependency management tool. More information can be found in its official documentation of [Git-Submodule](https://git-scm.com/docs/git-submodule).
 
<br>

## Quick Start Guide

SPF requires: **Java 8** and **Gradle 6.9**.

### 1. Get the latest SPF version
```{bash}
git clone --recurse-submodules git@github.com:SymbolicPathFinder/jpf-symbc.git
```
<details>
<summary>Console Output</summary>

```
yannic@Yannics-MacBook-Pro Desktop % git clone --recurse-submodules git@github.com:SymbolicPathFinder/jpf-symbc.git
Cloning into 'SPF'...
remote: Enumerating objects: 2438, done.
remote: Counting objects: 100% (611/611), done.
remote: Compressing objects: 100% (217/217), done.
remote: Total 2438 (delta 320), reused 585 (delta 306), pack-reused 1827
Receiving objects: 100% (2438/2438), 67.00 MiB | 2.89 MiB/s, done.
Resolving deltas: 100% (1257/1257), done.
Updating files: 100% (1042/1042), done.
Submodule 'jpf-core' (https://github.com/javapathfinder/jpf-core) registered for path 'jpf-core'
Cloning into '/Users/yannic/Desktop/SPF/jpf-core'...
remote: Enumerating objects: 3892, done.
remote: Counting objects: 100% (357/357), done.
remote: Compressing objects: 100% (208/208), done.
remote: Total 3892 (delta 114), reused 260 (delta 68), pack-reused 3535
Receiving objects: 100% (3892/3892), 2.27 MiB | 2.54 MiB/s, done.
Resolving deltas: 100% (1874/1874), done.
Submodule path 'jpf-core': checked out '45a4450cd0bd1193df5419f7c9d9b89807d00db6'
```
</details>

### 2. Build jpf-core
```{bash}
cd SPF
gradle :jpf-core:buildJars
```
<details>
<summary>Console Output</summary>

```{bash}
yannic@Yannics-MacBook-Pro SPF % gradle :jpf-core:buildJars
jpf-core
jpf-symbc

> Task :jpf-core:compileJava
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:21: warning: sun.misc.SharedSecrets is internal proprietary API and may be removed in a future release
import sun.misc.SharedSecrets;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:22: warning: sun.misc.JavaLangAccess is internal proprietary API and may be removed in a future release
import sun.misc.JavaLangAccess;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:85: warning: sun.misc.JavaLangAccess is internal proprietary API and may be removed in a future release
   static final JavaLangAccess JLA = SharedSecrets.getJavaLangAccess();
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:85: warning: sun.misc.SharedSecrets is internal proprietary API and may be removed in a future release
   static final JavaLangAccess JLA = SharedSecrets.getJavaLangAccess();
                                     ^
Note: /Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/choice/PermutationCG.java uses or overrides a deprecated API.
Note: Recompile with -Xlint:deprecation for details.
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.
4 warnings

> Task :jpf-core:compileClassesJava
/Users/yannic/Desktop/SPF/jpf-core/src/classes/java/lang/ClassLoader.java:29: warning: sun.misc.CompoundEnumeration is internal proprietary API and may be removed in a future release
import sun.misc.CompoundEnumeration;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/java/lang/ClassLoader.java:114: warning: sun.misc.CompoundEnumeration is internal proprietary API and may be removed in a future release
    return new CompoundEnumeration<URL>(resEnum);
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/JavaNetAccess.java:32: warning: sun.misc.URLClassPath is internal proprietary API and may be removed in a future release
    URLClassPath getURLClassPath (URLClassLoader ucl);
    ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:52: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
  private static JavaUtilJarAccess javaUtilJarAccess;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:60: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
  private static JavaOISAccess javaOISAccess;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:61: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
  private static JavaObjectInputStreamAccess javaObjectInputStreamAccess;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:82: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
  public static JavaUtilJarAccess javaUtilJarAccess() {
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:88: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
  public static void setJavaUtilJarAccess(JavaUtilJarAccess access) {
                                          ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:142: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
  public static JavaObjectInputStreamAccess getJavaObjectInputStreamAccess() {
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:151: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
  public static void setJavaObjectInputStreamAccess(JavaObjectInputStreamAccess access) {
                                                    ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:162: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
  public static void setJavaOISAccess(JavaOISAccess access) {
                                      ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:166: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
  public static JavaOISAccess getJavaOISAccess() {
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:175: warning: sun.misc.JavaObjectInputStreamReadString is internal proprietary API and may be removed in a future release
  public void setJavaObjectInputStreamReadString(sun.misc.JavaObjectInputStreamReadString ignored) {
                                                         ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/java/lang/System.java:64: warning: sun.misc.VM is internal proprietary API and may be removed in a future release
    sun.misc.VM.saveAndRemoveProperties(properties);
            ^
14 warnings

> Task :jpf-core:compilePeersJava
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:32: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
import sun.misc.Unsafe;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:93: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
  private static Unsafe unsafe;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:99: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
      Field singletonField = Unsafe.class.getDeclaredField("theUnsafe");
                             ^
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:101: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
      unsafe = (Unsafe)singletonField.get(null);
                ^
4 warnings

> Task :jpf-core:compileTestJava
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:34: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      Class<?> callerCls = sun.reflect.Reflection.getCallerClass(0); // that would be getCallerClass()
                                      ^
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:38: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      callerCls = sun.reflect.Reflection.getCallerClass(1); // foo()
                             ^
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:42: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      callerCls = sun.reflect.Reflection.getCallerClass(2); // bar()
                             ^
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:46: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      callerCls = sun.reflect.Reflection.getCallerClass(3); // callIt()
                             ^
Note: /Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java uses or overrides a deprecated API.
Note: Recompile with -Xlint:deprecation for details.
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.
4 warnings

Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
Use '--warning-mode all' to show the individual deprecation warnings.
See https://docs.gradle.org/6.9.2/userguide/command_line_interface.html#sec:command_line_warnings

BUILD SUCCESSFUL in 6s
15 actionable tasks: 15 executed
```
</details>

### 3. Build jpf-symbc
```{bash}
gradle :jpf-symbc:buildJars
```
<details>
<summary>Console Output</summary>

```
yannic@Yannics-MacBook-Pro SPF % gradle :jpf-symbc:buildJars
jpf-core
jpf-symbc

> Task :jpf-symbc:compileJava
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.

> Task :jpf-symbc:compileExamplesJava
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.

Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
Use '--warning-mode all' to show the individual deprecation warnings.
See https://docs.gradle.org/6.9.2/userguide/command_line_interface.html#sec:command_line_warnings

BUILD SUCCESSFUL in 7s
12 actionable tasks: 12 executed
```
</details>

### 4. Run Simple Example from the command line
*Inside the jpf-symbc folder, run the following command:*

```{bash}
cd jpf-symbc
java -Xmx1024m -ea -jar ../jpf-core/build/RunJPF.jar ./src/examples/demo/NumericExample.jpf
```

<details>
<summary>Console Output</summary>

```
yannic@Yannics-MacBook-Pro jpf-symbc % java -Xmx1024m -ea -jar ../jpf-core/build/RunJPF.jar ./src/examples/demo/NumericExample.jpf
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
JavaPathfinder core system v8.0 (rev c25d564ee76089e11adaa171137b2d7a2905e943) - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
demo.NumericExample.main()

====================================================== search started: 26/11/22 12:28 PM
Property Violated: PC is constraint # = 1
((a_1_SYMINT[-2147483648] + b_2_SYMINT[-2147483646]) - CONST_2) == CONST_0
Property Violated: result is  "java.lang.ArithmeticException: div by 0..."
****************************

====================================================== error 1
gov.nasa.jpf.vm.NoUncaughtExceptionsProperty
java.lang.ArithmeticException: div by 0
	at demo.NumericExample.test(NumericExample.java:26)
	at demo.NumericExample.main(NumericExample.java:34)


====================================================== snapshot #1
thread java.lang.Thread:{id:0,name:main,status:RUNNING,priority:5,isDaemon:false,lockCount:0,suspendCount:0}
  call stack:
	at demo.NumericExample.test(NumericExample.java:26)
	at demo.NumericExample.main(NumericExample.java:34)


====================================================== Method Summaries
Inputs: a_1_SYMINT,b_2_SYMINT

demo.NumericExample.test(-2147483648,-2147483646)  --> "java.lang.ArithmeticException: div by 0..."

====================================================== Method Summaries (HTML)
<h1>Test Cases Generated by Symbolic JavaPath Finder for demo.NumericExample.test (Path Coverage) </h1>
<table border=1>
<tr><td>a_1_SYMINT</td><td>b_2_SYMINT</td><td>RETURN</td></tr>
<tr><td>-2147483648</td><td>-2147483646</td><td>"java.lang.ArithmeticException: div by 0..."</td></tr>
</table>

====================================================== results
error #1: gov.nasa.jpf.vm.NoUncaughtExceptionsProperty "java.lang.ArithmeticException: div by 0  at demo.N..."

====================================================== statistics
elapsed time:       00:00:00
states:             new=3,visited=0,backtracked=3,end=0
search:             maxDepth=2,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=1
heap:               new=466,released=4,maxLive=0,gcCycles=1
instructions:       6308
max memory:         245MB
loaded code:        classes=85,methods=1648

====================================================== search finished: 26/11/22 12:28 PM
```
</details>


<!-- ### 6. Use SPF inside Eclipse
TODO -->

<br>

## Detailed Instructions and Suggestions
 
Please find below detailed instructions for installing and running SPF.
 
<details>
<summary><h2>System Requirements</h2></summary>
SPF is a pure Java Application and the minimal version is Java SE 8. We generally advise using the latest stable Java version 8 that is available for your platform.
You can determine your Java version by executing the following statement in the command line.

~~~~~~~~ {.bash}
> java -version
openjdk version "1.8.0_312"
OpenJDK Runtime Environment (Temurin)(build 1.8.0_312-b07)
OpenJDK 64-Bit Server VM (Temurin)(build 25.312-b07, mixed mode)
...
~~~~~~~~

### Java specifics for Windows
Make sure you have the JDK installed, otherwise there is no javac compiler available.
In order to build JPF from a Windows Command Prompt, you have to set the `JAVA_HOME` environment variable. 

### Java specifics for macOS
To switch to Java 8 on macOS, we recommend the following blog post: [https://medium.com/@devkosal/switching-java-jdk-versions-on-macos-80bc868e686a](https://medium.com/@devkosal/switching-java-jdk-versions-on-macos-80bc868e686a).

### Gradle (Build Automation Tool)

Make sure that you use [Gradle version 6.9](https://gradle.org/next-steps/?version=6.9&format=bin)! If you want to build the SPF source repositories, you need to install the Gradle. Please follow the [step by step installation guide for Gradle](https://docs.gradle.org/6.9/userguide/installation.html).

You can check your Gradle version by executing the following command in the command line:

```{bash}
> gradle -version
------------------------------------------------------------
Gradle 6.9.2
------------------------------------------------------------

Build time:   2021-12-21 20:18:38 UTC
Revision:     5d94aa68c0fdbe443838bb977080e3b9f273e889

Kotlin:       1.4.20
Groovy:       2.5.12
Ant:          Apache Ant(TM) version 1.10.9 compiled on September 27 2020
JVM:          1.8.0_312 (Temurin 25.312-b07)
OS:           Mac OS X 10.16 x86_64
```

If you are new to Gradle, check the [official website](https://docs.gradle.org/6.9/userguide/userguide.html) to learn the basics.
Note that all major IDEs (e.g., Netbeans, Eclipse, IntelliJ) come with Gradle support by default.
</details>

<details>
<summary><h2>Downloading sources from the GitHub repository</h2></summary>

SPF sources are kept in its main repository [https://github.com/SymbolicPathFinder/jpf-symbc](https://github.com/SymbolicPathFinder/jpf-symbc) within the [Symbolic PathFinder](https://github.com/SymbolicPathFinder) organization. There are two stable branches in our repository:

1. `ant-build`: It provides Java 8 support using the [Ant Build system](https://ant.apache.org).
2. `master`: Contains the latest stable version of our repository. In this version of SPF, we have introduced jpf-core as a git-submodule.

If you want to keep using Ant, consider using the `ant-build` branch. The branch `master` uses Gradle. To check out the SPF, it is recommended to fork the repository. Contributions are welcome, and we invite you to explore our [Java Pathfinder Google Group](https://groups.google.com/g/java-pathfinder). We also encourage you to check the following GitHub guides to familiarize yourself with the GitHub development workflow:

1. [Fork a Repo](https://help.github.com/articles/fork-a-repo/)
2. [About Pull Requests](https://help.github.com/articles/about-pull-requests/)

The following command shows you how to clone the repoistory along with the expected output:

```{bash}
git clone --recurse-submodules git@github.com:SymbolicPathFinder/jpf-symbc.git
```
<details>
<summary>Console Output</summary>

```
yannic@Yannics-MacBook-Pro Desktop % git clone --recurse-submodules git@github.com:SymbolicPathFinder/jpf-symbc.git
Cloning into 'SPF'...
remote: Enumerating objects: 2438, done.
remote: Counting objects: 100% (611/611), done.
remote: Compressing objects: 100% (217/217), done.
remote: Total 2438 (delta 320), reused 585 (delta 306), pack-reused 1827
Receiving objects: 100% (2438/2438), 67.00 MiB | 2.89 MiB/s, done.
Resolving deltas: 100% (1257/1257), done.
Updating files: 100% (1042/1042), done.
Submodule 'jpf-core' (https://github.com/javapathfinder/jpf-core) registered for path 'jpf-core'
Cloning into '/Users/yannic/Desktop/SPF/jpf-core'...
remote: Enumerating objects: 3892, done.
remote: Counting objects: 100% (357/357), done.
remote: Compressing objects: 100% (208/208), done.
remote: Total 3892 (delta 114), reused 260 (delta 68), pack-reused 3535
Receiving objects: 100% (3892/3892), 2.27 MiB | 2.54 MiB/s, done.
Resolving deltas: 100% (1874/1874), done.
Submodule path 'jpf-core': checked out '45a4450cd0bd1193df5419f7c9d9b89807d00db6'
```
</details>
</details>

<details>
<summary><h2>Building, Testing, Running</h2></summary>

### Building SPF using the Command Line

Requirements: **Java 8** and **Gradle 6.9**.

**Note:** 

* On Ubuntu, the `command apt-get install gradle` seems to install an older version of gradle (version 2.x) which is incompatible with the project and causes unzipping errors. Hence, it is recommended to visit the [Official Gradle installation guide](https://docs.gradle.org/6.9/userguide/installation.html) for installing the 6.9 version of gradle.

* Instead of using the `gradle` command, you may want to use the gradle wrapper `gradlew` instead. The SPF repository includes a Gradle wrapper that requires nothing except Java to execute. It ensures that all JPF developers and environments use the same builder to avoid any kind of configuration issue.

### Step 1: Build jpf-core

```{bash}
cd SPF
gradle :jpf-core:buildJars
```
<details>
<summary>Console Output</summary>

```{bash}
yannic@Yannics-MacBook-Pro SPF % gradle :jpf-core:buildJars
jpf-core
jpf-symbc

> Task :jpf-core:compileJava
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:21: warning: sun.misc.SharedSecrets is internal proprietary API and may be removed in a future release
import sun.misc.SharedSecrets;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:22: warning: sun.misc.JavaLangAccess is internal proprietary API and may be removed in a future release
import sun.misc.JavaLangAccess;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:85: warning: sun.misc.JavaLangAccess is internal proprietary API and may be removed in a future release
   static final JavaLangAccess JLA = SharedSecrets.getJavaLangAccess();
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:85: warning: sun.misc.SharedSecrets is internal proprietary API and may be removed in a future release
   static final JavaLangAccess JLA = SharedSecrets.getJavaLangAccess();
                                     ^
Note: /Users/yannic/Desktop/SPF/jpf-core/src/main/gov/nasa/jpf/vm/choice/PermutationCG.java uses or overrides a deprecated API.
Note: Recompile with -Xlint:deprecation for details.
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.
4 warnings

> Task :jpf-core:compileClassesJava
/Users/yannic/Desktop/SPF/jpf-core/src/classes/java/lang/ClassLoader.java:29: warning: sun.misc.CompoundEnumeration is internal proprietary API and may be removed in a future release
import sun.misc.CompoundEnumeration;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/java/lang/ClassLoader.java:114: warning: sun.misc.CompoundEnumeration is internal proprietary API and may be removed in a future release
    return new CompoundEnumeration<URL>(resEnum);
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/JavaNetAccess.java:32: warning: sun.misc.URLClassPath is internal proprietary API and may be removed in a future release
    URLClassPath getURLClassPath (URLClassLoader ucl);
    ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:52: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
  private static JavaUtilJarAccess javaUtilJarAccess;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:60: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
  private static JavaOISAccess javaOISAccess;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:61: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
  private static JavaObjectInputStreamAccess javaObjectInputStreamAccess;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:82: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
  public static JavaUtilJarAccess javaUtilJarAccess() {
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:88: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
  public static void setJavaUtilJarAccess(JavaUtilJarAccess access) {
                                          ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:142: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
  public static JavaObjectInputStreamAccess getJavaObjectInputStreamAccess() {
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:151: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
  public static void setJavaObjectInputStreamAccess(JavaObjectInputStreamAccess access) {
                                                    ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:162: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
  public static void setJavaOISAccess(JavaOISAccess access) {
                                      ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:166: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
  public static JavaOISAccess getJavaOISAccess() {
                ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/sun/misc/SharedSecrets.java:175: warning: sun.misc.JavaObjectInputStreamReadString is internal proprietary API and may be removed in a future release
  public void setJavaObjectInputStreamReadString(sun.misc.JavaObjectInputStreamReadString ignored) {
                                                         ^
/Users/yannic/Desktop/SPF/jpf-core/src/classes/java/lang/System.java:64: warning: sun.misc.VM is internal proprietary API and may be removed in a future release
    sun.misc.VM.saveAndRemoveProperties(properties);
            ^
14 warnings

> Task :jpf-core:compilePeersJava
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:32: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
import sun.misc.Unsafe;
               ^
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:93: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
  private static Unsafe unsafe;
                 ^
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:99: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
      Field singletonField = Unsafe.class.getDeclaredField("theUnsafe");
                             ^
/Users/yannic/Desktop/SPF/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:101: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
      unsafe = (Unsafe)singletonField.get(null);
                ^
4 warnings

> Task :jpf-core:compileTestJava
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:34: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      Class<?> callerCls = sun.reflect.Reflection.getCallerClass(0); // that would be getCallerClass()
                                      ^
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:38: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      callerCls = sun.reflect.Reflection.getCallerClass(1); // foo()
                             ^
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:42: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      callerCls = sun.reflect.Reflection.getCallerClass(2); // bar()
                             ^
/Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:46: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
      callerCls = sun.reflect.Reflection.getCallerClass(3); // callIt()
                             ^
Note: /Users/yannic/Desktop/SPF/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java uses or overrides a deprecated API.
Note: Recompile with -Xlint:deprecation for details.
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.
4 warnings

Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
Use '--warning-mode all' to show the individual deprecation warnings.
See https://docs.gradle.org/6.9.2/userguide/command_line_interface.html#sec:command_line_warnings

BUILD SUCCESSFUL in 6s
15 actionable tasks: 15 executed
```
</details>

### Step 2: Build jpf-symbc

```{bash}
gradle :jpf-symbc:buildJars
```
<details>
<summary>Console Output</summary>

```
yannic@Yannics-MacBook-Pro SPF % gradle :jpf-symbc:buildJars
jpf-core
jpf-symbc

> Task :jpf-symbc:compileJava
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.

> Task :jpf-symbc:compileExamplesJava
Note: Some input files use unchecked or unsafe operations.
Note: Recompile with -Xlint:unchecked for details.

Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
Use '--warning-mode all' to show the individual deprecation warnings.
See https://docs.gradle.org/6.9.2/userguide/command_line_interface.html#sec:command_line_warnings

BUILD SUCCESSFUL in 7s
12 actionable tasks: 12 executed
```
</details>


<!--
```{bash}
> cd SPF
> ./gradlew :jpf-core:buildJars
     jpf-core
     jpf-symbc

     Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
     Use '--warning-mode all' to show the individual deprecation warnings.
     See https://docs.gradle.org/6.9/userguide/command_line_interface.html#sec:command_line_warnings

     BUILD SUCCESSFUL in 2s
     15 actionable tasks: 2 executed, 13 up-to-date

> ./gradlew :jpf-symbc:buildJars
     jpf-core
     jpf-symbc

     > Task :jpf-symbc:compileJava
     Note: Some input files use unchecked or unsafe operations.
     Note: Recompile with -Xlint:unchecked for details.

     > Task :jpf-symbc:compileExamplesJava
     Note: Some input files use unchecked or unsafe operations.
     Note: Recompile with -Xlint:unchecked for details.

     Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
     Use '--warning-mode all' to show the individual deprecation warnings.
     See https://docs.gradle.org/6.9/userguide/command_line_interface.html#sec:command_line_warnings

     BUILD SUCCESSFUL in 20s
     12 actionable tasks: 12 executed   
```
-->

In the following, there is a summary of the main build tasks.
If you want to have some help about what other tasks are available, check the command `gradle tasks --all`.

```
SPF Build tasks
---------------
> gradle :jpf-symbc:buildJars - Generates all core JPF jar files.
> gradle :jpf-symbc:compile - Compiles all JPF core sources.

SPF Distribution tasks
----------------------
> gradle :jpf-symbc:dist - Builds binary distribution.
> gradle :jpf-symbc:srcDist - Builds the source distribution.

Verification tasks
------------------
> gradle :jpf-symbc:test - Runs core regression tests.
```

### Step 3: Run SPF Tests
```{bash}
gradle :jpf-symbc:test
```
<details>
<summary>Console Output</summary>

```{bash}
yannic@Yannics-MacBook-Pro SPF % gradle :jpf-symbc:test
jpf-core
jpf-symbc

> Task :jpf-symbc:test

gov.nasa.jpf.symbc.TestSymbolicJPF > testISUB_oneConcrete PASSED

gov.nasa.jpf.symbc.TestSymbolicJPF > testIADD_bothSymbolic PASSED

gov.nasa.jpf.symbc.TestSymbolicJPF > testISUB_bothSymbolic PASSED

gov.nasa.jpf.symbc.TestSymbolicJPF > testIADD_oneConcrete PASSED

gov.nasa.jpf.symbc.TestIntStatic1 > mainTest PASSED

gov.nasa.jpf.symbc.TestTermination > mainTest PASSED

gov.nasa.jpf.symbc.TestFCMPLConditions > mainTest PASSED

gov.nasa.jpf.symbc.TestFloatVirtual1 > mainTest PASSED

gov.nasa.jpf.symbc.TestBooleanSpecial1 > mainTest PASSED

gov.nasa.jpf.symbc.TestDCMPLConditions > mainTest PASSED

gov.nasa.jpf.symbc.TestBooleanVirtual1 > mainTest PASSED

gov.nasa.jpf.symbc.TestFloatSpecial1 > mainTest PASSED

gov.nasa.jpf.symbc.TestInvokeSTATICandVIRTUAL > mainTest PASSED

gov.nasa.jpf.symbc.TestLCMPConditions > mainTest PASSED

gov.nasa.jpf.symbc.TestIntSpecial1 > mainTest PASSED

gov.nasa.jpf.symbc.TestDoubleStatic1 > mainTest PASSED

gov.nasa.jpf.symbc.TestFloatStatic1 > mainTest PASSED

gov.nasa.jpf.symbc.TestIntVirtual1 > mainTest PASSED

gov.nasa.jpf.symbc.TestSymbc > testSymbcDriver PASSED

gov.nasa.jpf.symbc.TestMethodInvocation > mainTest PASSED

gov.nasa.jpf.symbc.TestDoubleSpecial1 > mainTest PASSED

gov.nasa.jpf.symbc.TestBooleanStatic1 > mainTest PASSED

gov.nasa.jpf.symbc.TestDoubleVirtual1 > mainTest PASSED

gov.nasa.jpf.symbc.TestSwitch > mainTest PASSED
Test Execution: SUCCESS
Summary: 24 tests, 24 passed, 0 failed, 0 skipped

Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
Use '--warning-mode all' to show the individual deprecation warnings.
See https://docs.gradle.org/6.9.2/userguide/command_line_interface.html#sec:command_line_warnings

BUILD SUCCESSFUL in 21s
13 actionable tasks: 6 executed, 7 up-to-date
```
</details>

### Step 4: Run Simple Example from the Command Line
*Inside the jpf-symbc folder, run the following command:*

```{bash}
cd jpf-symbc
java -Xmx1024m -ea -jar ../jpf-core/build/RunJPF.jar ./src/examples/demo/NumericExample.jpf
```

<details>
<summary>Console Output</summary>

```
yannic@Yannics-MacBook-Pro jpf-symbc % java -Xmx1024m -ea -jar ../jpf-core/build/RunJPF.jar ./src/examples/demo/NumericExample.jpf
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
JavaPathfinder core system v8.0 (rev c25d564ee76089e11adaa171137b2d7a2905e943) - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
demo.NumericExample.main()

====================================================== search started: 26/11/22 12:28 PM
Property Violated: PC is constraint # = 1
((a_1_SYMINT[-2147483648] + b_2_SYMINT[-2147483646]) - CONST_2) == CONST_0
Property Violated: result is  "java.lang.ArithmeticException: div by 0..."
****************************

====================================================== error 1
gov.nasa.jpf.vm.NoUncaughtExceptionsProperty
java.lang.ArithmeticException: div by 0
	at demo.NumericExample.test(NumericExample.java:26)
	at demo.NumericExample.main(NumericExample.java:34)


====================================================== snapshot #1
thread java.lang.Thread:{id:0,name:main,status:RUNNING,priority:5,isDaemon:false,lockCount:0,suspendCount:0}
  call stack:
	at demo.NumericExample.test(NumericExample.java:26)
	at demo.NumericExample.main(NumericExample.java:34)


====================================================== Method Summaries
Inputs: a_1_SYMINT,b_2_SYMINT

demo.NumericExample.test(-2147483648,-2147483646)  --> "java.lang.ArithmeticException: div by 0..."

====================================================== Method Summaries (HTML)
<h1>Test Cases Generated by Symbolic JavaPath Finder for demo.NumericExample.test (Path Coverage) </h1>
<table border=1>
<tr><td>a_1_SYMINT</td><td>b_2_SYMINT</td><td>RETURN</td></tr>
<tr><td>-2147483648</td><td>-2147483646</td><td>"java.lang.ArithmeticException: div by 0..."</td></tr>
</table>

====================================================== results
error #1: gov.nasa.jpf.vm.NoUncaughtExceptionsProperty "java.lang.ArithmeticException: div by 0  at demo.N..."

====================================================== statistics
elapsed time:       00:00:00
states:             new=3,visited=0,backtracked=3,end=0
search:             maxDepth=2,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=1
heap:               new=466,released=4,maxLive=0,gcCycles=1
instructions:       6308
max memory:         245MB
loaded code:        classes=85,methods=1648

====================================================== search finished: 26/11/22 12:28 PM
```
</details>

### Step 5: Try `Z3´ as constraint solver

#### → Change configuration `./src/examples/demo/NumericExample.jpf` to use z3

```bash
target=demo.NumericExample
classpath=${jpf-symbc}/build/examples
sourcepath=${jpf-symbc}/src/examples
symbolic.method = demo.NumericExample.test(sym#sym)

symbolic.dp=z3
listener = .symbc.SymbolicListener

search.multiple_errors=true
```

Then, the execution of:

`java -Xmx1024m -ea -jar ../jpf-core/build/RunJPF.jar ./src/examples/demo/NumericExample.jpf`

will result in an **error**: `java.lang.UnsatisfiedLinkError: no libz3java in java.library.path`

<details>
<summary>Full Error Stack Trace</summary>

```bash
java.lang.UnsatisfiedLinkError: no libz3java in java.library.path
	at java.lang.ClassLoader.loadLibrary(ClassLoader.java:1860)
	at java.lang.Runtime.loadLibrary0(Runtime.java:871)
	at java.lang.System.loadLibrary(System.java:1124)
	at com.microsoft.z3.Native.<clinit>(Native.java:14)
	at com.microsoft.z3.Context.<init>(Context.java:59)
	at gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3$Z3Wrapper.<init>(ProblemZ3.java:75)
	at gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3$Z3Wrapper.getInstance(ProblemZ3.java:69)
	at gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3.<init>(ProblemZ3.java:95)
	at gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral.isSatisfiable(SymbolicConstraintsGeneral.java:98)
	at gov.nasa.jpf.symbc.numeric.PathCondition.simplifyOld(PathCondition.java:393)
	at gov.nasa.jpf.symbc.numeric.PathCondition.simplify(PathCondition.java:340)
	at gov.nasa.jpf.symbc.bytecode.IDIV.execute(IDIV.java:121)
	at gov.nasa.jpf.vm.ThreadInfo.executeInstruction(ThreadInfo.java:1908)
	at gov.nasa.jpf.vm.ThreadInfo.executeTransition(ThreadInfo.java:1859)
	at gov.nasa.jpf.vm.SystemState.executeNextTransition(SystemState.java:765)
	at gov.nasa.jpf.vm.VM.forward(VM.java:1722)
	at gov.nasa.jpf.search.Search.forward(Search.java:579)
	at gov.nasa.jpf.search.DFSearch.search(DFSearch.java:79)
	at gov.nasa.jpf.JPF.run(JPF.java:613)
	at gov.nasa.jpf.JPF.start(JPF.java:189)
	at sun.reflect.NativeMethodAccessorImpl.invoke0(Native Method)
	at sun.reflect.NativeMethodAccessorImpl.invoke(NativeMethodAccessorImpl.java:62)
	at sun.reflect.DelegatingMethodAccessorImpl.invoke(DelegatingMethodAccessorImpl.java:43)
	at java.lang.reflect.Method.invoke(Method.java:498)
	at gov.nasa.jpf.tool.Run.call(Run.java:80)
	at gov.nasa.jpf.tool.RunJPF.main(RunJPF.java:116)
```
</details>

#### → Solution: Set the right java library path to the lib folder where the z3 native libraries are located

- macOS:
    - Key: `DYLD_LIBRARY_PATH`
    - Value: /Users/yannic/repositories/jpf-symbc/lib
- Linux:
    - Key: `LD_LIBRARY_PATH`
- Windows:
    - Key: `PATH`
    
For example for macOS, the command would look like this:

```{bash}
DYLD_LIBRARY_PATH=/Users/yannic/repositories/jpf-symbc/lib/ \
  /Library/Java/JavaVirtualMachines/temurin-8.jdk/Contents/Home/bin/java \
    -Xmx1024m -ea \
    -jar ../jpf-core/build/RunJPF.jar \
    src/examples/demo/NumericExample.jpf
```

<details>
<summary>Successful Console Output</summary>
    
```{bash}
yannic@Yannics-MacBook-Pro jpf-symbc % DYLD_LIBRARY_PATH=/Users/yannic/repositories/jpf-symbc/lib/ \
  /Library/Java/JavaVirtualMachines/temurin-8.jdk/Contents/Home/bin/java \
    -Xmx1024m -ea \
    -jar ../jpf-core/build/RunJPF.jar \
    src/examples/demo/NumericExample.jpf
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
JavaPathfinder core system v8.0 (rev fdd5cf06c743ad8a8a58fdb1c1ea0d77075985e3) - (C) 2005-2014 United States Government. All rights reserved.


====================================================== system under test
demo.NumericExample.main()

====================================================== search started: 26/11/22 1:53 PM
>0
<=0
Property Violated: PC is constraint # = 1
((a_1_SYMINT[2] + b_2_SYMINT[0]) - CONST_2) == CONST_0
Property Violated: result is  "java.lang.ArithmeticException: div by 0..."
****************************

====================================================== error 1
gov.nasa.jpf.vm.NoUncaughtExceptionsProperty
java.lang.ArithmeticException: div by 0
	at demo.NumericExample.test(NumericExample.java:26)
	at demo.NumericExample.main(NumericExample.java:34)


====================================================== snapshot #1
thread java.lang.Thread:{id:0,name:main,status:RUNNING,priority:5,isDaemon:false,lockCount:0,suspendCount:0}
  call stack:
	at demo.NumericExample.test(NumericExample.java:26)
	at demo.NumericExample.main(NumericExample.java:34)


====================================================== Method Summaries
Inputs: a_1_SYMINT,b_2_SYMINT

demo.NumericExample.test(-2147483648,-2147483648)  --> Return Value: --
demo.NumericExample.test(0,3)  --> Return Value: --
demo.NumericExample.test(2,0)  --> "java.lang.ArithmeticException: div by 0..."

====================================================== Method Summaries (HTML)
<h1>Test Cases Generated by Symbolic JavaPath Finder for demo.NumericExample.test (Path Coverage) </h1>
<table border=1>
<tr><td>a_1_SYMINT</td><td>b_2_SYMINT</td><td>RETURN</td></tr>
<tr><td>-2147483648</td><td>-2147483648</td><td>Return Value: --</td></tr>
<tr><td>0</td><td>3</td><td>Return Value: --</td></tr>
<tr><td>2</td><td>0</td><td>"java.lang.ArithmeticException: div by 0..."</td></tr>
</table>

====================================================== results
error #1: gov.nasa.jpf.vm.NoUncaughtExceptionsProperty "java.lang.ArithmeticException: div by 0  at demo.N..."

====================================================== statistics
elapsed time:       00:00:00
states:             new=5,visited=0,backtracked=5,end=2
search:             maxDepth=3,constraints=0
choice generators:  thread=1 (signal=0,lock=1,sharedRef=0,threadApi=0,reschedule=0), data=2
heap:               new=470,released=22,maxLive=446,gcCycles=3
instructions:       6330
max memory:         245MB
loaded code:        classes=85,methods=1648

====================================================== search finished: 26/11/22 1:53 PM
```
</details>

<!--
### Step 6: Use SPF inside Eclipse
TODO
-->
<summary><h2>Building, Testing, Running Using Docker</h2></summary>


This Dockerfile sets up an Ubuntu-based Docker image with OpenJDK 8, Gradle, dos2unix, and Git installed. It provides a convenient environment for building and running Java projects using Gradle.

## Usage

### Building the Docker Image

1. Clone or download this repository to your local machine.

2. Navigate to the directory containing the Dockerfile and the project files.

3. Build the Docker image using the following command:

   ```shell
   docker build -t spf:latest .
   ```
   <summary>Successful Console Output</summary>
    
```{bash}
C:\Users\gaura\SPF>docker build -t spf:latest .
[+] Building 6.8s (13/13) FINISHED
 => [internal] load build definition from Dockerfile                                                                                                   0.0s
 => => transferring dockerfile: 32B                                                                                                                    0.0s
 => [internal] load .dockerignore                                                                                                                      0.0s
 => => transferring context: 2B                                                                                                                        0.0s
 => [internal] load metadata for docker.io/library/ubuntu:latest                                                                                       2.0s
 => [internal] load build context                                                                                                                      0.7s
 => => transferring context: 473.37kB                                                                                                                  0.7s
 => [1/8] FROM docker.io/library/ubuntu:latest@sha256:0bced47fffa3361afa981854fcabcd4577cd43cebbb808cea2b1f33a3dd7f508                                 0.0s
 => CACHED [2/8] RUN apt-get update &&     apt-get install -y openjdk-8-jdk &&     apt-get install -y unzip wget &&     apt-get clean                  0.0s
 => CACHED [3/8] RUN apt-get update && apt-get install -y dos2unix && apt-get clean                                                                    0.0s
 => CACHED [4/8] RUN apt-get install -y git                                                                                                            0.0s
 => CACHED [5/8] RUN wget -q https://services.gradle.org/distributions/gradle-6.9-bin.zip &&     unzip -q gradle-6.9-bin.zip -d /opt &&     rm gradle  0.0s
 => CACHED [6/8] WORKDIR /app                                                                                                                          0.0s
 => [7/8] COPY . .                                                                                                                                     1.5s
 => [8/8] RUN dos2unix /app/entrypoint.sh && chmod +x /app/entrypoint.sh                                                                               0.4s
 => exporting to image                                                                                                                                 2.0s
 => => exporting layers                                                                                                                                2.0s
 => => writing image sha256:5060595607f86ab471899a000a45e73e726658e07ca7da920093f65f3b2449d3                                                           0.0s
 => => naming to docker.io/library/spf:latest                                                                                                          0.0s

Use 'docker scan' to run Snyk tests against images to find vulnerabilities and learn how to fix them
```
5. Run the Docker container using the following command:
   ```shell
   docker run spf:latest
   ```
 <summary>Successful Console Output</summary>
 
    ```shell
   		
	Welcome to Gradle 6.9!
	
	Here are the highlights of this release:
	- This is a small backport release.
	- Java 16 can be used to compile when used with Java toolchains
	- Dynamic versions can be used within plugin declarations
	- Native support for Apple Silicon processors
	
	For more details see https://docs.gradle.org/6.9/release-notes.html
	
	
	------------------------------------------------------------
	Gradle 6.9
	------------------------------------------------------------
	
	Build time:   2021-05-07 07:28:53 UTC
	Revision:     afe2e24ababc7b0213ccffff44970aa18035fc0e
	
	Kotlin:       1.4.20
	Groovy:       2.5.12
	Ant:          Apache Ant(TM) version 1.10.9 compiled on September 27 2020
	JVM:          1.8.0_362 (Private Build 25.362-b09)
	OS:           Linux 5.15.79.1-microsoft-standard-WSL2 amd64
	
	Running the current working dir cmd...
	/app
	Running the Gradle build cmd for JPF-CORE...
	Starting a Gradle Daemon (subsequent builds will be faster)
	jpf-core
	jpf-symbc
	
	> Task :jpf-core:compileJava
	/app/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:21: warning: sun.misc.SharedSecrets is internal proprietary API and may be removed in a future release
	import sun.misc.SharedSecrets;
	       ^
	/app/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:22: warning: sun.misc.JavaLangAccess is internal proprietary API and may be removed in a future release
	import sun.misc.JavaLangAccess;
	       ^
	/app/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:85: warning: sun.misc.JavaLangAccess is internal proprietary API and may be removed in a future release
	static final JavaLangAccess JLA = SharedSecrets.getJavaLangAccess();
		^
	/app/jpf-core/src/main/gov/nasa/jpf/vm/HashedAllocationContext.java:85: warning: sun.misc.SharedSecrets is internal proprietary API and may be removed in a future release
	static final JavaLangAccess JLA = SharedSecrets.getJavaLangAccess();
				     ^
	Note: /app/jpf-core/src/main/gov/nasa/jpf/vm/choice/PermutationCG.java uses or overrides a deprecated API.
	Note: Recompile with -Xlint:deprecation for details.
	Note: Some input files use unchecked or unsafe operations.
	Note: Recompile with -Xlint:unchecked for details.
	4 warnings
	
	> Task :jpf-core:compileClassesJava
	/app/jpf-core/src/classes/java/lang/ClassLoader.java:29: warning: sun.misc.CompoundEnumeration is internal proprietary API and may be removed in a future release
	import sun.misc.CompoundEnumeration;
	       ^
	/app/jpf-core/src/classes/java/lang/ClassLoader.java:114: warning: sun.misc.CompoundEnumeration is internal proprietary API and may be removed in a future release
	return new CompoundEnumeration<URL>(resEnum);
	       ^
	/app/jpf-core/src/classes/java/lang/System.java:64: warning: sun.misc.VM is internal proprietary API and may be removed in a future release
	sun.misc.VM.saveAndRemoveProperties(properties);
	    ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:52: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
	private static JavaUtilJarAccess javaUtilJarAccess;
		 ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:60: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
	private static JavaOISAccess javaOISAccess;
		 ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:61: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
	private static JavaObjectInputStreamAccess javaObjectInputStreamAccess;
		 ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:82: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
	public static JavaUtilJarAccess javaUtilJarAccess() {
		^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:88: warning: sun.misc.JavaUtilJarAccess is internal proprietary API and may be removed in a future release
	public static void setJavaUtilJarAccess(JavaUtilJarAccess access) {
					  ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:142: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
	public static JavaObjectInputStreamAccess getJavaObjectInputStreamAccess() {
		^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:151: warning: sun.misc.JavaObjectInputStreamAccess is internal proprietary API and may be removed in a future release
	public static void setJavaObjectInputStreamAccess(JavaObjectInputStreamAccess access) {
						    ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:162: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
	public static void setJavaOISAccess(JavaOISAccess access) {
				      ^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:166: warning: sun.misc.JavaOISAccess is internal proprietary API and may be removed in a future release
	public static JavaOISAccess getJavaOISAccess() {
		^
	/app/jpf-core/src/classes/sun/misc/SharedSecrets.java:175: warning: sun.misc.JavaObjectInputStreamReadString is internal proprietary API and may be removed in a future release
	public void setJavaObjectInputStreamReadString(sun.misc.JavaObjectInputStreamReadString ignored) {
							 ^
	/app/jpf-core/src/classes/sun/misc/JavaNetAccess.java:32: warning: sun.misc.URLClassPath is internal proprietary API and may be removed in a future release
	URLClassPath getURLClassPath (URLClassLoader ucl);
	^
	14 warnings
	
	> Task :jpf-core:compilePeersJava
	/app/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:32: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
	import sun.misc.Unsafe;
	       ^
	/app/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:93: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
	private static Unsafe unsafe;
		 ^
	/app/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:99: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
	Field singletonField = Unsafe.class.getDeclaredField("theUnsafe");
			     ^
	/app/jpf-core/src/peers/gov/nasa/jpf/vm/JPF_java_util_Random.java:101: warning: sun.misc.Unsafe is internal proprietary API and may be removed in a future release
	unsafe = (Unsafe)singletonField.get(null);
		^
	4 warnings
	
	> Task :jpf-core:compileTestJava
	/app/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:34: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
	Class<?> callerCls = sun.reflect.Reflection.getCallerClass(0); // that would be getCallerClass()
				      ^
	/app/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:38: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
	callerCls = sun.reflect.Reflection.getCallerClass(1); // foo()
			     ^
	/app/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:42: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
	callerCls = sun.reflect.Reflection.getCallerClass(2); // bar()
			     ^
	/app/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java:46: warning: sun.reflect.Reflection is internal proprietary API and may be removed in a future release
	callerCls = sun.reflect.Reflection.getCallerClass(3); // callIt()
			     ^
	Note: /app/jpf-core/src/tests/gov/nasa/jpf/test/vm/reflection/ReflectionTest.java uses or overrides a deprecated API.
	Note: Recompile with -Xlint:deprecation for details.
	Note: Some input files use unchecked or unsafe operations.
	Note: Recompile with -Xlint:unchecked for details.
	4 warnings
	
	Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
	Use '--warning-mode all' to show the individual deprecation warnings.
	See https://docs.gradle.org/6.9/userguide/command_line_interface.html#sec:command_line_warnings
	
	BUILD SUCCESSFUL in 47s
	15 actionable tasks: 15 executed
	Running the Gradle build cmd for JPF-SYMBC...
	jpf-core
	jpf-symbc
	
	> Task :jpf-symbc:compileJava
	POM relocation to an other version number is not fully supported in Gradle : xml-apis:xml-apis:2.0.2 relocated to xml-apis:xml-apis:1.0.b2.
	Please update your dependency to directly use the correct version 'xml-apis:xml-apis:1.0.b2'.
	Resolution will only pick dependencies of the relocated element.  Artifacts and other metadata will be ignored.
	Note: Some input files use unchecked or unsafe operations.
	Note: Recompile with -Xlint:unchecked for details.
	
	> Task :jpf-symbc:compileExamplesJava
	Note: Some input files use unchecked or unsafe operations.
	Note: Recompile with -Xlint:unchecked for details.
	
	Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
	Use '--warning-mode all' to show the individual deprecation warnings.
	See https://docs.gradle.org/6.9/userguide/command_line_interface.html#sec:command_line_warnings
	
	BUILD SUCCESSFUL in 1m 9s
	12 actionable tasks: 12 executed
	Run SPF Tests
	jpf-core
	jpf-symbc
	
	> Task :jpf-symbc:test
	
	gov.nasa.jpf.symbc.TestMethodInvocation > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestSymbolicJPF > testISUB_oneConcrete PASSED
	
	gov.nasa.jpf.symbc.TestSymbolicJPF > testIADD_bothSymbolic PASSED
	
	gov.nasa.jpf.symbc.TestSymbolicJPF > testISUB_bothSymbolic PASSED
	
	gov.nasa.jpf.symbc.TestSymbolicJPF > testIADD_oneConcrete PASSED
	
	gov.nasa.jpf.symbc.TestFloatVirtual1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestFCMPLConditions > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestBooleanVirtual1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestIntStatic1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestFloatStatic1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestBooleanStatic1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestIntSpecial1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestBooleanSpecial1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestSymbc > testSymbcDriver PASSED
	
	gov.nasa.jpf.symbc.TestLCMPConditions > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestDoubleSpecial1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestDoubleStatic1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestSwitch > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestDCMPLConditions > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestTermination > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestIntVirtual1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestInvokeSTATICandVIRTUAL > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestFloatSpecial1 > mainTest PASSED
	
	gov.nasa.jpf.symbc.TestDoubleVirtual1 > mainTest PASSED
	Test Execution: SUCCESS
	Summary: 24 tests, 24 passed, 0 failed, 0 skipped
	
	Deprecated Gradle features were used in this build, making it incompatible with Gradle 7.0.
	Use '--warning-mode all' to show the individual deprecation warnings.
	See https://docs.gradle.org/6.9/userguide/command_line_interface.html#sec:command_line_warnings
	
	BUILD SUCCESSFUL in 23s
	13 actionable tasks: 6 executed, 7 up-to-date
	Keep container running
    ```
   
</details>
