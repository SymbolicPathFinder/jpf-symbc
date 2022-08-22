# Symbolic PathFinder SPF
![build main-gk](https://github.com/gaurangkudale/SPF/actions/workflows/main.yml/badge.svg)

This JPF extension provides symbolic execution for Java bytecode. It performs a non-standard interpretation of byte-codes. It allows symbolic execution on methods with arguments of basic types (int, long, double, boolean, etc.). It also supports symbolic strings, arrays, and user-defined data structures.


## General Information about JPF
All the latest developments, changes, documentation can be found on our
[wiki](https://github.com/SymbolicPathFinder/jpf-symbc/wiki) page.


## Directory Structure of SPF
**The current directory structure is as follow.**

```{bash}
     SPF (Gradle Root Project)
        ---| jpf-core (Git-Submodule + Gradle Sub-Project)
        ---| jpf-symbc (Gradle Sub-Project)
```

As of Augest 2022, we are migrating our build workflow to `Gradle`, While migrating the SPF to `Gradle` we have introduced `Gradle Multi-Project build` and `GitHub Submodule` to the SPF.

* `Gradle Multi-Project Build :-` A multi-project build in Gradle consists of one root project, and one or more subprojects. In our case `jpf-core` and `jpf-symbc` are two subprojects.
 The more information about gradle multi-project build can be found at official documentation of 
 [Gradle Multi-Project Build](https://docs.gradle.org/current/userguide/multi_project_builds.html) page.
 
 * `Git-Submodule :-` Git submodules allow you to keep a git repository as a subdirectory of another git repository. Git submodules are simply a reference to another repository at a particular snapshot in time. Git submodules enable a Git repository  to incorporate and track version history of external code. Git submodules are a powerful way to leverage git as an external dependency management tool.
 The more information about Git-Submodule can be found at official documentation of
 [Git-Submodule](https://git-scm.com/docs/git-submodule) page.
 
 
 ## Building and Installing
 
 If you are having problems installing and running JPF, please look at the 
 [How to install SPF]()  guide.
