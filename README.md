# Symbolic PathFinder SPF
![build main-gk](https://github.com/gaurangkudale/SPF/actions/workflows/main.yml/badge.svg)

This JPF extension provides symbolic execution for Java bytecode. It performs a non-standard interpretation of byte-codes. It allows symbolic execution on methods with arguments of basic types (int, long, double, boolean, etc.). It also supports symbolic strings, arrays, and user-defined data structures.
***

* ## General Information about SPF
All the latest developments, changes, documentation can be found on our
[wiki](https://github.com/SymbolicPathFinder/jpf-symbc/wiki) page.


* ## Directory Structure of SPF
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
 ***
 
 
 * ## Building and Installing
 
 Instructions for installing and running SPF, please look at the following guide.
 
 <details close>
 <summary> <b> Step : 1 Click Here for System Requirments </b></summary>
 SPF is a pure Java Application, The minimal version is Java SE 8. We generally advise using the latest stable Java version 8 that is available for your platform.
 
 You can find out about your java by running the following statement from the command line.

~~~~~~~~ {.bash}
> java -version
java version "1.8.0_341"
Java(TM) SE Runtime Environment (build 1.8.0_341-b10)
Java HotSpot(TM) 64-Bit Server VM (build 25.341-b10, mixed mode)
...
~~~~~~~~

* ### Java specifics for Windows ###
Make sure you have the JDK installed, otherwise there is no javac compiler available.

In order to build JPF from a Windows Command Prompt, you have to set the `JAVA_HOME` environment variable. 

* ### Java specifics for OS X ###
On Mac OS X 10.10, Java 1.7 is default, but `/Applications/Utilities/Java Preferences.app` can change the setting. In some cases, it may be necessary to manually change the symlink that determines which version is default:

~~~~~~~~ {.bash}
sudo rm /System/Library/Frameworks/JavaVM.framework/Versions/Current
sudo ln -s 1.8 /System/Library/Frameworks/JavaVM.framework/Versions/Current
~~~~~~~~

* ## Gradle (Build Automation Tool) ##

* To download the Gradle version 6.9 from [ClickHere](https://gradle.org/next-steps/?version=6.9&format=bin)

If you want to build the SPF source repositories, you need to install the Gradle,
[click Here for Step by step installation guide for Gradle](https://docs.gradle.org/6.9/userguide/installation.html) 

You can check if you have Gradle version 6.9 on your machine with the following command:

```{bash}
> gradle -version
------------------------------------------------------------
Gradle 6.9
------------------------------------------------------------

Build time:   2021-05-07 07:28:53 UTC
Revision:     afe2e24ababc7b0213ccffff44970aa18035fc0e

Kotlin:       1.4.20
Groovy:       2.5.12
Ant:          Apache Ant(TM) version 1.10.9 compiled on September 27 2020
JVM:          1.8.0_341 (Oracle Corporation 25.341-b10)
OS:           Windows 11 10.0 amd64
```

**Note : Please use Gradle version 6.9 which is supported for SPF**

If you are new to Gradle, check the [official website](https://docs.gradle.org/6.9/userguide/userguide.html) to learn the basics.
Note that all major IDEs (e.g., Netbeans, Eclipse, IntelliJ) comes with Gradle support by default.



* ## Git (Version Control System) ##

If you want to download the JPF source repositories, you need to install the [Git](https://git-scm.com/downloads) distributed version control system on your machine. Most Unix platforms come with Git installed. You can check if you have Git on your machine with the following command:

```{bash}
> git --version
```

If you are new to Git, check the [official website](https://git-scm.com/) to learn the basics. You can also find some GUI Clients for different platforms.
Note that all major IDEs (e.g., Netbeans, Eclipse, IntelliJ) comes with Git support by default.

For more information about Git and how to use it to clone the repository, refer to the [Downloading Sources](https://github.com/javapathfinder/jpf-core/wiki/Downloading-sources) page.
***


</details>
<details close>
<summary> <b> Step 2 : Downloading sources from the GitHub repositories </b> </summary>
SPF sources are kept as https://github.com/SymbolicPathFinder repositories on GitHub within the [Symbolic PathFinder](https://github.com/SymbolicPathFinder). You need to clone the repository (e.g. https://github.com/gaurangkudale/SPF/tree/main-gk) that you are interested in.

There are two stable branches in our repository:
1. `java-8-ant`: It provides Java 8 support using the Ant Build system.
2. `master`: Contains the latest stable version of our repository. In this version of SPF, We have introduced jpf-core as a git-submodule

If you want to keep using Ant, consider using the `java-8-ant` branch. The branch `master` will drop Ant support to switch to Gradle.

Feel free to fork the desired repository. Contributions are welcome, and we invite you to subscribe to our mailing list: java-pathfinder@googlegroups.com

We also encourage you to check the following GitHub guides to familiarize yourself with the GitHub development workflow:

1. [Fork a Repo](https://help.github.com/articles/fork-a-repo/)
2. [About Pull Requests](https://help.github.com/articles/about-pull-requests/)

* ## Command Line Access ##


#### Getting the source files

To check out the SPF, it is recommended to fork the repository.


> If you only want to download the project, you can just download the repository content as a zip file.
> On the repository page, click on the `Clone or Download` button, and proceed with `Download as ZIP`.


When you fork a GitHub repository, you create a copy of the project in your GitHub account.
Then, use the git command `clone` to check out your forked repository in your local machine.

> In the following example, we use SSH but you can also use HTTPS. Note that you will have to use your
> username and password when using HTTPS. See the [Connecting to GitHub with SSH](https://help.github.com/articles/connecting-to-github-with-ssh/) guide for more info.


~~~~~~~~ {.bash}
> cd ~/projects

> git clone --recurse-submodules https://github.com/gaurangkudale/SPF.git -b main-gk
Cloning into 'SPF'...
remote: Enumerating objects: 2408, done.
remote: Counting objects: 100% (581/581), done.
remote: Compressing objects: 100% (297/297), done.
Receiving objects: 100% (2408/2408), 66.90 MiB | 344.00 KiB/sreused 1827
Receiving objects: 100% (2408/2408), 66.99 MiB | 145.00 KiB/s, done.
Resolving deltas: 100% (1229/1229), done.
Updating files: 100% (1042/1042), done.
Submodule 'jpf-core' (https://github.com/javapathfinder/jpf-core) registered for path 'jpf-core'
Cloning into 'C:/Users/gaura/Desktop/SPF Wiki/jpf-symbc.wiki/SPF/jpf-core'...
remote: Enumerating objects: 3873, done.
remote: Counting objects: 100% (338/338), done.
remote: Compressing objects: 100% (196/196), done.
remote: Total 3873 (delta 108), reused 245 (delta 63), pack-reused 3535
Receiving objects: 100% (3873/3873), 2.26 MiB | 1002.00 KiB/s, done.
Resolving deltas: 100% (1868/1868), done.
~~~~~~~~

* #### Synchronizing your forked repository with our main repository

When you have a forked repository, it will not update git-submodule automatically when the original repository updates.
To keep your forked repository synchronized, proceed with the following steps:

1. Add a reference to our main repository

~~~~~~~~ {.bash}
> cd ~/SPF
> git remote add upstream https://github.com/gaurangkudale/SPF
~~~~~~~~

2. Use the git command `pull` to fetch and merge the changes from `upstream` into your local repository

~~~~~~~~ {.bash}
> git pull upstream master

~~~~~~~~

Now, your local repostory is synchronized, but you need to update your remote (forked repository on GitHub) repository.

3. Use the git command `push` to submit the local changes:


~~~~~~~~ {.bash}
> git push origin master
~~~~~~~~

4. To update git sub-module use following command:

~~~~~~~~ {.bash}
>  git submodule update --init --recursive
>  git submodule foreach --recursive git fetch
>  git submodule foreach git merge origin master
~~~~~~~~

If you want to contribute to the project, you must make changes in your local repository and push them to your forked remote repository. In this situation, your remote repository is ahead of ours, and you must **create a pull request**. For more info, please, check the [Creating a Pull Request](https://help.github.com/articles/creating-a-pull-request/) guide.
***


</details>
<details close>
<summary> <b> Step 3 : Building, Testing, Runing </b> </summary>

## Building SPF

### Using the command line

The SPF repository includes a Gradle wrapper that requires nothing except Java to execute. It ensures that all JPF developers and environments use the same builder to avoid any kind of configuration issue.
Note that we assume that `./gradle` is used below, which installs a local copy of version 6.9. If you use your own version of Gradle, make sure it is version 6.9 or below.

**Note:** On Ubuntu, the `command apt-get install gradle` seems to install an older version of gradle (version 2.x) which is incompatible with the project and causes unzipping errors. Hence, it is recommended to visit the [Official Gradle installation guide](https://docs.gradle.org/6.9/userguide/installation.html) for installing the 6.9 version of gradle.


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

In the following, there is a summary of the main build tasks.
If you want to have some help about what other tasks are available, check the command `./gradlew tasks --all`.

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

## Running SPF ##

### Using the command line ###

~~~~~~~~ {.bash}
> cd SPF
> 
** NOTE : ADD EXAMPLE **
~~~~~~~~








