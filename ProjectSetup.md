# Overview
This document provides a detailed guide to setting up and building the SPF project on the sv-comp branch. 
* Required tools 
* Step-by-step instructions for setup
* Troubleshooting solutions for common issues encountered during the build process.

## Required Tools
* Java Development Kit (JDK) 8: JDK 11 is not supported with the current SPF version.
  - [Download JDK 8, Recommended Java SE Development Kit 8u321](https://www.oracle.com/eg/java/technologies/javase/javase8u211-later-archive-downloads.html)
  -  [How to install JDK](https://www.youtube.com/watch?v=Qtua8t20dA4)
* Gradle 6.9.2: Recommended for compatibility with the current SPF version.
  - [Download Gradle](https://gradle.org/releases/)
  - [How to install Gradle](https://www.youtube.com/watch?v=2RUX3JS4FWQ)

## Setup Instructions
1. Clone the repository:
Clone the repository with the [sv-comp](https://github.com/SymbolicPathFinder/jpf-symbc/tree/sv-comp) branch (please note this branch may change based on contributions).
```
git clone https://github.com/SymbolicPathFinder/jpf-symbc.git
```
2. Download jpf-core:
Ensure you download jpf-core for compatibility with spf as jpf-core is the core framework that jpf-symbc relies on:
``` 
git clone https://github.com/SymbolicPathFinder/jpf-core.git
```
3. Add jpf-core into SPF folder: (it will be as the following folder): ![SPF Folder](https://github.com/user-attachments/assets/4b0d5da6-a37b-462f-bfe1-c3dc4791be58)
Move the  directory into the SPF directory. After this step, your SPF folder structure will look like this:
```
SPF/
├── jpf-core/
├── ...
```

4. Build the project:
Navigate to the SPF folder in your terminal:
```
cd SPF
```

Run the following command to build the project:

```
gradle build
```

You will show the following screen:
![Testing](https://github.com/user-attachments/assets/55e27db9-95da-461d-890d-e2b24fe1c59c)

5. Run SPF on IntelliJ IDEA: press Run and SPF will be successful Run!
![SPF Running by IntelliJ IDEA](https://github.com/user-attachments/assets/81d19b0b-4aea-4424-9747-040bd69f7d63)


## Troubleshooting Build Failure
1. Unsupported Java Version
  - Cause: The project requires JDK 8, but if a different version (e.g., JDK 11 or higher JDK 8) is installed, you will face the following when you build SPF:![Java 11 failed](https://github.com/user-attachments/assets/e721b421-fbb1-454d-a14c-cdba4d389777)
  - Solution: Check the installed Java version: ``` java -version ``` and download JDK 8
2. Unsupported Gradle Version for some functions
  - Cause: Gradle version 6.9 is incompatible with the project setup, you will face the following when you build SPF:![Gradle Issue](https://github.com/user-attachments/assets/52a3b6aa-ac61-4de3-9c53-ded8b779cd2e)
    as well as Versions 7 and higher does not support some required functions like Gradle 6.9.2 does.
  - Solution: Verify the Gradle version: ``` gradle -version ```
  - Update **all** project’s **gradle-wrapper.properties** files to ensure it uses version 6.9.2: ``` distributionUrl=https\://services.gradle.org/distributions/gradle-6.9.2-all.zip ```

