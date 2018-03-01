#!/bin/sh -v

#compile the Java class
javac Bessel.java

# Generate a C header file
javah -jni Bessel

gcc -c -m64 concolic_BesselImp.c

gcc -m64 -dynamiclib concolic_BesselImp.o -o libCJavaInterface.dylib

# Set the search path for shared libraries
export LD_LIBRARY_PATH=.

# Run the Java program
java Bessel 1.0
