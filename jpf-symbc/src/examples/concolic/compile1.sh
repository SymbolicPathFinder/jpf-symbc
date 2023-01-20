#!/bin/sh -v

# This script will compile and run example 1.
# This script assumes that Java is installed in /usr/java/j2sdk1.4.0_02
# (modify if not), and that the Java bin directory is in your PATH.
# It also assumes that you have gcc and ld in your PATH.

# Compile the Java class
javac Bessel.java

# Generate a C header file
javah -jni Bessel

# Compile the implementation of the C interface to the Bessel function
gcc -c -I/usr/java/j2sdk1.4.0_02/include \
       -I/usr/java/j2sdk1.4.0_02/include/linux concolic_BesselImp.c

# Convert it to a shared library
ld -G concolic_BesselImp.o -o libCJavaInterface.so -lm -lc -lpthread

# Set the search path for shared libraries
export LD_LIBRARY_PATH=.

# Run the Java program
java Bessel 1.0
