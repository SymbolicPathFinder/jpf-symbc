#!/bin/bash

export JPF_HOME=/home/pcorina/workspace/javapathfinder-trunk

export JPF_CLASSPATH="\
${JPF_HOME}/build/jpf:\
${JPF_HOME}/build/env:\
${JPF_HOME}/build/env/jvm:\
${JPF_HOME}/build/env/jpf:\
${JPF_HOME}/build/examples:\
${JPF_HOME}/build/test:\
${JPF_HOME}/lib/bcel.jar:\
${JPF_HOME}/build-tools/lib/junit-4.3.jar:\
${JPF_HOME}/build-tools/lib/ant.jar:\
${JPF_HOME}/extensions/symbc/lib/choco-1_2_04.jar:\
${JPF_HOME}/extensions/symbc/lib/iasolver.jar:\
${JPF_HOME}/extensions/symbc/lib/libcvc3.jar"

export CLASSPATH=$CLASSPATH:$JPF_CLASSPATH:bin:lib/junit.jar

java -cp $CLASSPATH gov.nasa.jpf.JPF \
    +jpf.basedir=$JPF_HOME \
    +vm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory \
    +jpf.listener=gov.nasa.jpf.symbc.SymbolicListener \
    +vm.peer.packages=gov.nasa.jpf.symbc,gov.nasa.jpf.jvm \
    +symbolic.method=boxed\(sym#sym\),unboxed\(sym#sym\),customBoxed\(sym#sym\) \
    +symbolic.dp=choco \
    ExDarko



