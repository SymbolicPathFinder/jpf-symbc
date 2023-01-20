/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

package sequences;


import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.Preconditions;

/**
 *  Created by Tao Xie (xie@csc.ncsu.edu)
 *  With help from Corina S. Pasareanu (NASA JPF team; Corina.S.Pasareanu@nasa.gov)
 *  Mildly modified by Mithun Acharya.
 *  What's happening here?
 *  Clearly, the method testDriver is being executed symbolically, with symbolic arguments.
 *  Subsumption checking does not happen.
 *  Question is, are add, remove, and find also executed symbolically?
 *
 */

public class TaoSymbolicDriverForBST  {
  /*
  To run this driver, you need to configure your JPF command line arguments as
  +vm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory
  +vm.classpath=.
  +vm.storage.class=
  +symbolic.method=testDriver(sym#sym#sym#sym)
  +jpf.report.console.finished=
  +jpf.listener=gov.nasa.jpf.symbc.SymbolicListener
  TaoSymbolicDriverForBST

  Also see the FAQ in the end of this source file

  You may add "-Xmx1000M" as your VM argument to increase the memory allocation for JPF

  You shall see the following 15 generated test data being output from the console.

  testDriver(0,0,0,0)
  testDriver(0,0,1,0)
  testDriver(0,0,0,1)
  testDriver(0,1,0,0)
  testDriver(0,1,1,0)
  testDriver(0,1,0,1)
  testDriver(0,2,0,0)
  testDriver(0,2,1,0)
  testDriver(0,2,0,1)
  testDriver(1,0,0,0)
  testDriver(1,1,0,0)
  testDriver(1,2,0,0)
  testDriver(2,0,0,0)
  testDriver(2,1,0,0)
  testDriver(2,2,0,0)
  */


  /**
    * the following driver helps to generate method sequences of length 2 with exhaustive combination
    * of method sequences with symbolic arguments. The preconditions are important for helping the current JPF symbolic
    * execution engine to reduce time for the underlying Java-version constraint solver; Note that the ranges that you gave JPF
    * in preconditions shall be large enough so that the symbolic execution won't miss some important values to explore some paths.
    * you may add to update the preconditions when you try to change the driver for various situations. See FAQ below.
	*/

  @Preconditions("m1>=0&&m1<=2&&m2>=0&&m2<=2&&s1>=0&&s1<=2&&s2>=0&&s2<=2")

  public static void testDriver(int m1, int m2, int s1, int s2) {
	//mi indicates the **ith** method being invoked in the sequence
    //si indicates the symbolic argument value for the **ith** method in the sequence

    //NOTE: the reason for using integers as arguments for the test driver instead of int arrays because JPF symbolic
    //execution doesn't support turning an int array into a symbolic variable

    //NOTE: a property for the two arrays below is that they should have the same size, which means
    //you should have equal numbers of mi and si.
    int [] methodID = {m1, m2};
    //methodID[0], i.e., m1, indicates the method to be invoked as the first method in the sequence, ...
    //methodID[i], i.e., mi, indicates the method to be invoked as the ith method in the sequence
    int [] argValueID = {s1, s2};
    //argValueID[0], i.e., s1, indicates the method argument to be invoked as the argument of the first method in the sequence, ...
    //argValueID[i], i.e., si, indicates the method argument to be invoked as the argument of the ith method in the sequence
    //Here we assume that each method can have at most one method argument to be turned into symbolic.
    //For more method arguments of a method to be turned into symbolic, see FAQ below.

    BST b1 = new BST();
    System.out.println("BST just created... before loop...");
    for(int i=0; i<=(methodID.length-1); i++) {
	  //each loop iteration generates a method in a method sequence
	  //so the methodID.length determines how many methods you want to generate in a sequence

      switch(methodID[i]){
        case 0: {
          b1.add(argValueID[i]);
          break;
        }
        case 1: {
          b1.find(argValueID[i]);
          break;
        }
        default:{
          b1.remove(argValueID[i]);
          break;
        }
      }
    }
  }
  public static void main(String[] args) {
    testDriver(0, 0, 0, 0);
    Debug.printPC("TaoSymbolicDriverForBST.testDriver Path Condition: ");
    System.out.println();
  }
}

/*  FAQ
 *  Q: What if I want to generate sequences of length 3?
 *  A: The answer is for length 3 but you can generalize for any length i when i >= 3.
 *     You can follow the steps below
 *       (1) Add additional argument "int m3"
 *       (2) Add additional argument "int s3"
 *       (3) Add additional constraints for m3 and s3 in precondtions "m3>=0&&m3<=2&&s3>=0&&s3<=2"
 *       (4) Update the method call site of the driver in the main method
 *       (5) Update the command line parameter for reflecting the correct driver signature with additional #sym
 *           to be "+symbolic.method=testDriver(sym#sym#sym#sym#sym#sym)"
 *
 *  Q: What if one method under test (say, m2, to be used int the sequence) involves two integer arguments instead of two?
 *  A: The answer is for two integer arguments but your can generalize for any #int arguments i when i >=2.
 *      You can follow the steps below
 *       (1) Add additional arguments "int t1, int t2";
 *       (2) Add additional line "int [] secondArgValueID = {t1, t2};"
 *       (4) For the method with two arguments, invoke "b1.m2(argValueID[i], secondArgValueID[i]);"
 *       (5) Update the command line parameter for reflecting the correct driver signature with additional #sym
 *           to be "+symbolic.method=testDriver(sym#sym#sym#sym#sym#sym)"
 *
 *  Q: What if I want to test more than 3 methods (i.e., insert, find, and remove), say 4 methods including m4(int)?
 *  A: You add additional branch inside the loop before the last default else branch
   				} else if (methodID[i] == 2){
					b1.m4(argValueID[i]);//recall that argValueID[i] is the same as si
 *
 *
 *  Q: What if I want to generate JUnit exectuable unit test code from JPF output?
 *  A: The test driver is written in a way that it is quite easy for you to synthesize executable test code.
 *     JPF would output some strings like
 *       testDriver(0,2,0,1)
 *       ...
 *     You can write a simple tool to turn each of these lines into a JUnit test method like
 *        void test1() {
 *          TaoSymbolicDriverForBST.testDriver(0,2,0,1);
 *        }
 *     then you have a JUnit test suite!
 *     Remember to import the class of the test driver and the class under test in your generated JUnit test suite class.
 */

