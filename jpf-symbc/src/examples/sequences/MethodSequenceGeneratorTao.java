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


import gov.nasa.jpf.JPF;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.Preconditions;
import java.lang.reflect.*;
import java.text.*;
import java.util.Random;

import gov.nasa.jpf.vm.Verify;

/**
 * @author Mithun Acharya
 * Loosely based on TaoSymbolicDriverForBST
 * Tried to remove the necessity to enumerate m1, m2... and s1, s2, ... in TaoSymbolicDriverForBST
 * Currently, no reflection
 * Currently, its only for BST.
 */
public class MethodSequenceGeneratorTao {

  // Constructor
  public MethodSequenceGeneratorTao(){
  }

  // Name of the class for which method sequences are to be generated
  private String className;
  // Number of public methods
  private int numPublicMethods;
  // sequence length?
  private int sequenceLength = 0;
  // range
  private int range = 0;

  // public methods in the class
  // currently not used - public methods can be obtained through reflection
  private Method[] publicMethods;

  public void invokeMethodSequenceDriver(String _className, int _numPublicMethods, int _sequenceLength, int _range){
	className = _className;
	numPublicMethods = _numPublicMethods;
    sequenceLength = _sequenceLength;
    range = _range;

    // Here you can use Java reflection to
    // (1) get all public methods
    // (2) get the number of parameters for each public methods
    // (3) ...
    //
    //
    // OR
    //
    // if the user annotates the methods of interest, or explicitly specifies the methods
    // of interest then reflection is not required
    //

    // Reflection
    /*
    try {
      // from the class name get the actual class
      Class c = Class.forName(className);
      // get all public methods
      publicMethods = c.getDeclaredMethods();
      for (int i = 0; i < publicMethods.length; i++)
        System.out.println(publicMethods[i].toString());
    }
    catch (Throwable e) {
      System.err.println(e);
    }
    */
    // Once you get all the information about the class, you can
    // call the methodSequenceDriver, which will be executed with symbolic arguments


    // does not really matter what you pass to methodSequenceDriver.
    // It is executed symbolically anyways
    methodSequenceDriver(0, 0);
  }

  /*
   * Converts the decimalNumber to base-b with numDigits digits and stores it in array digitsArray
   */
  public static void shred(int decimalNumber, int[] digitsArray, int b, int numDigits){
	  int quotient = 1;
	  int remainder = 0;
	  int count = 0;

	  // Start shredding
	  quotient = decimalNumber;
	  for (int i = 0; i<numDigits; i++){
		  count = 0;
		  while(quotient >= b){
			  count++;
			  quotient = quotient - b;
		  }
		  remainder = quotient;
		  quotient = count;
		  digitsArray[i] = remainder;
	  }
  }


  // precondition currently hardcoded
  // numSequences < P^S and input < R^P
  @Preconditions("numSequences>=0&&numSequences<27&&input>=0&&input<27")
  /**
   * methodSequenceDriver is executed symbolically
   * the arrays numSequencesDigits and inputDigits depend on the
   * parameters numSequences and input
   *
   * let P = numPublicMethods, S = sequenceLength, and R = range
   * then numSequences = P^S and input = R^P
   *
   * So numSequences is converted to base-P with S digits and input is converted to base-R with P digits
   *
   * We assume the input value is picked from the range specified in Preconditions annotation
   *
   */
  public void methodSequenceDriver(int numSequences, int input) {
    // loop counters
    int i;

    BST b = new BST();

    int[] numSequencesDigits = new int[sequenceLength];
    int[] inputDigits = new int[range];

    int P, R, S;
    P = numPublicMethods;
    S = sequenceLength;
    R = range;

    // Shred numSequences
    // Convert to base-P with S digits
    shred(numSequences, numSequencesDigits, P, S);

    // Shred input
    // Convert to base-R with P digits
    shred(input, inputDigits, R, P);

    for (i=0; i<sequenceLength; i++){
      // Currently 0, 1, 2... are hardcoded
      // the number of options should be equal to number of public methods
      switch(numSequencesDigits[i]){
	    case 0: {
		  b.add(inputDigits[0]);
		  break;
		}
		case 1: {
		  b.find(inputDigits[1]);
		  break;
		}
		case 2: {
		  b.remove(inputDigits[2]);
		}
      }
    }
  }
}