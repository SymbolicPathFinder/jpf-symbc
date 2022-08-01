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

// Copyright (C) 2007 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//
package gov.nasa.jpf.symbc.sequences;

import gov.nasa.jpf.vm.ChoiceGenerator;



/**
* @author pcorina
*
*/

// I propose the following
// create a new choice generator that records the names of the methods that are executed
// symbolically + the concrete parameters and the symbolic values
// (in an array or something like that)
// it will not make any choices, but it will force JPF to remember this info on the current path
// so that it is easy to reconstruct and print it
// then we will not really need any more maps to print the information
public class SequenceChoiceGenerator extends gov.nasa.jpf.vm.choice.IntIntervalGenerator {

  private String methodShortName;
  private Object [] argValues;
  private Object [] attributes;
  
  @Override
  public ChoiceGenerator randomize() {
      // This doesn't make choices anyway, no need to change.
      return this;
  }
  
  // will always make only one choice
@SuppressWarnings("deprecation")
public SequenceChoiceGenerator(String _methodShortName) {
      super(0, 0);
      methodShortName = _methodShortName;
  }


  public Object [] getArgValues() {
      return argValues;
  }

  public void setArgValues(Object [] _argValues) {
      argValues = _argValues;;
  }

  public Object [] getArgAttributes() {
      return attributes;
  }

  public void setArgAttributes(Object [] _attributes) {
      attributes = _attributes;
  }

  public String getMethodShortName() {
	return methodShortName;
  }

}