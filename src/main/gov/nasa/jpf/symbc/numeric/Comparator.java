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

//
//Copyright (C) 2005 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc.numeric;

public enum Comparator {

   EQ(" = ") { public Comparator not() { return NE; }},
   NE(" != ") { public Comparator not() { return EQ; }},
   LT(" < ")  { public Comparator not() { return GE; }},
   LE(" <= ") { public Comparator not() { return GT; }},
   GT(" > ")  { public Comparator not() { return LE; }},
   GE(" >= ") { public Comparator not() { return LT; }};

   private final String str;

   Comparator(String str){
	   this.str= str;
   }
   
   public abstract Comparator not();
   
   @Override
   public String toString() {
	 return str;
   }

	/**
	 * Apply this comparator to the given operands.
	 * 
	 * @param left
	 *            the left operand
	 * @param right
	 *            the right operand
	 * @return <code>true</code> if and only if the operands satisfy this
	 *         comparator
	 */
	public boolean evaluate(double left, double right) {
		switch (this) {
		case EQ:
			return left == right;
		case NE:
			return left != right;
		case LT:
			return left < right;
		case LE:
			return left <= right;
		case GT:
			return left > right;
		case GE:
			return left >= right;
		default:
			return false;
		}
	}
}