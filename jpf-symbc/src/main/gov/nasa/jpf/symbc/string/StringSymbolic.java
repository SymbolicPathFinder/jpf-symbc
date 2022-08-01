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

/*  Copyright (C) 2005 United States Government as represented by the
Administrator of the National Aeronautics and Space Administration
(NASA).  All Rights Reserved.

Copyright (C) 2009 Fujitsu Laboratories of America, Inc.

DISCLAIMER OF WARRANTIES AND LIABILITIES; WAIVER AND INDEMNIFICATION

A. No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY
WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY,
INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE
WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM
INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR
FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO
THE SUBJECT SOFTWARE. NO SUPPORT IS WARRANTED TO BE PROVIDED AS IT IS PROVIDED "AS-IS".

B. Waiver and Indemnity: RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS
AGAINST FUJITSU LABORATORIES OF AMERICA AND ANY OF ITS AFFILIATES, THE
UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL
AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE
RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING
FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING
FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY
AND HOLD HARMLESS FUJITSU LABORATORTIES OF AMERICA AND ANY OF ITS AFFILIATES,
THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL
AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE
REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL
TERMINATION OF THIS AGREEMENT. */

package gov.nasa.jpf.symbc.string;

import java.util.Map;

import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;

public class StringSymbolic extends StringExpression {

  public static final String UNDEFINED = "**UNDEFINED**";
  public String solution = UNDEFINED;
  public static String SYM_STRING_SUFFIX = "_SYMSTRING";
  private String name;
  private IntegerExpression length;

  public StringSymbolic() {
	   super();

	   StringPathCondition.flagSolved = false;
  }

  public StringSymbolic(String n) {
    super();
    name = n;
    length = new SymbolicInteger(name + ".length");
	trackedSymVars.add(fixName(name));
	StringPathCondition.flagSolved=false;
  }

  public StringSymbolic clone() {
	  String newName = new String(this.name);
	  return new StringSymbolic(newName);
  }

  public String toString() {
	   if (!StringPathCondition.flagSolved) {
		      return (name != null) ? name : "STR_" + hashCode();
		    } else {
		      return (name != null) ? name + "[" + solution + "]" : "STR_" + hashCode()
		          + "[" + solution + "]";
		    }
  }

	public String stringPC () {
		if (!StringPathCondition.flagSolved) {
			return (name != null) ? name : "STR_" + hashCode();

		} else {
			return (name != null) ? name + "[" + solution + "]" :
				"STR_" + hashCode() + "[" + solution + "]";
		}
	}

	   public void getVarsVals(Map<String,Object> varsVals) {
	    	varsVals.put(fixName(name), solution);
	    }

	   public String fixName(String name) {
	    	if (name.endsWith(SYM_STRING_SUFFIX)) {
	    		name = name.substring(0, name.lastIndexOf(SYM_STRING_SUFFIX));
	    	}
	    	return name;
	    }

	   public IntegerExpression ___length() {
		    return length;
		  }

		public String getName() {
			return (name != null) ? name : "STRING_" + hashCode();
		}

	  public String solution() {
	    return solution;
	  }

	@Override
	public void accept(ConstraintExpressionVisitor visitor) {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

}