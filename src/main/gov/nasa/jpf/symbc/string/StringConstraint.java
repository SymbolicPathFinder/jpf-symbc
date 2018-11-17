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
TERMINATION OF THIS AGREEMENT.

*/

package gov.nasa.jpf.symbc.string;

import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.visitors.CollectVariableVisitor;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class StringConstraint {
  StringExpression left;

  StringComparator comp;

  StringExpression right;

  StringConstraint and;

  StringConstraint(StringExpression l, StringComparator c, StringExpression r) {
    left = l;
    comp = c;
    right = r;
//    left.addRelationship(this);
//    right.addRelationship(this);
  }

  StringConstraint(StringComparator c, StringExpression r) {
	    left = null;
	    comp = c;
	    right = r;
//	    right.addRelationship(this);
	  }

    public StringConstraint(StringConstraint original) {
      left = original.left;
      comp = original.comp;
      right = original.right;
      if (original.and!= null){
        and = new StringConstraint(original.and);
      }
    }

  public Set<StringExpression> getOperands() {
    Set<StringExpression> operands = new HashSet<StringExpression>();
    operands.add(right);
    if (left != null) {
      operands.add(left);
    }
    return operands;
  }

  public String stringPC() {
	  if(left != null) {
		    return "(" +left.stringPC() + comp.toString() + right.stringPC() + ")"
		        + ((and == null) ? "" : " && " + and.stringPC());
		   } else {
			    return "(" +comp.toString() + right.stringPC() + ")"
		        + ((and == null) ? "" : " && " + and.stringPC());
		   }
  }

  public void getVarVals(Map<String, Object> varsVals) {
    if (left != null) {
      left.getVarsVals(varsVals);
    }
    if (right != null) {
      right.getVarsVals(varsVals);
    }
    if (and != null) {
      and.getVarVals(varsVals);
    }
  }

  public boolean equals(Object o) {

    if (!(o instanceof StringConstraint)) {
      return false;
    }

    boolean a = true;
    if(left != null) a = left.equals(((StringConstraint) o).left);

    boolean b = true;
    if(right != null) b = right.equals(((StringConstraint) o).right);

    return a && comp.equals(((StringConstraint) o).comp) && b;
  }

  public boolean contradicts(StringConstraint o) {
	if(left != null){
    return left.equals(o.left)
        && comp.equals(o.comp.not())
        && right.equals(o.right);
	} else {
		   return comp.equals(o.comp.not())
	        && right.equals(o.right);
	}
  }

  public int hashCode() {
	if (left != null)
     return left.hashCode() ^ comp.hashCode() ^ right.hashCode();
	else
     return comp.hashCode() ^ right.hashCode();
  }

  public String toString() {
   if(left != null) {
    return "(" + left.toString() + comp.toString() + right.toString() + ")"
        + ((and == null) ? "" : " && " + and.toString());
   } else {
	    return "(" + comp.toString() + right.toString() + ")"
        + ((and == null) ? "" : " && " + and.toString());
   }
  }
  
  public StringComparator getComparator() {
	  return comp;
  }
  
  public StringExpression getLeft () {
	  return left;
  }
  
  public StringExpression getRight () {
	  return right;
  }
  
  public StringConstraint and () {
	  return and;
  }
  
	public void accept(ConstraintExpressionVisitor visitor) {
		visitor.preVisit(this);
		left.accept(visitor);
		right.accept(visitor);
	    if (and!=null) and.accept(visitor);
			visitor.postVisit(this);
	}

  public StringConstraint not() {
      return new StringConstraint(getLeft(), getComparator().not(), getRight());
  }

	public void accept(CollectVariableVisitor visitor) {
		visitor.preVisit(this);
		left.accept(visitor);
		right.accept(visitor);
	    if (and!=null) and.accept(visitor);
			visitor.postVisit(this);
	}
}
