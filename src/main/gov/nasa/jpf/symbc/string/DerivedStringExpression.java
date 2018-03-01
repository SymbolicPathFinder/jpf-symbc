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

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.Expression;

public class DerivedStringExpression extends StringExpression {

  public StringExpression left;
  public StringOperator op;
  public StringExpression right;
  
  public Expression[] oprlist;

  DerivedStringExpression(StringExpression l, StringOperator o, StringExpression r) {
	oprlist = null;
    left = l;
    op = o;
    right = r;
//    left.addDependent(this);
//    right.addDependent(this); 
  }
  
  DerivedStringExpression(StringOperator o, Expression[] olist) {
	  left = null;
	  right = null;
	  op = o;
	  int i = olist.length;
	  oprlist = new Expression[i];
	  for(int j = 0; j < i; j++){
		  oprlist[j] = olist[j];
//		  if(olist[j] instanceof StringExpression){
//			  ((StringExpression) oprlist[j]).addDependent(this);
//		  }
	  }
  }
  
  DerivedStringExpression(StringOperator o, StringExpression r) {
	    left = null;
	    op = o;
	    right = r;
//	    right.addDependent(this); 
	  }
  
    public DerivedStringExpression clone() {
	  throw new RuntimeException("Operation not implemented");
  }

  public Set<Expression> getOperands() {
    Set<Expression> operands = new HashSet<Expression>();
    if (right != null) {
      operands.add(right);
    }
    if (left != null) {
      operands.add(left);
    }
    if (oprlist != null) {
      for (Expression e : oprlist) {
        operands.add(e);
      }
    }
    return operands;
  }

  //TODO: add solution() cases for all supported operators
  public String solution() {
	  String l;
    if(left != null) 
    	l = left.solution();
    else
    	l = new String();
    String r = right.solution();
    switch (op) {
      case CONCAT:
        return l.concat(r);
      case TRIM:
    	  return right.solution();
      default:
        throw new RuntimeException(
            "## Error: BinaryStringSolution solution: l " + l + " op " + op
                + " r " + r);
    }
  }

  public void getVarsVals(Map<String, Object> varsVals) {
	if(left != null) left.getVarsVals(varsVals);
    right.getVarsVals(varsVals);
  }

  public String stringPC() {
	if (left != null)
        return left.stringPC() + "." + op.toString() + "(" + right.stringPC() + ")";
	else if (right != null)
		return "." + op.toString() + "(" + right.stringPC() + ")";
	else 
	{
		StringBuilder s = new StringBuilder();
		   s.append("{");
		for(int i = 0; i < oprlist.length; i++){	
			s.append("(");			
			s.append(oprlist[i].toString());
			s.append(")");				
		}
		   s.append("}");	
		return "." + op.toString() + s;
		
	}
  }

  public String toString() {
		if (left != null)	  
            return left.toString() + "." + op.toString() + "(" + right.toString() + ")";
		else if (right != null)
			return "." + op.toString() + "(" + right.toString() + ")";
		else 
		{
			StringBuilder s = new StringBuilder();
			   s.append("[");
			for(int i = 0; i < oprlist.length; i++){	
				s.append("(");			
				s.append(oprlist[i].toString());
				s.append(")");				
			}
			    s.append("]");	
			return "." + op.toString() + s;			
		}
				
  }
  	
  public String getName() {
    String name;
    if (left != null)
      name = left.getName() + "_" + op.toString() + "__" + right.getName()
          + "___";
    else if (right != null)
      name = "_" + op.toString() + "__" + right.getName() + "___";
    else {
      StringBuilder s = new StringBuilder();
      s.append("__");
      for (int i = 0; i < oprlist.length; i++) {
        s.append("__");
        if (oprlist[i] instanceof StringExpression) {
          s.append(((StringExpression)oprlist[i]).getName());
        } else {
          s.append(oprlist[i].toString());
        }
        s.append("___");
      }
      s.append("___");
      name = "_" + op.toString() + s;
    }

    return "STRING_" + name;
  }

	@Override
	public void accept(ConstraintExpressionVisitor visitor) {
		visitor.preVisit(this);
		left.accept(visitor);
		right.accept(visitor);
		visitor.postVisit(this);
	}
  
}

