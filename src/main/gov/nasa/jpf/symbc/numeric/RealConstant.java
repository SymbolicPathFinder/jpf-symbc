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

import java.util.Map;


public class RealConstant extends RealExpression {
  public double value;

  public RealConstant (double i) {
    value = i;
  }

  public RealExpression _minus (double i) {
		//simplify
	  if (i == 0)
		  return this;

    return new RealConstant(value - i);
  }

  public RealExpression _minus (RealExpression e) {
		//simplify
		if (e instanceof RealConstant) {
			RealConstant rc = (RealConstant)e;
			if (rc.value == 0)
				return this;
		}
		if (e == this)
			return new RealConstant(0);

    if (e instanceof RealConstant) {
      return new RealConstant(value - ((RealConstant) e).value);
    } else {
      return super._minus(e);
    }
  }

  public RealExpression _mul (double i) {
      //simplify
	  if (i == 1)
		  return this;
	  if (i == 0)
		  return new RealConstant(0);

    return new RealConstant(value * i);
  }

  public RealExpression _mul (RealExpression e) {
		//simplify
		if (e instanceof RealConstant) {
			RealConstant rc = (RealConstant)e;
			if (rc.value == 1)
				return this;
			if (rc.value == 0)
				return new RealConstant(0);
		}

    if (e instanceof RealConstant) {
      return new RealConstant(value * ((RealConstant) e).value);
    } else {
      return super._mul(e);
    }
  }

  public RealExpression _plus (double i) {
      //simplify
	  if (i == 0)
		  return this;

	  return new RealConstant(value + i);
  }

  public RealExpression _plus (RealExpression e) {
		//simplify
		if (e instanceof RealConstant) {
			RealConstant ic = (RealConstant)e;
			if (ic.value == 0)
				return this;
		}

    if (e instanceof RealConstant) {
      return new RealConstant(value + ((RealConstant) e).value);
    } else {
      return super._plus(e);
    }
  }

  public RealExpression _div (double i) {
	    assert (i!=0);
		//simplify
	    if (i == 1)
	    	return this;
	    return new RealConstant(value / i);
	  }

  public RealExpression _div (RealExpression e) {
		//simplify
		if (e instanceof RealConstant) {
			RealConstant ic = (RealConstant)e;
			if (ic.value == 1)
				return this;
		}

		if (e instanceof RealConstant) {
	      assert(((RealConstant) e).value!=0);
	      return new RealConstant(value / ((RealConstant) e).value);
	    } else {
	      return super._div(e);
	    }
	  }

	public RealExpression _neg ()
	{
		if (value == 0)
			return this;
		else
			return super._neg();
	}

  public boolean equals (Object o) {
    if (!(o instanceof RealConstant)) {
      return false;
    }

    return value == ((RealConstant) o).value;
  }

  public String toString () {
    return "CONST_" + value + "";
  }

  public String prefix_notation ()
	{
    String stringValue = Double.toString(value);
		if (stringValue.contains("E")) {
			int exp = Integer.valueOf(stringValue.substring(stringValue.indexOf("E") + 1, stringValue.length()));
			if (exp < 0) {
				stringValue = String .format("%." + (stringValue.indexOf("E") - stringValue.indexOf(".") - 1 - exp) + "f", value);
			} else {
				stringValue = String.format("%." + Math.max(0, (stringValue.indexOf("E") - stringValue.indexOf(".") - 1 - exp)) + "f", value);
			}
		}
		return stringValue;
	}

  public String stringPC () {
    return "CONST_" + value + "";
  }

  public double value () {
    return value;
  }

  public double solution() {
  		return value;
  }

  public void getVarsVals(Map<String,Object> varsVals) {}

	// JacoGeldenhuys
	@Override
	public void accept(ConstraintExpressionVisitor visitor) {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public int compareTo(Expression expr) {
		if (expr instanceof RealConstant) {
			RealConstant e = (RealConstant) expr;
			return Double.compare(value(), e.value());
		} else {
			return getClass().getCanonicalName().compareTo(expr.getClass().getCanonicalName());
		}
	}

	@Override
	public Object accept(ConstraintExpressionVisitor2 visitor) {
		// TODO Auto-generated method stub
		return null;
	}

}
