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
THE SUBJECT SOFTWARE. NO SUPPORT IS WARRANTED TO BE PROVIDED AS IT IS PROVIDED.

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

//import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.util.LogManager;
import java.util.*;


import hampi.Hampi;
import hampi.constraints.Constraint;
import hampi.constraints.Regexp;
import hampi.constraints.Expression;
import hampi.Solution;
import java.util.logging.Logger;


/*
 * HAMPI for now only works on Linux!!
 * To run HAMPI we need to add the libSTPJNI.so and STPJNI.jar (with of course hampi.jar) to the symbc/lib dir
 * Then we need to add this directory to the java.library.path on the command line as in: -Djava.library.path=<jpf-root>extensions/symbc/lib
 */
public class SymbolicStringConstraintsHAMPI {
  static Logger logger = LogManager.getLogger("stringsolver");
  StringPathCondition pc = null;
  Hampi hampi;

  public boolean isSatisfiable(StringPathCondition pc) {

		//System.out.println("String Constraint" + pc);

		//System.out.println("---------Start---------");

		hampi = new Hampi();

		boolean result =  getExpression(pc.header);
		//System.out.println("---------End---------");
		return result;
	}


	private Expression getStringExpression(StringExpression expr) {
		Expression result = null;
		if (expr instanceof StringConstant) {
		  result = hampi.constExpr(expr.solution());
		}
		else if (expr instanceof StringSymbolic) {
			result = hampi.varExpr(expr.getName());
		}
		else if (expr instanceof DerivedStringExpression) {
			DerivedStringExpression dexpr = (DerivedStringExpression) expr;
			//System.out.println("operator = " + dexpr.op);
			switch (dexpr.op) {
			case VALUEOF:
				result = getStringExpression((StringExpression) dexpr.oprlist[0]); // hack not always StringExpression
				break;
			case CONCAT:
				//System.out.println("Found CONCAT " + expr);
				Object left = getStringExpression(dexpr.left);
				Object right = getStringExpression(dexpr.right);
				result = hampi.concatExpr((Expression)left,(Expression)right);
				break;
			}
		}
		else {
			logger.severe("Exiting after unhandled type " + expr);
			System.exit(0);
		}
		return result;
	}


	private boolean findSolution(Constraint c1) {
		Constraint all = hampi.andConstraint(listOfAllConstraints);
		all = hampi.andConstraint(all,c1);
		Solution s;
		int len = 0;
		while (len < 256) {
			s = hampi.solve(all,len);
			if (s.isSatisfiable()) {
				logger.info("Found solution!");
				return true;
			}
			len++;
		}
		logger.warning("No solution for " + all.toJavaCode(""));
		return false;
	}

	List<Constraint> listOfAllConstraints = new LinkedList<Constraint>();

	private boolean evaluateStringConstraint(StringConstraint c) {
		Expression left = null;
		Expression right = null;
		switch (c.comp) {
		case EQUALS:
		case EQ:
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			if (!(c.left instanceof StringConstant) && !(c.right instanceof StringConstant)) {
				logger.severe("EQ: One side must be non symbolic for HAMPI to work!");
				System.exit(0);
			}
			if ((c.left instanceof StringConstant) && (c.right instanceof StringConstant))  {
				return c.left.solution().equals(c.right.solution());
			}
			if ((c.left instanceof StringConstant)) {
				// right is symbolic
				Regexp regLeft = hampi.constRegexp(c.left.solution());
				Constraint c1 = hampi.regexpConstraint(right, true, regLeft);
				if (findSolution(c1))
					listOfAllConstraints.add(c1);
				else
					return false;
			}
			else if ((c.right instanceof StringConstant)) {
				// left is symbolic
				Regexp regRight = hampi.constRegexp(c.right.solution());
				Constraint c1 = hampi.regexpConstraint(left, true, regRight);
				if (findSolution(c1))
					listOfAllConstraints.add(c1);
				else
					return false;
			}
			break;
		case NOTEQUALS:
		case NE:
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			if (!(c.left instanceof StringConstant) && !(c.right instanceof StringConstant)) {
				logger.severe("NE: One side must be non symbolic for HAMPI to work!");
				System.exit(0);
			}
			if ((c.left instanceof StringConstant) && (c.right instanceof StringConstant))  {
				return !c.left.solution().equals(c.right.solution());
			}
			if ((c.left instanceof StringConstant)) {
				// right is symbolic
				Regexp regLeft = hampi.constRegexp(c.left.solution());
				Constraint c1 = hampi.regexpConstraint(right, false, regLeft);
				if (findSolution(c1))
					listOfAllConstraints.add(c1);
				else
					return false;
			}
			else if ((c.right instanceof StringConstant)) {
				// left is symbolic
				Regexp regRight = hampi.constRegexp(c.right.solution());
				Constraint c1 = hampi.regexpConstraint(left, false, regRight);
				if (findSolution(c1))
					listOfAllConstraints.add(c1);
				else
					return false;
			}
			break;
		}
		return true;
	}


	private boolean getExpression(StringConstraint c) {
		listOfAllConstraints = new LinkedList<Constraint>();
		while (c != null) {

			boolean constraintResult = evaluateStringConstraint(c);

			if (constraintResult == false)
				return false;

			c = c.and;
		}

		return true;
	}


	public void solve(StringPathCondition pc) {

	}

}