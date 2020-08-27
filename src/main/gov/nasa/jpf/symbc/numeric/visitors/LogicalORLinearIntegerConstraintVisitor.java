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

package gov.nasa.jpf.symbc.numeric.visitors;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

public class LogicalORLinearIntegerConstraintVisitor extends ProblemGeneralVisitor {

	public LogicalORLinearIntegerConstraintVisitor(ProblemGeneral pb) {
		super(pb);
	}
	
	//LogicalORLinearIntegerConstraints Visitor
	@Override 
	public boolean visit(LogicalORLinearIntegerConstraints constraint) {

		List<Object> orList = new ArrayList<Object>();
		
		for (LinearIntegerConstraint cRef: constraint.getList()) {
			Object cc;
			Object lRef = cRef.getLeft().accept(this);
			Object rRef = cRef.getRight().accept(this);
			if(lRef instanceof Long && rRef instanceof Long) {
				boolean ccRet = parseLOLIC_LL((Long)lRef, cRef.getComparator(), (Long)rRef);
				
				//This is here to mimic the functionality of how booleans are returned in PCParser.
				if(ccRet) {
					return ccRet;
				} else {
					continue;
				}
			} else if(lRef instanceof Long) {
				cc = parseLOLIC_LO((Long)lRef, cRef.getComparator(), rRef);
			} else if(rRef instanceof Long) {
				cc = parseLOLIC_OL(lRef, cRef.getComparator(), (Long)rRef);
			} else {
				cc = parseLOLIC_OO(lRef, cRef.getComparator(), rRef);
			}
			orList.add(cc);
		}

		//System.out.println("[SymbolicConstraintsGeneral] orList: " + orList.toString());
		if (orList.size() == 0) {
			return true;
		}
		Object constraint_array[] = new Object[orList.size()];
		orList.toArray(constraint_array);
		
		pb.postLogicalOR(constraint_array);

		return true;
	}

	//LogicalORLinearIntegerConstraints Parsing Methods
	private boolean parseLOLIC_LL(Long left, Comparator comp, Long right) {
		long left2 = left.longValue();
		long right2 = right.longValue();
		switch(comp){
		case EQ:
			if (left2 == right2) {
				return true;
			}
			break;
		case NE:
			if (left2 != right2) {
				return true;
			}
			break;
		case LT:
			if (left2 < right2) {
				return true;
			}
			break;
		case LE:
			if (left2 <= right2) {
				return true;
			}
			break;
		case GT:
			if (left2 > right2) {
				return true;
			}
			break;
		case GE:
			if (left2 >= right2) {
				return true;
			}
			break;
		}
		return false;
	}

	private Object parseLOLIC_LO(Long left, Comparator comp, Object right) {

		long leftConst = left.longValue(); //This could technically be removed right?

		Object tempVar = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt("")); 
		tempVars++;
		pb.post(pb.eq(tempVar, right));

		switch(comp){
		case EQ:
			return pb.eq(leftConst, tempVar);
		case NE:
			return pb.neq(leftConst, tempVar);
		case LT:
			return pb.lt(leftConst, tempVar);
		case LE:
			return pb.leq(leftConst, tempVar);
		case GT:
			return pb.gt(leftConst, tempVar);
		case GE:
			return pb.geq(leftConst, tempVar);
		default:
			throw new RuntimeException("No valid comparator"); //Shouldn't be reachable
		}
	}

	private Object parseLOLIC_OL(Object left, Comparator comp, Long right) {
		long rightConst = right.longValue(); //This could technically be removed right?
		Object tempVar = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt("")); 
		tempVars++;
		pb.post(pb.eq(tempVar, left));

		switch(comp){
		case EQ:
			return pb.eq(tempVar, rightConst);
		case NE:
			return pb.neq(tempVar, rightConst);
		case LT:
			return pb.lt(tempVar, rightConst);
		case LE:
			return pb.leq(tempVar, rightConst);
		case GT:
			return pb.gt(tempVar, rightConst);
		case GE:
			return pb.geq(tempVar, rightConst);
		default:
			throw new RuntimeException("No valid comparator"); //Shouldn't be reachable
		}
	}

	private Object parseLOLIC_OO(Object left, Comparator comp, Object right) {

		Object tempVar1 = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt(""));
		tempVars++;
		Object tempVar2 = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt(""));
		tempVars++;
		pb.post(pb.eq(tempVar1, left));
		pb.post(pb.eq(tempVar2, right));

		switch(comp){
		case EQ:
			return pb.eq(tempVar1, tempVar2);
		case NE:
			return pb.neq(tempVar1, tempVar2);
		case LT:
			return pb.lt(tempVar1, tempVar2);
		case LE:
			return pb.leq(tempVar1, tempVar2);
		case GT:
			return pb.gt(tempVar1,tempVar2);
		case GE:
			return pb.geq(tempVar1, tempVar2);
		default:
			throw new RuntimeException("No valid comparator"); //Shouldn't be reachable
		}
	}

}
