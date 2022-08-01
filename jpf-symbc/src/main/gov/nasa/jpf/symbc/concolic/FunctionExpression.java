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

package gov.nasa.jpf.symbc.concolic;
// support for arbitrary external functions

import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.util.FileUtils;
import gov.nasa.jpf.vm.ClassLoaderInfo;

import java.util.ArrayList;
import java.util.Map;
import java.lang.reflect.*;
//import java.net.MalformedURLException;
//import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;

public class FunctionExpression extends RealExpression
{
	String class_name;
	String method_name;
	Class<?>[] argTypes;
	public Expression [] sym_args;
	static URLClassLoader clsLoader = null;
	ArrayList<PathCondition> conditions;

	// what happens when there are no arguments?
	public FunctionExpression (String cls, String mth, Class<?>[] ast, 
			Expression [] sym_as, ArrayList<PathCondition> conditions)
	{
		class_name = cls;
		method_name = mth;
		assert(ast != null && sym_as != null && sym_as.length == ast.length);
		// do we need a deep copy here or a shallow copy is enough?
		argTypes = ast;
		sym_args = sym_as;
		this.conditions = conditions;
	}

	// here we assume that the solution is always double; if it is not we can cast it later;
	public double solution()
	{
		// here we need to use reflection to invoke the method with
		// name method_name and with parameters the solutions of the arguments

		assert(sym_args!=null && sym_args.length >0);

		try {
			if(clsLoader == null) {
				ArrayList<String> list = new ArrayList<String>();
				String[] cp = ClassLoaderInfo.getCurrentClassLoader().getClassPathElements();
				cp = FileUtils.expandWildcards(cp);
				for (String e : cp) {
					list.add(e);
				}
				URL[] urls = FileUtils.getURLs(list);
				clsLoader = new URLClassLoader(urls);
			}
			
			Class<?> cls = null;
			try {
				cls = Class.forName(class_name, true, clsLoader);
			} catch (ClassNotFoundException c) {
				c.printStackTrace();
				System.err.println("Class not found:" + class_name);
			} catch (UnsatisfiedLinkError e) {
				e.printStackTrace();
				System.out.println("unsatisfied link error");
				
			}
			
			  Object[] args = new Object[sym_args.length];
		      for (int i=0; i<args.length; i++)
		    	  if (sym_args[i] instanceof IntegerExpression) {
			        args[i] = new Long(((IntegerExpression)sym_args[i]).solution());
		    	  }
			      else {// RealExpression
			    	args[i] = new Double(((RealExpression)sym_args[i]).solution());
			      }
		      Method m = cls.getMethod(method_name, argTypes);
		      int modifiers = m.getModifiers();
		      if (Modifier.isStatic(modifiers) && Modifier.isPublic(modifiers)){
		    	  Object result = null;
		    	  try {
		    		  result = m.invoke(null, args); // here we need the type of the result
		    	  } catch(InvocationTargetException e) {
		    		 e.printStackTrace();
		    		 System.err.println("exception :" + e.getMessage());
		    	  }
		        if (result instanceof Number) {
		        	return ((Number) result).doubleValue();
		        }
		      }
		}

		catch (Throwable e) {
			System.err.println(e);
		}
		return 0.0;
	}

    public void getVarsVals(Map<String,Object> varsVals) {
    	if (sym_args!=null)
    		for (int i = 0; i < sym_args.length; i++)
    			sym_args[i].getVarsVals(varsVals);
    }

	public String stringPC() {
		String result="";
		if (sym_args!=null)
    		for (int i = 0; i < sym_args.length; i++)
    			result = result + sym_args[i].stringPC() + " ";
		return "(" + class_name +"." + method_name + "(" + result + ")";

	}

	public String toString () {
		String result="";
		if (sym_args!=null)
    		for (int i = 0; i < sym_args.length; i++)
    			result = result + sym_args[i].toString() + " ";
		return "(" + class_name +"." + method_name + "(" + result + ")";
	}
	@Override
	public void accept(ConstraintExpressionVisitor visitor) {
		visitor.preVisit(this);
		for (Expression arg : sym_args) {
			arg.accept(visitor);
		}
		visitor.postVisit(this);
	}

	@Override
	public int compareTo(Expression expr) {
		if (expr instanceof FunctionExpression) {
			FunctionExpression e = (FunctionExpression) expr;
			int r = class_name.compareTo(e.class_name);
			if (r == 0) {
				r = method_name.compareTo(e.method_name);
				if (r == 0) {
					if (sym_args != null) {
						if (e.sym_args == null) {
							r = 1;
						} else {
							int a = sym_args.length;
							int b = e.sym_args.length;
							r = (a < b) ? -1 : (a > b) ? 1 : 0;
							if (r == 0) {
								int i = 0;
								while ((r == 0) && (i < a)) {
									r = sym_args[i].compareTo(e.sym_args[i]);
									i++;
								}
							}
						}
					} else if (e.sym_args != null) {
						r = -1;
					}
				}
			}
			return r;
		} else {
			return getClass().getCanonicalName().compareTo(expr.getClass().getCanonicalName());
		}
	}

	

}
