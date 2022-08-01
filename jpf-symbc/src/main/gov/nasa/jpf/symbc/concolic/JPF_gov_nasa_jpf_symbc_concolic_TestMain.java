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

package gov.nasa.jpf.symbc.concolic;


import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.concolic.FunctionExpression;
import gov.nasa.jpf.vm.NativePeer;

public class JPF_gov_nasa_jpf_symbc_concolic_TestMain extends NativePeer{

	public static double hash__D__D (MJIEnv env, int clsObjRef, double a) {
		  System.out.println("inside model function hash");
		  Object [] attrs = env.getArgAttributes();
		  boolean arg_concrete = false;
		  if (attrs==null) // concrete? I thing
			  arg_concrete = true;

		  RealExpression sym_arg = (RealExpression) attrs[0];
		  if (sym_arg == null)  // concrete
			  arg_concrete = true;
		  if (arg_concrete)
			  sym_arg = new RealConstant(a);

		  // assert(sym_arg!=null);
		  Class<?>[] args_type = new Class<?> [1];
		  args_type[0] = Double.TYPE;

		  Expression[] sym_args = new Expression[1];
		  sym_args[0] = sym_arg;

		  FunctionExpression result = new FunctionExpression(
				  "gov.nasa.jpf.symbc.concolic.TestMain",
				  "hash_java", args_type, sym_args, null);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0.0;
	  }


}