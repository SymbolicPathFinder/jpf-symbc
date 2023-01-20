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

package concolic;

import java.lang.reflect.*;
import gov.nasa.jpf.symbc.Concrete;
import gov.nasa.jpf.symbc.Partition;


// this is the example that shows the power of the new technique,
// it illustrates various heuristics and
// can be used to explain how we are different/improve upon from DART and EXE
public class TestMain {
	static String class_name;
	static String method_name;
	static Object[] method_args;

	/**
	 * @param args
	 */

	//native static double hash(double x);

	@Concrete("true")
    //@Partition({"x>3.0","x<=3.0"})
	public static double hash(double x) {
			return x*10.0;
	}

	public static void test_concolic(int x, int y) {
		int path = 0;
		if (x > 0) {
			if (y == hash(x)) {
				System.out.println("S0");
				path = 1;
			}
			else {
				System.out.println("S1");
				path = 2;
			}
			
			//if (y > 10) {
			if (x > 3 && y > 10) {
				 if (path == 1)
					System.out.println("S0;S3");
				 if (path == 2)
					System.out.println("S1;S3");
			}
			else {
				 if (path == 1)
					System.out.println("S0;S4");
				 if (path == 2)
					System.out.println("S1;S4");
			}
			
			
		}
		else {
			System.out.println("ELSE");
		}



	}
	public static void test_reflection() {
		System.out.println("Start");

		class_name = "gov.nasa.jpf.symbc.concolic.TestMain";
		method_name = "hash_java";
		method_args = new Object[1];


		try {
			  Class<?> cls = Class.forName(class_name);
		      Class<?>[] argTypes = new Class<?>[method_args.length];

		      for (int i=0; i< method_args.length; i++)
		        argTypes[i] = Double.TYPE;



		      for (int i=0; i< method_args.length; i++)
			        method_args[i] = new Double(1.0);

		      for (int i=0; i< method_args.length; i++)
			        argTypes[i] = Double.TYPE;

		      Method m = cls.getMethod(method_name, argTypes);

		      int modifiers = m.getModifiers();

		      if (Modifier.isStatic(modifiers) && Modifier.isPublic(modifiers)){
		        Object result = m.invoke(null, method_args); // here we need the type of the result
		        if (result instanceof Double)
		        	System.out.println("result type is double");
		        System.out.println("result "+result);
		      }
		}

		catch (Throwable e) {
			e.printStackTrace();
			System.err.println(e);
		}
	}

	public static void main(String[] as) {
		//test_reflection();
		test_concolic(0,0);
	}

}
