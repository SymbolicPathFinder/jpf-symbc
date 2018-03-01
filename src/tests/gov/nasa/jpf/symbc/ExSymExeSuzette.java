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

package gov.nasa.jpf.symbc;

public class ExSymExeSuzette {
	public void test(int x, int y) {

		int v = method_a(x, y);

		if(v > 0) {

			System.out.println("branch taken");

			int tmp=method_b(x); //orig method_b(x)

			if (tmp == x) //added

				System.out.println("inner branch taken"); //added

		}

	}



	public int method_a(int x, int y) {

		if(x > 10)

			return x;

		if(y > 10)

			return y;

		return 0;

	}
	public int method_b(int z) {

		if(z > 10)
			return z++;
		else
			return z--;
	}



	public static void main(String[] args) {

		ExSymExeSuzette ex = new ExSymExeSuzette ();

		ex.test(0,0);
		//test(0,0);
	}

}

