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


public class ExDarko {

	public static void main(String[] args) {
		new ExDarko().unboxed(1,2);
		new ExDarko().boxed(1,2);
		new ExDarko().customBoxed(1,2);
	}

	private void unboxed(int i, int j) {
		if (i == j) {
			System.out.println("HIT");
		}
	}

	private void boxed(int i, int j) {
		if (new Integer(i).equals(new Integer(j))) {
			System.out.println("HIT");
		}
	}

	private void customBoxed(int i, int j) {
		if (new MyInteger(i).equals(new MyInteger(j))) {
			System.out.println("HIT");
		}
	}

}

class MyInteger {
	int value;

	public MyInteger(int value) {
		this.value = value;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == this) {
			return true;
		}
		if (!(obj instanceof MyInteger)) {
			return false;
		}
		MyInteger other = (MyInteger) obj;
		return this.value == other.value;
	}
}
