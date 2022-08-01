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

package sequences;


import gov.nasa.jpf.vm.Verify;
import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.Preconditions;


public class BankAccountDriverSeqSymCGOptimization {

	public static void testDriver(int length){
		BankAccount b = new BankAccount(0);
		for (int i=0; i<length; i++){
			boolean res = flag(true);
			if(res) {
				b.deposit(10);
				if(!res) {
					b.deposit(5);
				}
				
			} else if(res) {
				b.withdraw(1);
				if(!res) {
					b.withdraw(1);
				}
			}
		}
	}
	
	public static boolean flag(boolean x) {
		return x;
	}

	public static void main(String[] args){
		testDriver(11);
		//Debug.printPC("Path Condition: ");
		//System.out.println();
	}
}
