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

import gov.nasa.jpf.symbc.Debug;



/**
 *
 * @author Mithun Acharya
 *
 */
public class IncDec {

	private int global;

	public IncDec(){
		global = 0;
	}

	public void inc(int input){
		if (input == 0)
			;
		else
			;
		this.global++;
		//System.out.println("global=" + global);
	}
	public void dec(int input){
		if (input == 0)
			;
		else
			;
		this.global--;
		//System.out.println("global=" + global);
		//Debug.recordMethodTransition(this);
	}

	/**
	 *
	 * Observer method.
	 */
	public boolean isZero(){
		return global == 0;
	}

}
