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

import gov.nasa.jpf.symbc.Symbolic;


public class MyClassWithFields {
    @Symbolic("true")
    public int field1;

	@Symbolic("true")
    public int field2;
    
    public int myMethod1() {
		int z = field1 + field2;
		if (z > 0) {
			z = 1;
		} else {
			z = z - field1;
		}
		z = field1 * z;
		return z;
    }
}