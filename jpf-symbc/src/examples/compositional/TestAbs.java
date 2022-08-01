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

package compositional;

// from Saswat Anand

public class TestAbs {
  int abs(int x) {
	  if(x>0) return x;
	  else if (x==0)
		  	return 100;
	  else
		  return -x;
  }
  void testAbs(int p, int q) {
	  int m = abs(p);
	  int n = abs(q);
	  if(m>n && p>0)
		  assert false;
  }
  public static void main(String[] args) {
		(new TestAbs()).testAbs(0,0);

	}
}
