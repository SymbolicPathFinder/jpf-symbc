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

// auto-generated JUnit code:
import org.junit.Before;
import org.junit.Test;
import gov.nasa.jpf.util.test.TestJPF;

public class sequences_StackTest extends TestJPF {

	private sequences.Stack sequences_stack;

	@Before
	public void setUp() throws Exception {
		sequences_stack = new sequences.Stack();
	}

	@Test
	public void test0() {
		sequences_stack.push(-2147483606);
		sequences_stack.push(0);
	}

	@Test
	public void test1() {
		sequences_stack.push(-2147483606);
		sequences_stack.push(-10000);
	}

	@Test
	public void test2() {
		sequences_stack.push(-2147483606);
		sequences_stack.pop(-2147483606);
	}

	@Test
	public void test3() {
		sequences_stack.push(0);
	}

	@Test
	public void test4() {
		sequences_stack.push(0);
		sequences_stack.push(0);
	}

	@Test
	public void test5() {
		sequences_stack.push(0);
		sequences_stack.push(-10000);
	}

	@Test
	public void test6() {
		sequences_stack.push(0);
		sequences_stack.pop(-2147483606);
	}

	@Test
	public void test7() {
		sequences_stack.push(-10000);
	}

	@Test(expected = java.lang.RuntimeException.class)
	public void test8() {
		sequences_stack.pop(-2147483606);
		//should lead to ##EXCEPTION## "java.lang.RuntimeException: empty stack..."
	}

	@Test
	public void test9() {
		sequences_stack.pop(-2147483606);
	}
}
