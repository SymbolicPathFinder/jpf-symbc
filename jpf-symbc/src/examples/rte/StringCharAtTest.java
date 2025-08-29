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

package rte;

import org.sosy_lab.sv_benchmarks.Verifier;

public class StringCharAtTest {
    public static void main(String[] args) {
        // Tests for charAt() method with symbolic execution to check for StringIndexOutOfBoundsException
        // Each test explores different variation add individual methods to run specific test case scenarios
    }

    //Test 1: Both symbolic
    public static void testBothSymbolic() {
        String arg = Verifier.nondetString();
        int i = Verifier.nondetInt();
        System.out.println(arg.charAt(i));
    }

    //Test 2: Arg symbolic, index concrete
    public static void testArgSymbolicIndexConcret() {
        String arg = Verifier.nondetString();
        System.out.println(arg.charAt(-1));
        System.out.println(arg.charAt(100));
    }

    //Test 3: Arg concrete, index smybolic
    public static void testArgConcreteIndexSymbolic() {
        String arg = "Hello World";
        int i = Verifier.nondetInt();
        System.out.println(arg.charAt(i));
    }

    //Test 4: String Builder
    public static void testSB() {
        StringBuilder sb = new StringBuilder(Verifier.nondetString());
        assert sb.charAt(0) == sb.charAt(5);
    }
}
