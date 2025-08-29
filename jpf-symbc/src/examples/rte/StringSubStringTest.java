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

public class StringSubStringTest {
    public static void main(String[] args) {
        // Tests for substring() method with symbolic execution to check for StringIndexOutOfBoundsException
        // Each test explores different variation
    }

    // substring(beginIndex)

    // Test 1: Both symbolic (arg and beginIndex)
    public static void testBeginBothSymbolic() {
        String arg = Verifier.nondetString();
        int begin = Verifier.nondetInt();
        System.out.println(arg.substring(begin));
    }

    // Test 2: Arg symbolic, beginIndex concrete
    public static void testBeginArgSymbolicIndexConcrete() {
        String arg = Verifier.nondetString();
        System.out.println(arg.substring(-1));
        System.out.println(arg.substring(100));
    }

    // Test 3: Arg concrete, beginIndex symbolic
    public static void testBeginArgConcreteIndexSymbolic() {
        String arg = "Hello World";
        int begin = Verifier.nondetInt();
        System.out.println(arg.substring(begin));
    }


    // substring(beginIndex, endIndex)

    // Test 4: All symbolic (arg, beginIndex, endIndex)
    public static void testBothSymbolic() {
        String arg = Verifier.nondetString();
        int begin = Verifier.nondetInt();
        int end = Verifier.nondetInt();
        System.out.println(arg.substring(begin, end));
    }

    // Test 5: Arg symbolic, indices concrete
    public static void testArgSymbolicIndicesConcrete() {
        String arg = Verifier.nondetString();
        System.out.println(arg.substring(-1, 2));
        System.out.println(arg.substring(2, -3));
        System.out.println(arg.substring(3, 100));
        System.out.println(arg.substring(100,2 ));
        System.out.println(arg.substring(5, 2)); // begin > end
    }

    // Test 6: Arg concrete, indices symbolic
    public static void testArgConcreteIndicesSymbolic() {
        String arg = "Hello World";
        int begin = Verifier.nondetInt();
        int end = Verifier.nondetInt();
        System.out.println(arg.substring(begin, end));
    }
}
