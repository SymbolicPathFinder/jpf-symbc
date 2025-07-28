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

package npe;

import org.sosy_lab.sv_benchmarks.Verifier;

public class StringEqualsTest {
    public static void main(String[] args) {
        // Tests for String.equals() method with symbolic execution to check for null pointer exception
        // Each test explores different variation add individual methods to run specific test scenarios
    }

    // Test 1: Both strings concrete
    public static void testBothConcrete() {
        String arg = "Hello World";
        String str = "SPF";
        if (str.equals(arg)) {
            System.out.println("Test 1: Then Side");
        } else {
            System.out.println("Test 1: Else Side");
        }
    }

    // Test 2: Both strings symbolic
    public static void testBothSymbolic() {
        String arg = Verifier.nondetString();
        String str = Verifier.nondetString();
        if (str.equals(arg)) {
            System.out.println("Test 2: Then Side");
        } else {
            System.out.println("Test 2: Else Side");
        }
    }

    // Test 3: arg is concrete, str is symbolic
    public static void testArgConcreteStrSymbolic() {
        String arg = "Hello World";
        String str = Verifier.nondetString();
        if (str.equals(arg)) {
            System.out.println("Test 3: Then Side");
        } else {
            System.out.println("Test 3: Else Side");
        }
    }

    // Test 4: str is concrete, arg is symbolic
    // The call str.equals(arg) will not throw NullPointerException
    // because String.equals(Object anObject) handles null perfectly
    // and checks for content comparison not reference
    public static void testConcreteOnSymbolic() {
        String str = Verifier.nondetString();
        String arg = "HELLO WORLD";
        if(arg.equals(str)) {
            System.out.println("Test 4: Then Side");
        } else {
            System.out.println("Test 4: Else Side");
        }
    }
}
