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

public class StringContainsTest {
    public static void main(String[] args) {
        // Tests for String.contains() method with symbolic execution to check for null pointer exception
        // Each test explores different variation add individual methods to run specific test scenarios
        // Note: Assignments like arg = null assign a concrete null literal, not symbolic.
        // In contrast, conditions like str == null or str != null add branching when str is symbolic,
        // meaning both null and non-null paths are explored for str.
    }

    // Test 1: Both strings concrete
    public static void testConcreteStrings() {
        String arg = "Hello World";
        String str = "SPF";
        if (str.contains(arg)) {
            System.out.println("Test 1: Then Side");
        } else {
            System.out.println("Test 1: Else Side");
        }
    }

    // Test 2: Both strings symbolic
    public static void testBothSymbolic() {
        String arg = Verifier.nondetString();
        String str = Verifier.nondetString();
        if (str.contains(arg)) {
            System.out.println("Test 2: Then Side");
        } else {
            System.out.println("Test 2: Else Side");
        }
    }

    // Test 3: arg is null, str is symbolic
    // arg is concretely assigned to null literal (not symbolic).
    public static void testArgNullStrSymbolic() {
        String arg = null;
        String str = Verifier.nondetString();
        if (str.contains(arg)) {
            System.out.println("Test 3: Then Side");
        } else {
            System.out.println("Test 3: Else Side");
        }
    }

    // Test 4: arg is symbolic, str is null
    // arg is concretely assigned to null literal (not symbolic).
    public static void testArgSymbolicStrNull() {
        String arg = Verifier.nondetString();
        String str = null;
        if (arg.contains(str)) {
            System.out.println("Test 4: Then Side");
        } else {
            System.out.println("Test 4: Else Side");
        }
    }

    // Test 5: both str and arg are null
    // both are concretely assigned to null literal (not symbolic).
    public static void testBothNull() {
        String str = null;
        String arg = null;
        if(str.contains(arg)) {
            System.out.println("Test 15: Then Side");
        } else {
            System.out.println("Test 15: Else Side");
        }
    }

    // Test 6: arg is concrete, str is symbolic
    public static void testArgConcreteStrSymbolic() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str.contains(arg)) {
            System.out.println("Test 6: Then Side");
        } else {
            System.out.println("Test 6: Else Side");
        }
    }

    // Test 7: arg is symbolic, str is concrete
    public static void testArgSymbolicStrConcrete() {
        String arg = Verifier.nondetString();
        String str = "Hello";
        if (arg.contains(str)) {
            System.out.println("Test 7: Then Side");
        } else {
            System.out.println("Test 7: Else Side");
        }
    }

    // Test 8: if str is not null - branch check (arg != null) => (IFNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNotNull1() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str != null) {
            System.out.println("str is not null");
            if (str.contains(arg)) {
                System.out.println("Test 8: Then Side");
            } else {
                System.out.println("Test 8: Else Side");
            }
        } else {
            System.out.println("str is null");
        }
    }

    // Test 9: if str is not null - branch check (arg == null) => (IFNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNotNull2() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str != null) {
            System.out.println("str is not null");
        } else {
            System.out.println("str is null");
            if (str.contains(arg)) {
                System.out.println("Test 9: Then Side");
            } else {
                System.out.println("Test 9: Else Side");
            }
        }
    }

    // Test 10: if str is not null - branch check (arg != null) and (arg == null) => (IFNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNotNull3() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str != null) {
            System.out.println("str is not null");
            if (str.contains(arg)) {
                System.out.println("Test 10: Then Side");
            } else {
                System.out.println("Test 10: Else Side");
            }
        } else {
            System.out.println("str is null");
            if (str.contains(arg)) {
                System.out.println("Test 10: Then Side");
            } else {
                System.out.println("Test 10: Else Side");
            }
        }
    }

    // Test 11: if str null - branch check (arg != null) => (IFNONNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNull1() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str == null) {
            System.out.println("str is null");
        } else {
            System.out.println("str is not null");
            if (str.contains(arg)) {
                System.out.println("Test 11: Then Side");
            } else {
                System.out.println("Test 11: Else Side");
            }
        }
    }

    // Test 12: if str null - branch check (arg == null) => (IFNONNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNull2() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str == null) {
            System.out.println("str is null");
            if (str.contains(arg)) {
                System.out.println("Test 12: Then Side");
            } else {
                System.out.println("Test 12: Else Side");
            }
        } else {
            System.out.println("str is not null");
        }
    }

    // Test 13: if str null - branch check (arg == null) and (arg != null) => (IFNONNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNull3() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str == null) {
            System.out.println("str is null");
            if (str.contains(arg)) {
                System.out.println("Test 13: Then Side");
            } else {
                System.out.println("Test 13: Else Side");
            }
        } else {
            System.out.println("str is not null");
            if (str.contains(arg)) {
                System.out.println("Test 13: Then Side");
            } else {
                System.out.println("Test 13: Else Side");
            }
        }
    }

    // Test 14: self contains check
    public static void testSelf() {
        String str = Verifier.nondetString();
        if(str.contains(str)) {
            System.out.println("Test 14: Then Side");
        } else {
            System.out.println("Test 14: Else Side");
        }
    }

    // Test 15: self contains check - branch check (arg != null) => (IFNULL)
    public static void testSelfNotNull() {
        String str = Verifier.nondetString();
        if (str != null) {
            if (str.contains(str)) {
                System.out.println("Test 15: Then Side");
            } else {
                System.out.println("Test 15: Else Side");
            }
        } else {
            System.out.println("Test 15: str is null");
        }
    }

    // Test 16: self contains check - branch check (arg == null) => (IFNONNULL)
    public static void testSelfNull() {
        String str = Verifier.nondetString();
        if (str == null) {
            if (str.contains(str)) {
                System.out.println("Test 16: Then Side");
            } else {
                System.out.println("Test 16: Else Side");
            }
        } else {
            System.out.println("Test 16: str is not null");
        }
    }


    // Test 17: using assert with one variable which is symbolic
    public static void testAssert1() {
        String str = Verifier.nondetString();
        assert (str.contains("Hello"));
    }

    // Test 18: using assert with two variables, both symbolic
    public static void testAssert2() {
        String str = Verifier.nondetString();
        String arg = Verifier.nondetString();
        assert (arg.contains(str));
    }

 }
