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

public class StringStartsWithIfNonNullTest {
    public static void main(String[] args) {
        // Tests for String.startsWith() method with symbolic execution to check for null pointer exception
        // Each test explores different variation add individual methods to run specific test scenarios
        // In contrast, conditions like str == null or str != null add branching when str is symbolic,
        // meaning both null and non-null paths are explored for str.
    }

    // Test 1: if str null - branch check (arg != null) => (IFNONNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNull1() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str == null) {
            System.out.println("str is null");
        } else {
            System.out.println("str is not null");
            if (str.startsWith(arg)) {
                System.out.println("Test 1: Then Side");
            } else {
                System.out.println("Test 1: Else Side");
            }
        }
    }

    // Test 2: if str null - branch check (arg == null) => (IFNONNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNull2() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str == null) {
            System.out.println("str is null");
            if (str.startsWith(arg)) {
                System.out.println("Test 2: Then Side");
            } else {
                System.out.println("Test 2: Else Side");
            }
        } else {
            System.out.println("str is not null");
        }
    }

    // Test 3: if str null - branch check (arg == null) and (arg != null) => (IFNONNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNull3() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str == null) {
            System.out.println("str is null");
            if (str.startsWith(arg)) {
                System.out.println("Test 3: Then Side");
            } else {
                System.out.println("Test 3: Else Side");
            }
        } else {
            System.out.println("str is not null");
            if (str.startsWith(arg)) {
                System.out.println("Test 3: Then Side");
            } else {
                System.out.println("Test 3: Else Side");
            }
        }
    }
}
