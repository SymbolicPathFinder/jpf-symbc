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

public class StringIsEmptyTest {
    public static void main(String[] args) {
        // Tests for String.isEmpty() method with symbolic execution to check for null pointer exception
        // Each test explores different variation add individual methods to run specific test scenarios
        testConcreteStr();
    }

    // Test 1 : str is concrete
    public static void testSymbolicStr() {
        String str = Verifier.nondetString();
        if(str.isEmpty()) {
            System.out.println("Empty String");
        } else {
            System.out.println("Not Empty String");
        }
    }

    // Test 2 : str is concrete
    public static void testConcreteStr() {
        String str = "Hello World";
        // String str = "";
        if(str.isEmpty()) {
            System.out.println("Empty String");
        } else {
            System.out.println("Not Empty String");
        }
    }
}
