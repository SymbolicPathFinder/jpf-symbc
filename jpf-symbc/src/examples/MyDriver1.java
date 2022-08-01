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


import gov.nasa.jpf.symbc.Debug;

public class MyDriver1 {

    // The method whose parameters are marked as symbolic.
    private static void imposePreconditions(int x, int y) {
        MyClass1 mc = new MyClass1();

        // The preconditions
        if (-100 <= x  &&  x <= 100  &&  1 <= y  &&  y <= 3) {
            mc.myMethod(x, y);
            Debug.printPC("\nMyClass1.myMethod Path Condition: ");
        }
    }

    // The test driver
    public static void main(String[] args) {
        // Actual arguments are ignored when doing symbolic execution.
        imposePreconditions(1,2);
    }
}