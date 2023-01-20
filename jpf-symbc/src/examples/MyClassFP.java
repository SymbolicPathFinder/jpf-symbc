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

public class MyClassFP {
    public double myMethodFP(double x, double y) {
        double z = x + y;
        if (z > 0.0) {
            z = 1.0;
        } else {
            z = z - x;
        }
        z = 2.0 * z;
        return z;
    }

    // The test driver
    public static void main(String[] args) {
        MyClassFP mc = new MyClassFP();
        double x = mc.myMethodFP(1.0, 22.0);
        Debug.printPC("\nMyClassFP.myMethodFP Path Condition: ");
    }
}