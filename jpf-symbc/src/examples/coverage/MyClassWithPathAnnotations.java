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

package coverage;

public class MyClassWithPathAnnotations {
    public int myMethod(int x, int y) {
        StringBuilder path = new StringBuilder();
        int z = x + y;
        if (z > 0) {
            path.append("z>0 ");
            z = 1;
        } else {
            path.append("z<=0 ");
            z = z - x;
        }

        if (x < 0) {
            path.append("x<0 ");
            z = z * 2;
        } else if (x < 10) {
            path.append("0<=x<10 ");
            z = z + 2;
        } else {
            path.append("x>=10 ");
            z = -z;
        }

        if (y < 5) {
            path.append("y<5 ");
            z = z - 12;
        } else {
            path.append("y>=5 ");
            z = z - 30;
        }
        CheckCoverage.processTestCase(path.toString());
        return z;
    }
}

