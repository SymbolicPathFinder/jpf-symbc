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

package gov.nasa.jpf.symbc;

public class TestPC {
    
    native public static String booleanPC_x_y(String name1, String comp1, String name2, String comp2);
    
    native public static String doublePC1(String name1, String comp1, double val);
    native public static String doublePC2(double val,String comp1 ,String name1);
    native public static String doublePC3(String name1,String operator ,String name2,String comp, double val);
    native public static String doublePC4(double val, String name1,String operator ,String name2,String comp);

    native public static String intPC1(String name1, String comp1, int val);
    native public static String intPC2(String name1,String operator ,String name2,String comp, int val);
}
