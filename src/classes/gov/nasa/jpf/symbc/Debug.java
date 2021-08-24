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

//
// Copyright (C) 2006 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc;

import gov.nasa.jpf.vm.Verify;

public class Debug {
    
    native public static void printPC(String msg);
    native public static String getSolvedPC();
    native public static String getPC_prefix_notation();
    native public static String PC4Z3();

    native public static String getSymbolicIntegerValue(int v);
    native public static String getSymbolicLongValue(long v);
    native public static String getSymbolicShortValue(short v);
    native public static String getSymbolicByteValue(byte v);
    native public static String getSymbolicCharValue(char v);
    native public static String getSymbolicRealValue(double v);
    native public static String getSymbolicRealValue4Z3(double v);
    native public static String getSymbolicBooleanValue(boolean v);
    native public static String getSymbolicStringValue(String v);
    
    native public static int addSymbolicInt(int v, String name);
    //native public static long addSymbolic(long v, String name);
    //native public static short addSymbolic(short v, String name);
    native public static byte addSymbolicByte(byte v, String name);
    native public static char addSymbolicChar(char v, String name);
    native public static double addSymbolicDouble(double v, String name);
    native public static boolean addSymbolicBoolean(boolean v, String name);
    //native public static String addSymbolic(String v, String name);
    
    native public static boolean isSymbolicInteger(int v);
    native public static boolean isSymbolicLong(long v);
    native public static boolean isSymbolicShort(short v);
    native public static boolean isSymbolicByte(byte v);
    native public static boolean isSymbolicChar(char v);
    
    native public static boolean checkAccuracy(double v, double err); 
    // check accuracy of floating point computation
    // wrt given error
    
    public static void assume (boolean c) {
    	if(!c)
    		Verify.ignoreIf(true);
    }

    // puts a new symbolic value in the arg attribute
    native public static int makeSymbolicInteger(String name);
    native public static long makeSymbolicLong(String name);
    native public static short makeSymbolicShort(String name);
    native public static byte makeSymbolicByte(String name);
    native public static double makeSymbolicReal(String name);
    native public static boolean makeSymbolicBoolean(String name);
    native public static char makeSymbolicChar(String name);
    native public static String makeSymbolicString(String name);
    
    // this method should be used instead of the native one in
    // the no-string-models branch of jpf-core
    public static String makeSymbolicString(String name, int size){
		char str[] = new char[size];
    	for(int i = 0; i < size; i++) {
    		str[i] = makeSymbolicChar(name + i);
         }
    	return new String(str);
    }
    
    // makes v a symbolic object
    public static Object makeSymbolicRef(String name, Object v) {
    	assert (v!=null); // needed for type info
    	if (Verify.randomBool()) {

    		makeFieldsSymbolic(name, v);
    	}
    	else {

    		v = makeSymbolicNull(name);
    	}
    	return v;
    }

    native public static void makeFieldsSymbolic(String name, Object v);
    native public static Object makeSymbolicNull(String name);

    native public static void printSymbolicRef(Object v, String msg);

    native public static void printHeapPC(String msg);


    // performs abstract state matching
    native public static boolean matchAbstractState(Object v);
    
    /* YN: user-defined cost*/
    native public static void addCost(Object v);
    native public static void setLastObservedInputSize(Object v);
    native public static int getLastObservedInputSize();
    native public static double getLastMeasuredMetricValue();
    native public static void clearMeasurements();
}
