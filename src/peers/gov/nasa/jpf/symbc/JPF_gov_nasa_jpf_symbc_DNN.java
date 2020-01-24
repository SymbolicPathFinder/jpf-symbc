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

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;



public class JPF_gov_nasa_jpf_symbc_DNN extends NativePeer {

	/* YN: Methods to read the internal values of the DNN on the SPF side. */
    @MJI
    public static double get_biases0_value(MJIEnv env, int objRef, int index) {
        return DNNData.biases0[index];
    }

    @MJI
    public static double get_biases2_value(MJIEnv env, int objRef, int index) {
        return DNNData.biases2[index];
    }

    @MJI
    public static double get_biases6_value(MJIEnv env, int objRef, int index) {
        return DNNData.biases6[index];
    }

    @MJI
    public static double get_biases8_value(MJIEnv env, int objRef, int index) {
        return DNNData.biases8[index];
    }

    @MJI
    public static double get_weights6_value(MJIEnv env, int objRef, int index0, int index1) {
        return DNNData.weights6[index0][index1];
    }

    @MJI
    public static double get_weights8_value(MJIEnv env, int objRef, int index0, int index1) {
        return DNNData.weights8[index0][index1];
    }

    @MJI
    public static double get_weights0_value(MJIEnv env, int objRef, int index0, int index1, int index2, int index3) {
        return DNNData.weights0[index0][index1][index2][index3];
    }

    @MJI
    public static double get_weights2_value(MJIEnv env, int objRef, int index0, int index1, int index2, int index3) {
        return DNNData.weights2[index0][index1][index2][index3];
    }

    
   @MJI
   public static void readDataFromFiles(MJIEnv env, int objRef, int pathRef) {
      
       String path = env.getStringObject(pathRef);
       System.out.println("Reading from ..."+path);
       DNNData.createFromDataFiles(path);
   }
   


}