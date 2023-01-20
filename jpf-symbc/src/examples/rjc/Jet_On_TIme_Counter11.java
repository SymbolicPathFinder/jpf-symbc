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

package rjc;

public class Jet_On_TIme_Counter11 {
  private double Value1297 = 0;

  public void Main14( double ton_2, double Clock_at_tics_3, double Clock_at_Sample_Time_4, boolean[] Stop_jets_5 )
  {
    double sig_0 = 0;
    double sig_1 = 0;
    double sig_2 = 0;

    sig_2 = Clock_at_tics_3 - Clock_at_Sample_Time_4;
    sig_1 = ton_2 - sig_2;
    sig_0 = Value1297;
    Stop_jets_5[ 0 ] = sig_1 > sig_0;
  }
  public void Init15(  )
  {
    Value1297 = 0;
  }
}
