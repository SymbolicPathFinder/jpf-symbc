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

public class Yaw_Control_Law1 {
  private double Value793 = 0;
  private double Gain913 = 0;
  private double Value928 = 0;
  private double Value940 = 0;
  private double Gain1030 = 0;
  private double Gain1072 = 0;
  private double Gain1188 = 0;
  private SimpleCounter SimpleCounter_member7 = new SimpleCounter();
  private Subsystem35 Subsystem3_100000163_class_member8 = new Subsystem35();
  private Subsystem26 Subsystem2_100000162_class_member9 = new Subsystem26();
  private Subsystem17 Subsystem1_100000161_class_member10 = new Subsystem17();
  private Subsystem8 Subsystem_100000160_class_member11 = new Subsystem8();
  private Chart Chart_member12 = new Chart();
  private Jet_On_TIme_Counter10 Jet_On_TIme_Counter_100000127_class_member13 = new Jet_On_TIme_Counter10();

  public void Main4( double Position_2, double Rate_3, double[] Jet_Command_4 )
  {
    int sig_0 = 0;
    double sig_1 = 0;
    double sig_2 = 0;
    double sig_3 = 0;
    double sig_4 = 0;
    double sig_5[] = new double[ 1 ];
    double sig_6[] = new double[ 1 ];
    double sig_7[] = new double[ 1 ];
    boolean sig_8 = false;
    double sig_9 = 0;
    double sig_10 = 0;
    double[] sig_11 = new double[2];
    double sig_12 = 0;
    double sig_13 = 0;
    double sig_14 = 0;
    boolean sig_15[] = new boolean[ 1 ];
    boolean sig_16 = false;
    boolean sig_17 = false;
    double[] sig_18 = new double[2];
    double sig_19 = 0;
    double sig_20 = 0;
    double sig_21 = 0;
    int sig_22[] = new int[ 1 ];
    double sig_23 = 0;
    double sig_24 = 0;
    double sig_25[] = new double[ 1 ];
    double sig_26[] = new double[ 1 ];
    double sig_27[] = new double[ 1 ];
    double sig_28[] = new double[ 1 ];
    double sig_29 = 0;
    double sig_30 = 0;
    int ix969 = 0;
    int ix_26 = 0;
    int ix_29 = 0;

    SimpleCounter_member7.Main( sig_22 );
    sig_19 = Value793;
    sig_18[ (int)( 0 ) ] = Position_2;
    sig_18[ (int)( 1 ) ] = Rate_3;
    Subsystem3_100000163_class_member8.Main10( sig_18, sig_19, sig_28 );
    Subsystem2_100000162_class_member9.Main11( sig_18, sig_19, sig_27 );
    Subsystem1_100000161_class_member10.Main12( sig_18, sig_19, sig_26 );
    Subsystem_100000160_class_member11.Main13( sig_18, sig_19, sig_25 );
    sig_13 = (double)( sig_22[ 0 ] ) * Gain913;
    sig_10 = Value928;
    sig_4 = Value940;
    sig_12 = (double)( 1 ) / sig_19 / sig_4 * sig_10;
    ix969 = 0;
    while( ix969 < 2 )
    {
      sig_11[ (int)( ix969 ) ] = sig_18[ (int)( ix969 ) ] / sig_4 / sig_19;
      ++ix969;
    }

    sig_21 = sig_11[ (int)( 1 ) ];
    sig_23 = sig_21 * sig_21;
    sig_30 = sig_23 * Gain1030;
    sig_20 = sig_11[ (int)( 0 ) ];
    sig_3 = (double)( Math.abs( sig_20 ) );
    sig_29 = sig_30 + sig_3 - sig_12;
    sig_1 = sig_29 * Gain1072;
    sig_2 = sig_1 * (  ( sig_1 >= 0 ) ? 1 : 0  );
    sig_24 = (double)( Math.sqrt( sig_2 ) );
    Chart_member12.Main( sig_19, sig_18, sig_25[ 0 ], sig_26[ 0 ], sig_27[ 0 ], sig_28[ 0 ], sig_21, sig_24, sig_5, sig_6, sig_7 );
    sig_8 = sig_6[ 0 ] != 0;
    sig_0 = (int)( Math.floor( sig_22[ 0 ] / 160 ) ) * 160;
    sig_14 = (double)( sig_0 ) * Gain1188;
    Jet_On_TIme_Counter_100000127_class_member13.Main14( sig_7[ 0 ], sig_13, sig_14, sig_15 );
    sig_16 = !( sig_8 || sig_15[ 0 ] );
    sig_17 = sig_16 || sig_15[ 0 ];
    sig_9 = (double)(  ( sig_17 ) ? 1 : 0  );
    Jet_Command_4[ 0 ] = sig_5[ 0 ] * sig_9;
  }
  public void Init7(  )
  {
    Value793 = 2;
    Gain913 = 0.000625000000000000010000;
    Value928 = 0.00523598775598298810000;
    Value940 = 0.0550000;
    Gain1030 = 0.50000;
    Gain1072 = 0.181818181818181850000;
    Gain1188 = 0.000625000000000000010000;
    Jet_On_TIme_Counter_100000127_class_member13.Init15(  );
    Subsystem_100000160_class_member11.Init16(  );
    Subsystem1_100000161_class_member10.Init17(  );
    Subsystem2_100000162_class_member9.Init18(  );
    Subsystem3_100000163_class_member8.Init19(  );
    Chart_member12.Init(  );
    SimpleCounter_member7.Init(  );
  }
}
