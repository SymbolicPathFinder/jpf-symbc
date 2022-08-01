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

public class u_Control_Law3 {
  private double Value797 = 0;
  private double Gain918 = 0;
  private double Value932 = 0;
  private double Value944 = 0;
  private double Gain1035 = 0;
  private double Gain1077 = 0;
  private double Gain1210 = 0;
  private SimpleCounter SimpleCounter_member7 = new SimpleCounter();
  private Subsystem312 Subsystem3_100000434_class_member8 = new Subsystem312();
  private Subsystem213 Subsystem2_100000433_class_member9 = new Subsystem213();
  private Subsystem114 Subsystem1_100000432_class_member10 = new Subsystem114();
  private Subsystem15 Subsystem_100000431_class_member11 = new Subsystem15();
  private ObserverAutomata ObserverAutomata_member12 = new ObserverAutomata();
  private Chart Chart_member13 = new Chart();
  private Jet_On_TIme_Counter18 Jet_On_TIme_Counter_100000397_class_member14 = new Jet_On_TIme_Counter18();

  public void Main6( double Position_2, double Rate_3, double[] Jet_Command_4 )
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
    int ix985 = 0;
    int ix_27 = 0;
    int ix_30 = 0;

    SimpleCounter_member7.Main( sig_22 );
    sig_19 = Value797;
    sig_18[ (int)( 0 ) ] = Position_2;
    sig_18[ (int)( 1 ) ] = Rate_3;
    Subsystem3_100000434_class_member8.Main20( sig_18, sig_19, sig_28 );
    Subsystem2_100000433_class_member9.Main21( sig_18, sig_19, sig_27 );
    Subsystem1_100000432_class_member10.Main22( sig_18, sig_19, sig_26 );
    Subsystem_100000431_class_member11.Main23( sig_18, sig_19, sig_25 );
    sig_13 = (double)( sig_22[ 0 ] ) * Gain918;
    sig_10 = Value932;
    sig_4 = Value944;
    sig_12 = (double)( 1 ) / sig_19 / sig_4 * sig_10;
    ix985 = 0;
    while( ix985 < 2 )
    {
      sig_11[ (int)( ix985 ) ] = sig_18[ (int)( ix985 ) ] / sig_4 / sig_19;
      ++ix985;
    }

    sig_21 = sig_11[ (int)( 1 ) ];
    sig_23 = sig_21 * sig_21;
    sig_30 = sig_23 * Gain1035;
    sig_20 = sig_11[ (int)( 0 ) ];
    sig_3 = (double)( Math.abs( sig_20 ) );
    sig_29 = sig_30 + sig_3 - sig_12;
    sig_1 = sig_29 * Gain1077;
    sig_2 = sig_1 * (  ( sig_1 >= 0 ) ? 1 : 0  );
    sig_24 = (double)( Math.sqrt( sig_2 ) );
    ObserverAutomata_member12.Main( sig_24 );
    Chart_member13.Main( sig_19, sig_18, sig_25[ 0 ], sig_26[ 0 ], sig_27[ 0 ], sig_28[ 0 ], sig_21, sig_24, sig_5, sig_6, sig_7 );
    sig_8 = sig_6[ 0 ] != 0;
    sig_0 = (int)( Math.floor( sig_22[ 0 ] / 160 ) ) * 160;
    sig_14 = (double)( sig_0 ) * Gain1210;
    Jet_On_TIme_Counter_100000397_class_member14.Main24( sig_7[ 0 ], sig_13, sig_14, sig_15 );
    sig_16 = !( sig_8 || sig_15[ 0 ] );
    sig_17 = sig_16 || sig_15[ 0 ];
    sig_9 = (double)(  ( sig_17 ) ? 1 : 0  );
    Jet_Command_4[ 0 ] = sig_5[ 0 ] * sig_9;
  }
  public void Init8(  )
  {
    Value797 = 2;
    Gain918 = 0.000625000000000000010000;
    Value932 = 0.00523598775598298810000;
    Value944 = 0.00628553390593273790000;
    Gain1035 = 0.50000;
    Gain1077 = 0.181818181818181850000;
    Gain1210 = 0.000625000000000000010000;
    Jet_On_TIme_Counter_100000397_class_member14.Init25(  );
    Subsystem_100000431_class_member11.Init26(  );
    Subsystem1_100000432_class_member10.Init27(  );
    Subsystem2_100000433_class_member9.Init28(  );
    Subsystem3_100000434_class_member8.Init29(  );
    Chart_member13.Init(  );
    ObserverAutomata_member12.Init(  );
    SimpleCounter_member7.Init(  );
  }
}
