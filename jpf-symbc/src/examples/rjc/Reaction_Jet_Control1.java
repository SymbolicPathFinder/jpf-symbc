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

public class Reaction_Jet_Control1 {
  private double[][] Value440 = new double[2][2];
  private double[][] Value472 = new double[2][2];
  private double[][] Value504 = new double[2][2];
  private Yaw_Control_Law2 Yaw_Control_Law_100000072_class_member3 = new Yaw_Control_Law2();
  private v_Control_Law3 v_Control_Law_100000086_class_member4 = new v_Control_Law3();
  private u_Control_Law4 u_Control_Law_100000080_class_member5 = new u_Control_Law4();

  public void Main1( double[] Attitude_Cmd__2, double[] Attitude_Meas__3, double[] Yaw_Jets_4, double[] Pitch_Roll_Jets_5 )
  {
    double[] sig_0 = new double[2];
    double[] sig_1 = new double[2];
    double sig_2 = 0;
    double sig_3 = 0;
    double sig_4 = 0;
    double sig_5 = 0;
    double sig_6 = 0;
    double sig_7 = 0;
    double sig_8 = 0;
    double sig_9 = 0;
    double sig_10 = 0;
    double sig_11 = 0;
    double sig_12 = 0;
    double sig_13 = 0;
    struct0 sig_14 = new struct0();
    struct0 sig_15 = new struct0();
    struct0 sig_16 = new struct0();
    double sig_17 = 0;
    double sig_18 = 0;
    double sig_19 = 0;
    double[] sig_20 = new double[3];
    double[][] sig_21 = new double[2][2];
    double[][] sig_22 = new double[2][2];
    double sig_23[] = new double[ 1 ];
    double[][] sig_24 = new double[2][2];
    double sig_25[] = new double[ 1 ];
    int ix447 = 0;
    int ix479 = 0;
    int ix511 = 0;
    int ix533 = 0;
    double[] sig_14_array_3 = new double[2];
    int kx589 = 0;
    double sum590 = 0;
    int ix592 = 0;
    double[] sig_15_array_6 = new double[2];
    int kx627 = 0;
    double sum628 = 0;
    int ix630 = 0;
    double[] sig_16_array_9 = new double[2];
    int kx691 = 0;
    double sum692 = 0;
    int ix694 = 0;

    ix447 = 0;
    while( ix447 < 2 )
    {
      int ix451 = 0;

      ix451 = 0;
      while( ix451 < 2 )
      {
        sig_24[ (int)( ix447 ) ][ (int)( ix451 ) ] = Value440[ (int)( ix447 ) ][ (int)( ix451 ) ];
        ++ix451;
      }

      ++ix447;
    }

    ix479 = 0;
    while( ix479 < 2 )
    {
      int ix483 = 0;

      ix483 = 0;
      while( ix483 < 2 )
      {
        sig_22[ (int)( ix479 ) ][ (int)( ix483 ) ] = Value472[ (int)( ix479 ) ][ (int)( ix483 ) ];
        ++ix483;
      }

      ++ix479;
    }

    ix511 = 0;
    while( ix511 < 2 )
    {
      int ix515 = 0;

      ix515 = 0;
      while( ix515 < 2 )
      {
        sig_21[ (int)( ix511 ) ][ (int)( ix515 ) ] = Value504[ (int)( ix511 ) ][ (int)( ix515 ) ];
        ++ix515;
      }

      ++ix511;
    }

    ix533 = 0;
    while( ix533 < 3 )
    {
      sig_20[ (int)( ix533 ) ] = Attitude_Meas__3[ (int)( ix533 ) ] - Attitude_Cmd__2[ (int)( ix533 ) ];
      ++ix533;
    }

    sig_7 = sig_20[ (int)( 0 ) ];
    sig_8 = sig_20[ (int)( 1 ) ];
    sig_9 = sig_20[ (int)( 2 ) ];
    sig_15.signal1 = sig_8;
    sig_15.signal2 = sig_9;
    sig_4 = Attitude_Meas__3[ (int)( 0 ) ];
    sig_5 = Attitude_Meas__3[ (int)( 1 ) ];
    sig_6 = Attitude_Meas__3[ (int)( 2 ) ];
    Yaw_Control_Law_100000072_class_member3.Main4( sig_7, sig_19, Yaw_Jets_4 );
    sig_14.signal1 = sig_18;
    sig_14.signal2 = sig_17;
    sig_14_array_3[ (int)( 0 ) ] = sig_14.signal1;
    sig_14_array_3[ (int)( 1 ) ] = sig_14.signal2;
    ix592 = 0;
    while( ix592 < 2 )
    {
      kx589 = 0;
      sum590 = 0;
      while( kx589 < 2 )
      {
        sum590 += sig_21[ (int)( ix592 ) ][ (int)( kx589 ) ] * sig_14_array_3[ (int)( kx589 ) ];
        ++kx589;
      }

      sig_1[ (int)( ix592 ) ] = sum590;
      ++ix592;
    }

    sig_10 = sig_1[ (int)( 0 ) ];
    sig_11 = sig_1[ (int)( 1 ) ];
    sig_15_array_6[ (int)( 0 ) ] = sig_15.signal1;
    sig_15_array_6[ (int)( 1 ) ] = sig_15.signal2;
    ix630 = 0;
    while( ix630 < 2 )
    {
      kx627 = 0;
      sum628 = 0;
      while( kx627 < 2 )
      {
        sum628 += sig_22[ (int)( ix630 ) ][ (int)( kx627 ) ] * sig_15_array_6[ (int)( kx627 ) ];
        ++kx627;
      }

      sig_0[ (int)( ix630 ) ] = sum628;
      ++ix630;
    }

    sig_12 = sig_0[ (int)( 0 ) ];
    sig_13 = sig_0[ (int)( 1 ) ];
    v_Control_Law_100000086_class_member4.Main5( sig_13, sig_11, sig_25 );
    sig_3 = sig_25[ 0 ];
    u_Control_Law_100000080_class_member5.Main6( sig_12, sig_10, sig_23 );
    sig_2 = sig_23[ 0 ];
    sig_16.signal1 = sig_2;
    sig_16.signal2 = sig_3;
    sig_16_array_9[ (int)( 0 ) ] = sig_16.signal1;
    sig_16_array_9[ (int)( 1 ) ] = sig_16.signal2;
    ix694 = 0;
    while( ix694 < 2 )
    {
      kx691 = 0;
      sum692 = 0;
      while( kx691 < 2 )
      {
        sum692 += sig_24[ (int)( ix694 ) ][ (int)( kx691 ) ] * sig_16_array_9[ (int)( kx691 ) ];
        ++kx691;
      }

      Pitch_Roll_Jets_5[ (int)( ix694 ) ] = sum692;
      ++ix694;
    }

  }
  public void Init3(  )
  {
    Value440[ (int)( 0 ) ][ (int)( 0 ) ] = 1;
    Value440[ (int)( 0 ) ][ (int)( 1 ) ] = -1;
    Value440[ (int)( 1 ) ][ (int)( 0 ) ] = 1;
    Value440[ (int)( 1 ) ][ (int)( 1 ) ] = 1;
    Value472[ (int)( 0 ) ][ (int)( 0 ) ] = 0.707107;
    Value472[ (int)( 0 ) ][ (int)( 1 ) ] = 0.707107;
    Value472[ (int)( 1 ) ][ (int)( 0 ) ] = -0.707107;
    Value472[ (int)( 1 ) ][ (int)( 1 ) ] = 0.707107;
    Value504[ (int)( 0 ) ][ (int)( 0 ) ] = 0.707107;
    Value504[ (int)( 0 ) ][ (int)( 1 ) ] = 0.707107;
    Value504[ (int)( 1 ) ][ (int)( 0 ) ] = -0.707107;
    Value504[ (int)( 1 ) ][ (int)( 1 ) ] = 0.707107;
    Yaw_Control_Law_100000072_class_member3.Init7(  );
    u_Control_Law_100000080_class_member5.Init8(  );
    v_Control_Law_100000086_class_member4.Init9(  );
  }
}
