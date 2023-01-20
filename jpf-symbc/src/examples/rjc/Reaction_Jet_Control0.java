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

public class Reaction_Jet_Control0 {
  private double[][] Value431 = new double[2][2];
  private double[][] Value463 = new double[2][2];
  private double[][] Value495 = new double[2][2];
  private double[] NumeratorCoefficients_3554 = new double[2];
  private double[] DenominatorCoefficients_4556 = new double[2];
  private double NumeratorTerms_5557 = 0;
  private double DenominatorTerms_6558 = 0;
  private double[] NumeratorCoefficients_7588 = new double[2];
  private double[] DenominatorCoefficients_8590 = new double[2];
  private double NumeratorTerms_9591 = 0;
  private double DenominatorTerms_10592 = 0;
  private double[] NumeratorCoefficients_11614 = new double[2];
  private double[] DenominatorCoefficients_12616 = new double[2];
  private double NumeratorTerms_13617 = 0;
  private double DenominatorTerms_14618 = 0;
  private Yaw_Control_Law1 Yaw_Control_Law_100000076_class_member15 = new Yaw_Control_Law1();
  private v_Control_Law2 v_Control_Law_100000084_class_member16 = new v_Control_Law2();
  private u_Control_Law3 u_Control_Law_100000081_class_member17 = new u_Control_Law3();

  public void Main1( double[] Attitude_Cmd__2, double[] Attitude_Meas__3, double[] Yaw_Jets_4, double[] Pitch_Roll_Jets_5 )
  {
	  System.out.println("in Reaction_Jet_Control0");
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
    int ix438 = 0;
    int ix470 = 0;
    int ix502 = 0;
    int ix524 = 0;
    double[] sig_14_array_15 = new double[2];
    int kx658 = 0;
    double sum659 = 0;
    int ix661 = 0;
    double[] sig_15_array_18 = new double[2];
    int kx696 = 0;
    double sum697 = 0;
    int ix699 = 0;
    double[] sig_16_array_21 = new double[2];
    int kx760 = 0;
    double sum761 = 0;
    int ix763 = 0;

    ix438 = 0;
    while( ix438 < 2 )
    {
      int ix442 = 0;

      ix442 = 0;
      while( ix442 < 2 )
      {
        sig_24[ (int)( ix438 ) ][ (int)( ix442 ) ] = Value431[ (int)( ix438 ) ][ (int)( ix442 ) ];
        ++ix442;
      }

      ++ix438;
    }

    ix470 = 0;
    while( ix470 < 2 )
    {
      int ix474 = 0;

      ix474 = 0;
      while( ix474 < 2 )
      {
        sig_22[ (int)( ix470 ) ][ (int)( ix474 ) ] = Value463[ (int)( ix470 ) ][ (int)( ix474 ) ];
        ++ix474;
      }

      ++ix470;
    }

    ix502 = 0;
    while( ix502 < 2 )
    {
      int ix506 = 0;

      ix506 = 0;
      while( ix506 < 2 )
      {
        sig_21[ (int)( ix502 ) ][ (int)( ix506 ) ] = Value495[ (int)( ix502 ) ][ (int)( ix506 ) ];
        ++ix506;
      }

      ++ix502;
    }

    ix524 = 0;
    while( ix524 < 3 )
    {
      sig_20[ (int)( ix524 ) ] = Attitude_Meas__3[ (int)( ix524 ) ] - Attitude_Cmd__2[ (int)( ix524 ) ];
      ++ix524;
    }

    sig_7 = sig_20[ (int)( 0 ) ];
    sig_8 = sig_20[ (int)( 1 ) ];
    sig_9 = sig_20[ (int)( 2 ) ];
    sig_15.signal1 = sig_8;
    sig_15.signal2 = sig_9;
    sig_4 = Attitude_Meas__3[ (int)( 0 ) ];
    sig_5 = Attitude_Meas__3[ (int)( 1 ) ];
    sig_6 = Attitude_Meas__3[ (int)( 2 ) ];
    sig_19 = ( NumeratorCoefficients_3554[ (int)( 0 ) ] * sig_4 + NumeratorCoefficients_3554[ (int)( 1 ) ] * NumeratorTerms_5557 - DenominatorCoefficients_4556[ (int)( 1 ) ] * DenominatorTerms_6558 ) / DenominatorCoefficients_4556[ (int)( 0 ) ];
    NumeratorTerms_5557 = sig_4;
    DenominatorTerms_6558 = sig_19;
    Yaw_Control_Law_100000076_class_member15.Main4( sig_7, sig_19, Yaw_Jets_4 );
    sig_18 = ( NumeratorCoefficients_7588[ (int)( 0 ) ] * sig_5 + NumeratorCoefficients_7588[ (int)( 1 ) ] * NumeratorTerms_9591 - DenominatorCoefficients_8590[ (int)( 1 ) ] * DenominatorTerms_10592 ) / DenominatorCoefficients_8590[ (int)( 0 ) ];
    NumeratorTerms_9591 = sig_5;
    DenominatorTerms_10592 = sig_18;
    sig_17 = ( NumeratorCoefficients_11614[ (int)( 0 ) ] * sig_6 + NumeratorCoefficients_11614[ (int)( 1 ) ] * NumeratorTerms_13617 - DenominatorCoefficients_12616[ (int)( 1 ) ] * DenominatorTerms_14618 ) / DenominatorCoefficients_12616[ (int)( 0 ) ];
    NumeratorTerms_13617 = sig_6;
    DenominatorTerms_14618 = sig_17;
    sig_14.signal1 = sig_18;
    sig_14.signal2 = sig_17;
    sig_14_array_15[ (int)( 0 ) ] = sig_14.signal1;
    sig_14_array_15[ (int)( 1 ) ] = sig_14.signal2;
    ix661 = 0;
    while( ix661 < 2 )
    {
      kx658 = 0;
      sum659 = 0;
      while( kx658 < 2 )
      {
        sum659 += sig_21[ (int)( ix661 ) ][ (int)( kx658 ) ] * sig_14_array_15[ (int)( kx658 ) ];
        ++kx658;
      }

      sig_1[ (int)( ix661 ) ] = sum659;
      ++ix661;
    }

    sig_10 = sig_1[ (int)( 0 ) ];
    sig_11 = sig_1[ (int)( 1 ) ];
    sig_15_array_18[ (int)( 0 ) ] = sig_15.signal1;
    sig_15_array_18[ (int)( 1 ) ] = sig_15.signal2;
    ix699 = 0;
    while( ix699 < 2 )
    {
      kx696 = 0;
      sum697 = 0;
      while( kx696 < 2 )
      {
        sum697 += sig_22[ (int)( ix699 ) ][ (int)( kx696 ) ] * sig_15_array_18[ (int)( kx696 ) ];
        ++kx696;
      }

      sig_0[ (int)( ix699 ) ] = sum697;
      ++ix699;
    }

    sig_12 = sig_0[ (int)( 0 ) ];
    sig_13 = sig_0[ (int)( 1 ) ];
    v_Control_Law_100000084_class_member16.Main5( sig_13, sig_11, sig_25 );
    sig_3 = sig_25[ 0 ];
    u_Control_Law_100000081_class_member17.Main6( sig_12, sig_10, sig_23 );
    sig_2 = sig_23[ 0 ];
    sig_16.signal1 = sig_2;
    sig_16.signal2 = sig_3;
    sig_16_array_21[ (int)( 0 ) ] = sig_16.signal1;
    sig_16_array_21[ (int)( 1 ) ] = sig_16.signal2;
    ix763 = 0;
    while( ix763 < 2 )
    {
      kx760 = 0;
      sum761 = 0;
      while( kx760 < 2 )
      {
        sum761 += sig_24[ (int)( ix763 ) ][ (int)( kx760 ) ] * sig_16_array_21[ (int)( kx760 ) ];
        ++kx760;
      }

      Pitch_Roll_Jets_5[ (int)( ix763 ) ] = sum761;
      ++ix763;
    }

  }
  public void Init3(  )
  {
    Value431[ (int)( 0 ) ][ (int)( 0 ) ] = 1;
    Value431[ (int)( 0 ) ][ (int)( 1 ) ] = -1;
    Value431[ (int)( 1 ) ][ (int)( 0 ) ] = 1;
    Value431[ (int)( 1 ) ][ (int)( 1 ) ] = 1;
    Value463[ (int)( 0 ) ][ (int)( 0 ) ] = 0.707106781186547570000;
    Value463[ (int)( 0 ) ][ (int)( 1 ) ] = 0.707106781186547570000;
    Value463[ (int)( 1 ) ][ (int)( 0 ) ] = -0.707106781186547570000;
    Value463[ (int)( 1 ) ][ (int)( 1 ) ] = 0.707106781186547570000;
    Value495[ (int)( 0 ) ][ (int)( 0 ) ] = 0.707106781186547570000;
    Value495[ (int)( 0 ) ][ (int)( 1 ) ] = 0.707106781186547570000;
    Value495[ (int)( 1 ) ][ (int)( 0 ) ] = -0.707106781186547570000;
    Value495[ (int)( 1 ) ][ (int)( 1 ) ] = 0.707106781186547570000;
    NumeratorCoefficients_3554[ (int)( 0 ) ] = 10;
    NumeratorCoefficients_3554[ (int)( 1 ) ] = -10;
    DenominatorCoefficients_4556[ (int)( 0 ) ] = 1;
    DenominatorCoefficients_4556[ (int)( 1 ) ] = 0;
    NumeratorTerms_5557 = 0;
    DenominatorTerms_6558 = 0;
    NumeratorCoefficients_7588[ (int)( 0 ) ] = 10;
    NumeratorCoefficients_7588[ (int)( 1 ) ] = -10;
    DenominatorCoefficients_8590[ (int)( 0 ) ] = 1;
    DenominatorCoefficients_8590[ (int)( 1 ) ] = 0;
    NumeratorTerms_9591 = 0;
    DenominatorTerms_10592 = 0;
    NumeratorCoefficients_11614[ (int)( 0 ) ] = 10;
    NumeratorCoefficients_11614[ (int)( 1 ) ] = -10;
    DenominatorCoefficients_12616[ (int)( 0 ) ] = 1;
    DenominatorCoefficients_12616[ (int)( 1 ) ] = 0;
    NumeratorTerms_13617 = 0;
    DenominatorTerms_14618 = 0;
    Yaw_Control_Law_100000076_class_member15.Init7(  );
    u_Control_Law_100000081_class_member17.Init8(  );
    v_Control_Law_100000084_class_member16.Init9(  );
  }
}
