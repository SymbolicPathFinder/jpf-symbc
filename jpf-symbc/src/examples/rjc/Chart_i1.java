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

public class Chart_i1 {
  public int activeSubStates[] = new int [ 1 ];
  public double TopLevel_Chart_i1_jets = 0;
  public double TopLevel_Chart_i1_enable = 0;
  public double TopLevel_Chart_i1_ton = 0;
  double TopLevel_Chart_i1_tmin = 0;
  double TopLevel_Chart_i1_delt = 0.1;
  double TopLevel_Chart_i1_count = 0;
  int execute_at_initialization_1466 = 0;
  private double TopLevel_Chart_i1_Firefct2 = 0;
  private double[] TopLevel_Chart_i1_e = new double[2];
  private double TopLevel_Chart_i1_Nofjets = 0;
  private double TopLevel_Chart_i1_Coastfct1 = 0;
  private double TopLevel_Chart_i1_Firefct1 = 0;
  private double TopLevel_Chart_i1_Coastfct2 = 0;
  private double TopLevel_Chart_i1_tjcalc1 = 0;
  private double TopLevel_Chart_i1_tjcalc = 0;

  final static int CHART_I10 = 0x0;
  final static int WAIT_FOR_STABLE_RATE1 = 0x1;
  final static int START2 = 0x2;
  final static int FIRE_REGION_13 = 0x3;
  final static int COAST_REGION_24 = 0x4;
  final static int SKIP_A_SAMPLE_25 = 0x5;
  final static int SKIP_A_SAMPLE_16 = 0x6;
  final static int COAST_REGION_17 = 0x7;
  final static int FIRE_REGION_28 = 0x8;

  public void Chart_i1_100000471_enter( int entryMode, int tpp )
  {
    if ( entryMode > -2 && entryMode <= 0 )
    {
      if ( (  ( 1 ) != 0  ) )
      {
        TopLevel_Chart_i1_count = 2;
        Wait_for_stable_rate_100000472_enter( 0, CHART_I10 );
      }

    }

  }
  public void Chart_i1_100000471_exec(  )
  {
    if ( activeSubStates[ CHART_I10 & 0xFFFF ] == WAIT_FOR_STABLE_RATE1 )
    {
      Wait_for_stable_rate_100000472_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == START2 )
    {
      Start_100000473_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == FIRE_REGION_13 )
    {
      Fire_region_1_100000474_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == COAST_REGION_24 )
    {
      Coast_region_2_100000475_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == SKIP_A_SAMPLE_25 )
    {
      Skip_a_Sample_2_100000476_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == SKIP_A_SAMPLE_16 )
    {
      Skip_a_Sample_1_100000477_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == COAST_REGION_17 )
    {
      Coast_region_1_100000478_exec(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == FIRE_REGION_28 )
    {
      Fire_region_2_100000479_exec(  );
    }

  }
  public void Chart_i1_100000471_exit(  )
  {
    if ( activeSubStates[ CHART_I10 & 0xFFFF ] == WAIT_FOR_STABLE_RATE1 )
    {
      Wait_for_stable_rate_100000472_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == START2 )
    {
      Start_100000473_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == FIRE_REGION_13 )
    {
      Fire_region_1_100000474_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == COAST_REGION_24 )
    {
      Coast_region_2_100000475_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == SKIP_A_SAMPLE_25 )
    {
      Skip_a_Sample_2_100000476_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == SKIP_A_SAMPLE_16 )
    {
      Skip_a_Sample_1_100000477_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == COAST_REGION_17 )
    {
      Coast_region_1_100000478_exit(  );
    }
    else if ( activeSubStates[ CHART_I10 & 0xFFFF ] == FIRE_REGION_28 )
    {
      Fire_region_2_100000479_exit(  );
    }

  }
  public void Wait_for_stable_rate_100000472_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = WAIT_FOR_STABLE_RATE1;
    }

  }
  public void Wait_for_stable_rate_100000472_exec(  )
  {
    if ( TopLevel_Chart_i1_count==0 )
    {
      Wait_for_stable_rate_100000472_exit(  );
      Start_100000473_enter( 0, CHART_I10 );
    }
    else if ( (  ( 1 ) != 0  ) )
    {
      Wait_for_stable_rate_100000472_exit(  );
      --TopLevel_Chart_i1_count;
      Wait_for_stable_rate_100000472_enter( 0, WAIT_FOR_STABLE_RATE1 );
    }

  }
  public void Wait_for_stable_rate_100000472_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -WAIT_FOR_STABLE_RATE1;
  }
  public void Start_100000473_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = START2;
    }

  }
  public void Start_100000473_exec(  )
  {
    if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] < 0 && TopLevel_Chart_i1_Firefct2 < 0 || TopLevel_Chart_i1_e[ (int)( 1 ) ] > 0 && TopLevel_Chart_i1_Coastfct2 > 0 )
    {
      Start_100000473_exit(  );
      Fire_region_2_100000479_enter( 0, CHART_I10 );
    }
    else if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] > 0 && TopLevel_Chart_i1_Coastfct2 >= 0 && TopLevel_Chart_i1_Firefct1 < 0 )
    {
      Start_100000473_exit(  );
      Coast_region_2_100000475_enter( 0, CHART_I10 );
    }
    else if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] > 0 && TopLevel_Chart_i1_Firefct1 > 0 || TopLevel_Chart_i1_e[ (int)( 1 ) ] < 0 && TopLevel_Chart_i1_Coastfct1 < 0 )
    {
      Start_100000473_exit(  );
      Fire_region_1_100000474_enter( 0, CHART_I10 );
    }
    else if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] < 0 && TopLevel_Chart_i1_Coastfct1 <= 0 && TopLevel_Chart_i1_Firefct2 > 0 )
    {
      Start_100000473_exit(  );
      Coast_region_1_100000478_enter( 0, CHART_I10 );
    }

  }
  public void Start_100000473_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -START2;
  }
  public void Fire_region_1_100000474_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = FIRE_REGION_13;
      TopLevel_Chart_i1_jets = -TopLevel_Chart_i1_Nofjets;
      TopLevel_Chart_i1_ton = TopLevel_Chart_i1_tjcalc + TopLevel_Chart_i1_tjcalc1;
    }

  }
  public void Fire_region_1_100000474_exec(  )
  {
    if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] < 0 && TopLevel_Chart_i1_Coastfct1 <= 0 )
    {
      Fire_region_1_100000474_exit(  );
      Coast_region_1_100000478_enter( 0, CHART_I10 );
    }

    else if ( TopLevel_Chart_i1_ton < (double)( 2 ) * TopLevel_Chart_i1_delt )
    {
      TopLevel_Chart_i1_enable = 1;
      if ( TopLevel_Chart_i1_ton > TopLevel_Chart_i1_tmin )
      {
        TopLevel_Chart_i1_count = 2;
        Fire_region_1_100000474_exit(  );
        Skip_a_Sample_1_100000477_enter( 0, CHART_I10 );
      }
      else if ( (  ( 1 ) != 0  ) )
      {
        TopLevel_Chart_i1_enable = 0;
        Fire_region_1_100000474_exit(  );
        Coast_region_1_100000478_enter( 0, CHART_I10 );
      }

    }

    else if ( (  ( 1 ) != 0  ) )
    {
      Fire_region_1_100000474_exit(  );
      Fire_region_1_100000474_enter( 0, FIRE_REGION_13 );
    }

  }
  public void Fire_region_1_100000474_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -FIRE_REGION_13;
  }
  public void Coast_region_2_100000475_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = COAST_REGION_24;
      TopLevel_Chart_i1_jets = 0;
      TopLevel_Chart_i1_ton = 0;
      TopLevel_Chart_i1_enable = 0;
    }

  }
  public void Coast_region_2_100000475_exec(  )
  {
    if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] > 0 && TopLevel_Chart_i1_Firefct1 > 0 )
    {
      Coast_region_2_100000475_exit(  );
      Fire_region_1_100000474_enter( 0, CHART_I10 );
    }

  }
  public void Coast_region_2_100000475_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -COAST_REGION_24;
  }
  public void Skip_a_Sample_2_100000476_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = SKIP_A_SAMPLE_25;
      --TopLevel_Chart_i1_count;
    }

  }
  public void Skip_a_Sample_2_100000476_exec(  )
  {
    if ( TopLevel_Chart_i1_count==0 )
    {
      Skip_a_Sample_2_100000476_exit(  );
      Coast_region_2_100000475_enter( 0, CHART_I10 );
    }
    else if ( (  ( 1 ) != 0  ) )
    {
      Skip_a_Sample_2_100000476_exit(  );
      TopLevel_Chart_i1_ton -= TopLevel_Chart_i1_delt;
      Skip_a_Sample_2_100000476_enter( 0, SKIP_A_SAMPLE_25 );
    }

  }
  public void Skip_a_Sample_2_100000476_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -SKIP_A_SAMPLE_25;
  }
  public void Skip_a_Sample_1_100000477_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = SKIP_A_SAMPLE_16;
      --TopLevel_Chart_i1_count;
    }

  }
  public void Skip_a_Sample_1_100000477_exec(  )
  {
    if ( TopLevel_Chart_i1_count==0 )
    {
      Skip_a_Sample_1_100000477_exit(  );
      Coast_region_1_100000478_enter( 0, CHART_I10 );
    }
    else if ( (  ( 1 ) != 0  ) )
    {
      Skip_a_Sample_1_100000477_exit(  );
      TopLevel_Chart_i1_ton -= TopLevel_Chart_i1_delt;
      Skip_a_Sample_1_100000477_enter( 0, SKIP_A_SAMPLE_16 );
    }

  }
  public void Skip_a_Sample_1_100000477_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -SKIP_A_SAMPLE_16;
  }
  public void Coast_region_1_100000478_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = COAST_REGION_17;
      TopLevel_Chart_i1_jets = 0;
      TopLevel_Chart_i1_ton = 0;
      TopLevel_Chart_i1_enable = 0;
    }

  }
  public void Coast_region_1_100000478_exec(  )
  {
    if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] < 0 && TopLevel_Chart_i1_Firefct2 < 0 )
    {
      Coast_region_1_100000478_exit(  );
      Fire_region_2_100000479_enter( 0, CHART_I10 );
    }

  }
  public void Coast_region_1_100000478_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -COAST_REGION_17;
  }
  public void Fire_region_2_100000479_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ CHART_I10 & 0xFFFF ] = FIRE_REGION_28;
      TopLevel_Chart_i1_jets = TopLevel_Chart_i1_Nofjets;
      TopLevel_Chart_i1_ton = TopLevel_Chart_i1_tjcalc - TopLevel_Chart_i1_tjcalc1;
    }

  }
  public void Fire_region_2_100000479_exec(  )
  {
    if ( TopLevel_Chart_i1_ton < (double)( 2 ) * TopLevel_Chart_i1_delt )
    {
      TopLevel_Chart_i1_enable = 1;
      if ( TopLevel_Chart_i1_ton > TopLevel_Chart_i1_tmin )
      {
        TopLevel_Chart_i1_count = 2;
        Fire_region_2_100000479_exit(  );
        Skip_a_Sample_2_100000476_enter( 0, CHART_I10 );
      }
      else if ( (  ( 1 ) != 0  ) )
      {
        TopLevel_Chart_i1_enable = 0;
        Fire_region_2_100000479_exit(  );
        Coast_region_2_100000475_enter( 0, CHART_I10 );
      }

    }
    else if ( TopLevel_Chart_i1_e[ (int)( 1 ) ] > 0 && TopLevel_Chart_i1_Coastfct2 > 0 )
    {
      Fire_region_2_100000479_exit(  );
      Coast_region_2_100000475_enter( 0, CHART_I10 );
    }
    else if ( (  ( 1 ) != 0  ) )
    {
      Fire_region_2_100000479_exit(  );
      Fire_region_2_100000479_enter( 0, FIRE_REGION_28 );
    }

  }
  public void Fire_region_2_100000479_exit(  )
  {
    activeSubStates[ CHART_I10 & 0xFFFF ] = -FIRE_REGION_28;
  }
  public void Main( double Nofjets_, double[] e_, double Firefct1_, double Coastfct1_, double Firefct2_, double Coastfct2_, double tjcalc1_, double tjcalc_, double[] jets_, double[] enable_, double[] ton_ )
  {
    {
      TopLevel_Chart_i1_Nofjets = Nofjets_;
    }
    {
      int ix1006;
      for( ix1006 = 0 ; ix1006 < 2 ; ++ix1006 )
      {
        TopLevel_Chart_i1_e[ix1006] = e_[ix1006];
      }
    }
    {
      TopLevel_Chart_i1_Firefct1 = Firefct1_;
    }
    {
      TopLevel_Chart_i1_Coastfct1 = Coastfct1_;
    }
    {
      TopLevel_Chart_i1_Firefct2 = Firefct2_;
    }
    {
      TopLevel_Chart_i1_Coastfct2 = Coastfct2_;
    }
    {
      TopLevel_Chart_i1_tjcalc1 = tjcalc1_;
    }
    {
      TopLevel_Chart_i1_tjcalc = tjcalc_;
    }
    if ( execute_at_initialization_1466==1 )
    {
      Chart_i1_100000471_exec(  );
    }

    execute_at_initialization_1466 = 1;
    {
      jets_[ 0 ] = TopLevel_Chart_i1_jets;
    }
    {
      enable_[ 0 ] = TopLevel_Chart_i1_enable;
    }
    {
      ton_[ 0 ] = TopLevel_Chart_i1_ton;
    }
  }
  public void Init(  )
  {
    int i = 0;
    int ix1505 = 0;

    i = 0;
    while( i < 1 )
    {
      activeSubStates[ (int)( i ) ] = 0;
      ++i;
    }

    TopLevel_Chart_i1_Firefct2 = 0;
    TopLevel_Chart_i1_jets = 0;
    ix1505 = 0;
    while( ix1505 < 2 )
    {
      TopLevel_Chart_i1_e[ (int)( ix1505 ) ] = 0;
      ++ix1505;
    }

    TopLevel_Chart_i1_Nofjets = 0;
    TopLevel_Chart_i1_enable = 0;
    TopLevel_Chart_i1_ton = 0;
    TopLevel_Chart_i1_Coastfct1 = 0;
    TopLevel_Chart_i1_Firefct1 = 0;
    TopLevel_Chart_i1_Coastfct2 = 0;
    TopLevel_Chart_i1_tjcalc1 = 0;
    TopLevel_Chart_i1_tjcalc = 0;
    TopLevel_Chart_i1_tmin = 0.0140;
    TopLevel_Chart_i1_delt = 0.1;
    TopLevel_Chart_i1_count = 0;
    execute_at_initialization_1466 = (int)( 0 );
    Chart_i1_100000471_enter( -1, 0 );
  }
}
