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

public class SimpleCounter_i2 {
  public int activeSubStates[] = new int [ 1 ];
  public int TopLevel_SimpleCounter_i2_counter = 0;
  int execute_at_initialization_3132 = 0;

  final static int SIMPLECOUNTER_I20 = 0x0;
  final static int COUNTERSTATE1 = 0x1;

  public void SimpleCounter_i2_100000808_enter( int entryMode, int tpp )
  {
    if ( entryMode > -2 && entryMode <= 0 )
    {
      if ( (  ( 1 ) != 0  ) )
      {
        TopLevel_SimpleCounter_i2_counter = (int)( 0 );
        CounterState_100000809_enter( 0, SIMPLECOUNTER_I20 );
      }

    }

  }
  public void SimpleCounter_i2_100000808_exec(  )
  {
    if ( activeSubStates[ SIMPLECOUNTER_I20 & 0xFFFF ] == COUNTERSTATE1 )
    {
      CounterState_100000809_exec(  );
    }

  }
  public void SimpleCounter_i2_100000808_exit(  )
  {
    if ( activeSubStates[ SIMPLECOUNTER_I20 & 0xFFFF ] == COUNTERSTATE1 )
    {
      CounterState_100000809_exit(  );
    }

  }
  public void CounterState_100000809_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ SIMPLECOUNTER_I20 & 0xFFFF ] = COUNTERSTATE1;
    }

  }
  public void CounterState_100000809_exec(  )
  {
    if ( (  ( 1 ) != 0  ) )
    {
      ++TopLevel_SimpleCounter_i2_counter;
      CounterState_100000809_exit(  );
      CounterState_100000809_enter( 0, COUNTERSTATE1 );
    }

  }
  public void CounterState_100000809_exit(  )
  {
    activeSubStates[ SIMPLECOUNTER_I20 & 0xFFFF ] = -COUNTERSTATE1;
  }
  public void Main( int[] counter_ )
  {
    if ( execute_at_initialization_3132==1 )
    {
      SimpleCounter_i2_100000808_exec(  );
    }

    execute_at_initialization_3132 = 1;
    {
      counter_[ 0 ] = TopLevel_SimpleCounter_i2_counter;
    }
  }
  public void Init(  )
  {
    int i = 0;

    i = 0;
    while( i < 1 )
    {
      activeSubStates[ (int)( i ) ] = 0;
      ++i;
    }

    TopLevel_SimpleCounter_i2_counter = (int)( 0 );
    execute_at_initialization_3132 = (int)( 0 );
    SimpleCounter_i2_100000808_enter( -1, 0 );
  }
}
