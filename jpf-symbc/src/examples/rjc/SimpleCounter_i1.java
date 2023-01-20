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

public class SimpleCounter_i1 {
  public int activeSubStates[] = new int [ 1 ];
  public int TopLevel_SimpleCounter_i1_counter = 0;
  int execute_at_initialization_2130 = 0;

  final static int SIMPLECOUNTER_I10 = 0x0;
  final static int COUNTERSTATE1 = 0x1;

  public void SimpleCounter_i1_100000539_enter( int entryMode, int tpp )
  {
    if ( entryMode > -2 && entryMode <= 0 )
    {
      if ( (  ( 1 ) != 0  ) )
      {
        TopLevel_SimpleCounter_i1_counter = (int)( 0 );
        CounterState_100000540_enter( 0, SIMPLECOUNTER_I10 );
      }

    }

  }
  public void SimpleCounter_i1_100000539_exec(  )
  {
    if ( activeSubStates[ SIMPLECOUNTER_I10 & 0xFFFF ] == COUNTERSTATE1 )
    {
      CounterState_100000540_exec(  );
    }

  }
  public void SimpleCounter_i1_100000539_exit(  )
  {
    if ( activeSubStates[ SIMPLECOUNTER_I10 & 0xFFFF ] == COUNTERSTATE1 )
    {
      CounterState_100000540_exit(  );
    }

  }
  public void CounterState_100000540_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ SIMPLECOUNTER_I10 & 0xFFFF ] = COUNTERSTATE1;
    }

  }
  public void CounterState_100000540_exec(  )
  {
    if ( (  ( 1 ) != 0  ) )
    {
      ++TopLevel_SimpleCounter_i1_counter;
      CounterState_100000540_exit(  );
      CounterState_100000540_enter( 0, COUNTERSTATE1 );
    }

  }
  public void CounterState_100000540_exit(  )
  {
    activeSubStates[ SIMPLECOUNTER_I10 & 0xFFFF ] = -COUNTERSTATE1;
  }
  public void Main( int[] counter_ )
  {
    if ( execute_at_initialization_2130==1 )
    {
      SimpleCounter_i1_100000539_exec(  );
    }

    execute_at_initialization_2130 = 1;
    {
      counter_[ 0 ] = TopLevel_SimpleCounter_i1_counter;
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

    TopLevel_SimpleCounter_i1_counter = (int)( 0 );
    execute_at_initialization_2130 = (int)( 0 );
    SimpleCounter_i1_100000539_enter( -1, 0 );
  }
}
