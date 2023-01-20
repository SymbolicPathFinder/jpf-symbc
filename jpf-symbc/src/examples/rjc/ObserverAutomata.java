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

public class ObserverAutomata {
  public int activeSubStates[] = new int [ 1 ];
  int execute_at_initialization_1974 = 0;
  private double TopLevel_ObserverAutomata_tjcalc = 0;

  final static int OBSERVERAUTOMATA0 = 0x0;
  final static int OK1 = 0x1;
  final static int BAD2 = 0x2;

  public void ObserverAutomata_100000523_enter( int entryMode, int tpp )
  {
    if ( entryMode > -2 && entryMode <= 0 )
    {
      if ( (  ( 1 ) != 0  ) )
      {
        if ( TopLevel_ObserverAutomata_tjcalc > 0 )
        {
          OK_100000524_enter( 0, OBSERVERAUTOMATA0 );
        }
        else if ( (  ( 1 ) != 0  ) )
        {
          Bad_100000525_enter( 0, OBSERVERAUTOMATA0 );
        }

      }

    }
  }
  public void ObserverAutomata_100000523_exec(  )
  {
    if ( activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] == OK1 )
    {
      OK_100000524_exec(  );
    }

  }
  public void ObserverAutomata_100000523_exit(  )
  {
    if ( activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] == OK1 )
    {
      OK_100000524_exit(  );
    }
    else if ( activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] == BAD2 )
    {
      Bad_100000525_exit(  );
    }

  }
  public void OK_100000524_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] = OK1;
    }

  }
  public void OK_100000524_exec(  )
  {

    if ( TopLevel_ObserverAutomata_tjcalc > 0 )
    {
      OK_100000524_exit(  );
      OK_100000524_enter( 0, OK1 );
    }

    else if ( (  ( 1 ) != 0  ) )
    {
      OK_100000524_exit(  );
      Bad_100000525_enter( 0, OBSERVERAUTOMATA0 );
    }
  }
  public void OK_100000524_exit(  )
  {
    activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] = -OK1;
  }
  public void Bad_100000525_enter( int entryMode, int tpp )
  {
    if ( entryMode <= 0 )
    {
      activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] = BAD2;
    }

  }
  public void Bad_100000525_exit(  )
  {
    activeSubStates[ OBSERVERAUTOMATA0 & 0xFFFF ] = -BAD2;
  }
  public void Main( double tjcalc_ )
  {
    {
      TopLevel_ObserverAutomata_tjcalc = tjcalc_;
    }
    if ( execute_at_initialization_1974==1 )
    {
      ObserverAutomata_100000523_exec(  );
    }

    execute_at_initialization_1974 = 1;
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

    TopLevel_ObserverAutomata_tjcalc = 0;
    execute_at_initialization_1974 = (int)( 0 );
    ObserverAutomata_100000523_enter( -1, 0 );
  }
}
