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

package concolic;
import gov.nasa.jpf.symbc.Concrete;
// Bessel example taken from:
// http://www.nag.com/IndustryArticles/pontjavafiles.zip
import gov.nasa.jpf.symbc.Partition;

// The Bessel.java file

public class Bessel
{

	/*
	 	Y0(1.0) is 0.08825696421567698
		Y0(1.25) is 0.2582168515945408
		Y0(1.5) is 0.38244892379775897
		Y0(1.75) is 0.465492628646906
		Y0(2.0) is 0.5103756726497451
		Y0(2.25) is 0.5200647624572782
		Y0(2.5) is 0.49807035961523183
		Y0(2.75) is 0.4486587215691319
		Y0(3.0) is 0.3768500100127904
		Y0(3.25) is 0.2882869026730871
	 */



  // Declaration of the Native (C) function
@Concrete("true")
 public static native double bessely0(double x);

  //@Concrete("true")
  public static double bessely0test(double x) {
	  if(x==1.0) return 0.08825696421567698;
	  if(x==1.25) return 0.2582168515945408;
      if(x==1.5) return 0.38244892379775897;
	  if(x==1.75) return 0.465492628646906;
	  if(x==2.0) return 0.5103756726497451;
	  if(x==2.25) return 0.5200647624572782;
	  if(x==2.5) return 0.49807035961523183;
	  if(x==2.75) return 0.4486587215691319;
	  if(x==3.0) return 0.3768500100127904;
	  if(x==3.25) return 0.2882869026730871;
	  return 1.0;
  }

  static
    {
      System.loadLibrary("CJavaInterface");
    }


  public static void main(String[] args)
    {
      run_bessel(0.0);
      for(int i=0; i<100;i++)
    	  System.out.println("Y0 "+i + " " + y0(i));

    }

  public static void run_bessel(double x) {
      	System.out.println("Calls of Y0 Bessel function routine bessely0");

      	double y;
      	y = y0(x); //bessely0(x);

      	if(x >= 1.25 && y > 0.2)
      		System.out.println("!!!!!!!!!!! br1");
      	else
      		System.out.println("!!!!!!!!!!! br2");
  }

  //@Concrete("true")
 // @Concrete("true")
  //@Partition({"x>=1.25","x>0.0"})
  public static double y0(double x) {
	  double result = bessely0(x); //bessely0test(x);
	  System.out.println("Invoking concrete y0 "+ x + " " + result );
	  return result;
  }
}
