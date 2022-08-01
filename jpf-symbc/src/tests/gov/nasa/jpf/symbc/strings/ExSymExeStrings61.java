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

package gov.nasa.jpf.symbc.strings;

import gov.nasa.jpf.symbc.Debug;


public class ExSymExeStrings61 {
	static int field;

  public static void main (String[] args) {
	  String a="http://google.com/EasyChair";
	  String b = "bbb";
	  String c = "ccc";
	  String d = "ddd";
	  boolean result = test (a);
	  System.out.println(result);
	  Debug.printPC("This is the PC at the end:");
	  //a=a.concat(b);
	  
  }
  
  public static boolean test (String str){
	// (1) check that str contains "/" followed by anything not
	    // containing "/" and containing "EasyChair"
	    int lastSlash = str.lastIndexOf('/');
	    if (lastSlash < 0) {
	      return false;
	    }
	    
	    
	    String rest = str.substring(lastSlash + 1);
	    if (!rest.contains("EasyChair")) {
	      return false;
	    }
	    
	    
	 // (2) Check that str starts with "http://"
	    if (!str.startsWith("http://")) {
	      return false;
	    }
	    
	 // (3) Take the string between "http://" and the last "/".
	    // if it starts with "www." strip the "www." off
	    String t =
	        str.substring("http://".length(), lastSlash);
	    if (t.startsWith("www.")) {
	      t = t.substring("www.".length());
	    }
	    
	 // (4) Check that after stripping we have either "live.com"
	    // or "google.com"
	    if (!(t.equals("live.com")) && !(t.equals("google.com"))) {
	      return false;
	    }
	    //throw new RuntimeException("found it");
	    return true;
	    
  }

}

