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

//
//Copyright (C) 2006 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package java.lang;

public class Math {

	/**
	 * The value of <i><b>PI</b></i> as specified (IEEE 754 standards).
	 * <p>
	 * The Java {@code double} type has a precision of 52 significand bits (mantissa), which is about 15–17 decimal digits.
	 * For this particular value, it will use 15 digits to represent the mantissa.
	 * <p>
	 * We might see <i><b>PI</b></i> defined with ({@code 3.14159265358979323846}) in some
	 * OpenJDK versions (e.g., JDK 8 or Adoptium builds), but
	 * the extra digits ({@code 23846}) will get truncated and would not affect the actual stored value.
	 * This was removed in later JDKs like JDK 19.
	 *
	 * @see <a href="https://github.com/openjdk/jdk8u-dev/blob/master/jdk/src/share/classes/java/lang/Math.java#L123">OpenJDK jdk8u-dev</a>
	 * @see <a href="https://github.com/adoptium/jdk8u/blob/master/jdk/src/share/classes/java/lang/Math.java">Adoptium jdk8u</a>
	 * @see <a href="https://github.com/openjdk/jdk19u/blob/master/src/java.base/share/classes/java/lang/Math.java#L144">OpenJDK jdk19u</a>
	 */
	public static final double PI = 3.141592653589793;

	public static double abs ( double a) {
	    return (a < 0.0) ? -a : a;
	  }

	  public static float abs ( float a) {
		return (a < 0.0) ? - a : a;
	  }

	  public static int abs ( int a) {
	    return (a < 0) ? -a : a; // that's probably slightly faster
	  }

	  public static long abs ( long a) {
	    return (a < 0) ? -a : a;
	  }

	  public static double max ( double a, double b) {
		if (a != a)
			return a;
		if (a == b)
			return (1.0d / a > 0) ? a : b;
		return (a >= b) ? a : b;
	  }

	  public static float max ( float a, float b) {
		if (a != a)
			return a;
		if (a == b)
			return (1.0f / a > 0) ? a : b;
		return (a >= b) ? a : b;
	  }

	  public static int max ( int a, int b) {
	    return (a >= b) ? a : b;
	  }

	  public static long max ( long a, long b) {
		return (a >= b) ? a : b;
	  }

	  public static double min ( double a, double b) {
		if (a != a)
			return a;
		if (a == b)
			return (1.0d / a < 0) ? a : b;
		return (a <= b) ? a : b;
	  }
	  
	  public static float min ( float a, float b) {
		 if (a != a)
			 return a;
		 if (a == b)
			 return (1.0f / a < 0) ? a : b;
		 return (a <= b) ? a : b;
	  }

	  public static int min ( int a, int b) {
		  return (a <= b) ? a : b;
	  }

	  public static long min ( long a, long b) {
		  return (a <= b) ? a : b;
	  }
	  
	  public static long round ( double d) {
	  if (d > 0) {
	        return (long) (d + 0.5d);
	    } else {
	        return (long) (d - 0.5d);
	    }
	  }
	  
	  public static int round ( float d) {
		  if (d > 0) {
		        return (int) (d + 0.5d);
		    } else {
		        return (int) (d - 0.5d);
		    }
		  }
	  public native static double sqrt ( double a) ;

	  public native static double random ();

	  

	  public native static double exp ( double a) ;

	  public native static double asin ( double a) ;

	  public native static double acos ( double a) ;

	  public native static double atan ( double a);

	  public native static double atan2 ( double a, double b);

//	TODO: fix
	  public static double ceil ( double a) {
		  long result = (long)a;
		  if (result < a) result ++;

		  return result;
	  }

//	TODO: fix
	  public static double floor ( double a) {
		  long result = (long)a;
		  if (result > a) result --;

		  return result;
	  }

	  public native static double log ( double a);

	  // TODO: fix
	  // Warning: this is different IEEE standard
	  public static double rint ( double a) {
		  System.err.println("Warning: Math.rint not modeled according to IEEE standard");

		  if (a >= 0)
			  return (long) (a + 0.5);
		  else
			  return (long) (a - 0.5);
	  }

	  public native static double tan ( double a);

	  public native static double sin ( double a);

	  public native static double cos ( double a);

	  public native static double pow ( double a, double b);

	  public static native double log10(double a);

}
