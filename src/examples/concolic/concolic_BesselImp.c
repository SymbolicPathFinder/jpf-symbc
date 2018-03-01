/* The BesselImp.c file, which implements the native function */

#include <jni.h>      /* Java Native Interface headers */
#include "concolic_Bessel.h"   /* Auto-generated header created by javah -jni */

#include <math.h>     /* Include math.h for the prototype of function y0 */

/* Our C definition of the function bessely0 declared in Bessel.java */
JNIEXPORT jdouble JNICALL
Java_concolic_Bessel_bessely0(JNIEnv *env, jobject obj, jdouble x)
{
  double y;

  /* Call the Y0(x) Bessel function from the
     standard C mathematical library */
  y = y0(x);

  return y;
}
