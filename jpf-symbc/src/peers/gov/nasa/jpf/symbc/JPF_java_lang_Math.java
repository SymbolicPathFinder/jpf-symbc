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

package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;

/**
 * MJI NativePeer class for java.lang.Math library abstraction
 */

// simple functions abs, min, max
public class JPF_java_lang_Math extends NativePeer{

  // <2do> those are here to hide their implementation from traces, not to
  // increase performance. If we want to do that, we should probably inline
  // their real implementation here, instead of delegating (just a compromise)

  // TODO  abs, min, max should be solved symbolically here

//  public static double abs__D__D (MJIEnv env, int clsObjRef, double a) {
//    // return Math.abs(a);
//    System.err.println("Warning: Math.abs not modeled yet");
//    return (a <= .0) ? -a : a;
//  }

//  public static float abs__F__F (MJIEnv env, int clsObjRef, float a) {
//	System.err.println("Warning: Math.abs not modeled yet");
//    return Math.abs(a);
//  }
//
//  public static int abs__I__I (MJIEnv env, int clsObjRef, int a) {
//    //return Math.abs(a);
//	System.err.println("Warning: Math.abs not modeled yet");
//    return (a < 0) ? -a : a; // that's probably slightly faster
//  }
//
//  public static long abs__J__J (MJIEnv env, int clsObjRef, long a) {
//    //return Math.abs(a);
//	System.err.println("Warning: Math.abs not modeled yet");
//    return (a < 0) ? -a : a;
//  }
//
//  public static double max__DD__D (MJIEnv env, int clsObjRef, double a, double b) {
//    // that one has to handle inexact numbers, so it's probably not worth the hassle
//    // to inline it
//	System.err.println("Warning: Math.max not modeled yet");
//    return Math.max(a, b);
//  }
//
//  public static float max__FF__F (MJIEnv env, int clsObjRef, float a, float b) {
//	System.err.println("Warning: Math.max not modeled yet");
//	return Math.max(a, b);
//  }
//
//  public static int max__II__I (MJIEnv env, int clsObjRef, int a, int b) {
//    //return Math.max(a, b);
//	System.err.println("Warning: Math.max not modeled yet");
//    return (a >= b) ? a : b;
//  }
//
//  public static long max__JJ__J (MJIEnv env, int clsObjRef, long a, long b) {
//    //return Math.max(a, b);
//	System.err.println("Warning: Math.max not modeled yet");
//	return (a >= b) ? a : b;
//  }
//
//  public static double min__DD__D (MJIEnv env, int clsObjRef, double a, double b) {
//	System.err.println("Warning: Math.min not modeled yet");
//	return Math.min(a, b);
//  }
//
//  public static float min__FF__F (MJIEnv env, int clsObjRef, float a, float b) {
//	System.err.println("Warning: Math.min not modeled yet");
//	return Math.min(a, b);
//  }
//
//  public static int min__II__I (MJIEnv env, int clsObjRef, int a, int b) {
//	  System.err.println("Warning: Math.min not modeled yet");
//	  return Math.min(a, b);
//  }
//
//  public static long min__JJ__J (MJIEnv env, int clsObjRef, long a, long b) {
//	  System.err.println("Warning: Math.min not modeled yet");
//	  return Math.min(a, b);
//  }
  @MJI
  public static double sqrt__D__D (MJIEnv env, int clsObjRef, double a) {
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.sqrt(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.sqrt(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.SQRT,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double random____D (MJIEnv env, int clsObjRef) {
    return Math.random();
  }

  
  @MJI
  public static double exp__D__D (MJIEnv env, int clsObjRef, double a) {
      Object [] attrs = env.getArgAttributes();
      if (attrs==null) // concrete? I think
    	  return Math.exp(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.exp(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.EXP,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double asin__D__D (MJIEnv env, int clsObjRef, double a) {
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.asin(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.asin(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.ASIN,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double acos__D__D (MJIEnv env, int clsObjRef, double a) {
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.acos(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.acos(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.ACOS,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }

  }
  @MJI
  public static double atan__D__D (MJIEnv env, int clsObjRef, double a) {
      Object [] attrs = env.getArgAttributes();
      if (attrs==null) // concrete? I think
    	  return Math.atan(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.atan(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.ATAN,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double atan2__DD__D (MJIEnv env, int clsObjRef, double a, double b) {
      Object [] attrs = env.getArgAttributes();
      if (attrs==null) // concrete? I think
    	  return Math.atan2(a,b);
	  RealExpression sym_arg1 = (RealExpression)attrs[0];
	  RealExpression sym_arg2 = (RealExpression)attrs[1];
	  RealExpression result;

	  if (sym_arg1 == null && sym_arg2 == null) // concrete
		  return Math.atan2(a,b);
	  else if (sym_arg1 == null)
		  result = new MathRealExpression(MathFunction.ATAN2, a, sym_arg2);
	  else if (sym_arg2 == null)
		  result = new MathRealExpression(MathFunction.ATAN2, sym_arg1, b);
	  else // both symbolic
		  result = new MathRealExpression(MathFunction.ATAN2, sym_arg1, sym_arg2);

	  env.setReturnAttribute(result);
	  // System.out.println("result "+result);
	  return 0; // don't care about concrete value


  }

//TODO: fix
//  public static double ceil__D__D (MJIEnv env, int clsObjRef, double a) {
//	  System.err.println("Warning: Math.ceil not modeled yet");
//	  return Math.ceil(a);
//  }
//
////TODO: fix
//  public static double floor__D__D (MJIEnv env, int clsObjRef, double a) {
//	  System.err.println("Warning: Math.floor not modeled yet");
//      return Math.floor(a);
//  }
  @MJI
  public static double log__D__D (MJIEnv env, int clsObjRef, double a) {
      Object [] attrs = env.getArgAttributes();
      if (attrs==null) // concrete? I think
    	  return Math.log(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.log(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.LOG,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double log10__D__D (MJIEnv env, int clsObjRef, double a) {
	      Object [] attrs = env.getArgAttributes();
	      if (attrs==null) // concrete? I think
	    	return Math.log10(a);
		  RealExpression sym_arg = (RealExpression) attrs[0];
		  if (sym_arg == null) { // concrete
			  return Math.log10(a);
		  }
		  else {
			  throw new RuntimeException("## Error: symbolic log10 not implemented ");
		  }
	  }




  // TODO: fix
//  public static double rint__D__D (MJIEnv env, int clsObjRef, double a) {
//	  System.err.println("Warning: Math.rint not modeled yet");
//	  return Math.rint(a);
//  }
  @MJI
  public static double tan__D__D (MJIEnv env, int clsObjRef, double a) {
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.tan(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.tan(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.TAN,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double sin__D__D (MJIEnv env, int clsObjRef, double a) {
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.sin(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) { // concrete
		  return Math.sin(a);
	  }
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.SIN,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }

  }
  @MJI
  public static double cos__D__D (MJIEnv env, int clsObjRef, double a) {
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.cos(a);
	  RealExpression sym_arg = (RealExpression) attrs[0];
	  if (sym_arg == null) // concrete
		  return Math.cos(a);
	  else {
		  RealExpression result = new MathRealExpression(MathFunction.COS,sym_arg);
		  env.setReturnAttribute(result);
		  // System.out.println("result "+result);
		  return 0;
	  }
  }
  @MJI
  public static double pow__DD__D (MJIEnv env, int clsObjRef, double a, double b) {
//	  System.out.println("here!!!!!");
	  Object [] attrs = env.getArgAttributes();
	  if (attrs==null) // concrete? I think
		  return Math.pow(a,b);
	  RealExpression sym_arg1 = (RealExpression)attrs[0];
	  RealExpression sym_arg2 = (RealExpression)attrs[1];
	  RealExpression result;

	  if (sym_arg1 == null && sym_arg2 == null) // concrete
		  return Math.pow(a,b);
	  else if (sym_arg1 == null)
		  result = new MathRealExpression(MathFunction.POW, a, sym_arg2);
	  else if (sym_arg2 == null)
		  result = new MathRealExpression(MathFunction.POW, sym_arg1, b);
	  else // both symbolic
		  result = new MathRealExpression(MathFunction.POW, sym_arg1, sym_arg2);

	  env.setReturnAttribute(result);
	  // System.out.println("result "+result);
	  return 0; // don't care about concrete value
  }

}
