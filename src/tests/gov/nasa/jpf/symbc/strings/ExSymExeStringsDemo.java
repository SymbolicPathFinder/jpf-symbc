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


public class ExSymExeStringsDemo {
	static int field;

  public static void main (String[] args) {
	  String a="aaa";
	  String b = "bbb";
	  String c = "ccc";
	  String d = "ddd"; 
	  //test01 (a,b, 1);
	  //test02(a,b,1);
	  //test02a(a, b, 1);
	  //test03(a,b,1);
	  //test04(a,b,1);
	  //test05(a,b,1);
	  //test06(a,b,1);
	  //test07(a,b,1);
	  test08("c  ","c",0);
	  //test08a(a,b,1);
	  //test09(a,b,1);
	  //test10(a,b,1);
	  //Debug.printPC("This is the PC at the end:");
	  //a=a.concat(b);
	  
  }
  
  public static void test01 (String a, String b, int x) {
	  if (a.startsWith("ba")) {
		  if (a.endsWith("ba")) {
			  System.out.println("boo");
		  }
	  }
  }
  
  public static void test02 (String a, String b, int x) {
	  String c = a.concat("ab");
	  if (c.startsWith("c")) {
		  int i = c.indexOf("d");
		  if (i == 2) {
			  System.out.println("aaa");
		  }
		  else if (i == -1){
			 System.out.println("ah!");
		  }
	  }
  }
  
  public static void test02a (String a, String b, int x) {
	  //cvc_inc has difficulty with this one
	  String c = a.concat("ab");
	  if (c.startsWith("c")) {
		  if (c.contains("d")) {
			  int i = c.indexOf("d");
			  if (i == 2) {
				  System.out.println("aaa");
			  }
			  else if (i == -1){
				 throw new RuntimeException("ah!");
			  }
		  }
	  }
  }
  
  public static void test03 (String a, String b, int x) {
	  if (a.startsWith("hello")) {
		  throw new RuntimeException("aaah!");
	  }
  }
  
  public static void test04 (String a, String b, int x) {
	  if (b.startsWith("c")) { 
		  for (int i = 0; i < 3; i++) {
			  if (a.charAt(i) == 'h') {
				  System.out.println("boo");
			  }
			  else if (a.charAt(i) == 'c') {
				  System.out.println("aaa");
			  }
			  if (b.startsWith("d")) {
				  throw new RuntimeException("aaah!");
			  }
		  }
	  }
  }
  
  public static void test05 (String a, String b, int x) {
	  if (b.startsWith("c")) { 
		  for (int i = 0; i < 3; i++) {
			  if (a.charAt(i) == 'h') {
				  System.out.println("boo");
			  }
			  else if (a.charAt(i) == 'c') {
				  System.out.println("aaa");
			  }
			  if (a.equals("chc")) {
				  throw new RuntimeException("aaah!");
			  }
		  }
	  }
  }
  
  public static void test06 (String a, String b, int x) {
	  if (b.startsWith("c")) { 
		  for (int i = 0; i < 3; i++) {
			  if (a.charAt(i) == 'h') {
				  System.out.println("boo");
			  }
			  else if (a.charAt(i) == 'c') {
				  System.out.println("aaa");
			  }
			  if (a.equals("d")) {
				  throw new RuntimeException("aaah!");
			  }
		  }
	  }
  }
  
  public static void test07 (String a, String b, int x) {
	  //this seems to give some good variance in performance
	  if (b.startsWith("c") && a.length() < 4) { 
		  for (int i = 0; i < a.length(); i++) {
			  if (a.charAt(i) == 'h') {
				  System.out.println("boo");
			  }
			  else if (a.charAt(i) == 'c') {
				  System.out.println("aaa");
			  }
			  if (a.equals("chc")) {
				  throw new RuntimeException("aaah!");
			  }
		  }
	  }
  }
  
  public static void test08 (String a, String b, int i) { 
	  if (b.startsWith("c") && a.length() > 2 
			  && a.length() < 5 && b.length() < 2) {
		  if (i >= 0) {
			  for (; i < a.length(); i++) {
				  //System.out.println(i);
				  int old = i;
				  /* some code */
				  if (a.charAt(i) == 'c' && a.charAt(i+1) == 'd') {
					  i = a.indexOf("/cd");
				  }
				  /* some code */
				  if (i <= old) {
					  throw new RuntimeException("Does not work");
				  }
			  }
		  }
	  }
  }
  
  public static void test08a (String a, String b, int x) {
	  if (a.equals(b)) {
		  for (int i = 0; i < a.length(); i++) {
			  int old = i;
			  /* some code */
			  if (	a.charAt(i) == '<' && 
					a.charAt(i+1) == 'c' &&
					a.charAt(i + 2) == 'd' &&
					a.charAt(i + 3) == '>') {
				  
				  i = a.indexOf("</cd>");
			  }
			  /* some code */
			  if (i <= old) {
				  throw new RuntimeException("Does not work");
			  }
		  }
	  }
  }
  
  public static void test09 (String a, String b, int x) {
	  //this causes automata's equality to crawl, needs to be investigated
	  if (b.startsWith(" ") && a.startsWith(b) && a.endsWith("c")) {
		  if (b.trim().equals("ab"));
	  }
  }
  
  public static void test10 (String a, String b, int x) {
	  String c = a.concat(b);
	  if (c.substring(2).equals("hello")) {
		  if (c.substring(0,2).equals(a)) {
			  System.out.println("aaa");
		  }
	  }
  }

}

