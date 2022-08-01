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

package strings;

//This example featured in the paper: "Modeling Imperative String Operations with Transducers"
public class WU_FTPD {
	public static void main (String [] args) {
		site_exec("!!!!!!!!!!!!!!!!!!!!!!!!!!!!%n");
	}

	//Some precission and speedup is still needed here
	public static void site_exec(String cmd) {
		String PATH = "/home/ftp/bin";
		int sp = cmd.indexOf(' ');
		int j;
		String result;
		if (sp == -1) {
			j = cmd.lastIndexOf('/');
			result = cmd.substring(j);
		}
		else {
			j = cmd.lastIndexOf('/', sp);
			result = cmd.substring(j);
		}
		//Take everything to lowercase
		if (result.length()  + PATH.length()> 32) { //Prevent buffer overflow
			System.out.println ("Will cause bufferoverflow");
			return;
		}
		String buf = PATH + result; 
		if (buf.contains ("%n")){
			throw new RuntimeException ("String may contain threat");
		}
		//System.out.println (buf);

	}
	
	//Some precission and speedup is still needed here
	public static void site_execLL(String cmd) {
		String PATH = "/home/ftp/bin";
		int sp = cmd.indexOf(' ');
		int j;
		String result;
		int slash = 0;
		if (sp == -1) {
			while (cmd.indexOf('/', slash) != -1) {
				slash++;
			}
		}
		else {
			int temp = cmd.indexOf('/', slash);
			while (temp < sp) {
				slash = temp + 1;
				temp = cmd.indexOf('/', slash);
			}
		}
		System.out.println("Slash: " + slash);
		result = cmd.substring(slash);
		//Take everything to lowercase
		
		if (result.length()  + PATH.length()> 32) { //Prevent buffer overflow
			System.out.println ("Will cause bufferoverflow");
			return;
		}
		String buf = PATH.concat (result);
		if (buf.contains ("%n")){
			throw new RuntimeException ("String may contain threat");
		}
		System.out.println (buf);

	}
}
