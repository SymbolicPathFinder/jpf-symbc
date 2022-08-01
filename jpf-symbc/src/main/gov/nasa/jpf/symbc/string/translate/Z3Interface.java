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

package gov.nasa.jpf.symbc.string.translate;



import gov.nasa.jpf.util.LogManager;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.Logger;


public class Z3Interface {
  static Logger logger = LogManager.getLogger("Z3Interface");

	Process process;
	OutputStream stdin;
	InputStream stdout;
	BufferedReader brCleanUp;
	boolean sat;
	
	public static String Z3Version;
	
	public static final String Z3_2_19 = "2.19";
	public static final String Z3_2_18 = "2.18";
	
	Map<String, String> answers;
	
	public Z3Interface () throws IOException{
		if (Z3Version == null) {
			Z3Version = decideZ3Version();
		}
		process = Runtime.getRuntime().exec("./lib/z3 -smt2 -in -m");
		stdin = process.getOutputStream();
		stdout = process.getInputStream();
		brCleanUp = new BufferedReader (new InputStreamReader (stdout));
	}
	
	public String decideZ3Version() throws IOException {
		process = Runtime.getRuntime().exec("./lib/z3 -version");
		stdout = process.getInputStream();
		brCleanUp = new BufferedReader (new InputStreamReader (stdout));
		String line = brCleanUp.readLine();
		String result = "";
		if (line.contains ("Z3 version 2.19")) {
			result = Z3_2_19;
		}
		else if (line.contains ("Z3 version 2.18")) {
			result = Z3_2_18;
		} else {
			throw new RuntimeException("Unknown Z3 version: '" + line + "'");
		}
		process.destroy();
		stdout.close();
		brCleanUp.close();
		return result;
	}
	
	public void sendMessage (String msg) throws IOException {
		//println ("Entered sendMessage");
		if (Z3Version.equals (Z3_2_18)) {
			sendMessage218 (msg);
		} else if (Z3Version.equals (Z3_2_19)) {
			sendMessage219(msg);
		}
		//println ("Exited sendMessage");
	}
	
	public void sendMessage218 (String msg) throws IOException{
		sat = false;
		stdin.write((msg + "\n(exit)").getBytes());
		stdin.flush();
		answers = new HashMap<String, String>();
		String line = brCleanUp.readLine();
		//System.out.println("[Stdout] " + line);
		while (line != null) {
			if (line.equals ("sat")) {
				sat = true;
			}
			if (line.contains("ERROR")) {
				String oldline = line;
				line = brCleanUp.readLine();
				logger.warning(msg);
				throw new RuntimeException("Z3 encountered an error in its input: " + oldline + "\n" + line);
			}
			else if (line.startsWith("((\"model\" \"") && sat) {
				if (line.endsWith("\"))")) break;
				line = brCleanUp.readLine();
				process (line);
				while (!line.endsWith("\"))")) {
					line = brCleanUp.readLine();
					process (line);
				}
				
				break;
			}
			line = brCleanUp.readLine();
			//System.out.println("[Stdout] " + line);
		}
	}
	
	public void sendMessage219 (String msg) throws IOException{
		sat = false;
		stdin.write((msg + "\n(exit)").getBytes());
		//System.out.println(msg + "\n(exit)");
		stdin.flush();
		stdin.close();
		answers = new HashMap<String, String>();
		String line = brCleanUp.readLine();
		//System.out.println("[Stdout] " + line);
		while (line != null) {
			if (line.equals ("sat")) {
				sat = true;
			}
			if (line.contains("ERROR")) {
				String oldline = line;
				line = brCleanUp.readLine();
				logger.warning(msg);
				throw new RuntimeException("Z3 encountered an error in its input: " + oldline + "\n" + line);
			}
			else if (line.startsWith("((\"model\" \"") && sat) {
				if (line.endsWith("\"))")) break;
				line = brCleanUp.readLine();
				process (line);
				while (!line.endsWith("\"))")) {
					line = brCleanUp.readLine();
					process (line);
				}
				
				break;
			}
			line = brCleanUp.readLine();
			//System.out.println("[Stdout] " + line);
		}
	}
	
	public void sendIncMessage (String msg) throws IOException{
		//println ("Entered sendIncMessage");
		if (Z3Version.equals (Z3_2_18)) {
			sendIncMessage218(msg);
		} else if (Z3Version.equals (Z3_2_19)) {
			sendIncMessage219(msg);
		}
		//println ("Exiting...");
	}
	

	public void sendIncMessage218 (String msg) throws IOException{
		sat = false;
		stdin.write((msg + "\n(check-sat)\n(get-info model)").getBytes());
		stdin.flush();
		answers = new HashMap<String, String>();
		String line = brCleanUp.readLine();
		//System.out.println("[Stdout] " + line);
		
		
		while (line != null) {
			
			if (line.equals ("sat")) {
				sat = true;
			}
			else if (line.equals("unsat")) {
				sat = false;
				break;
			}
			if (line.contains("ERROR") || line.contains("error")) {
				String oldline = line;
				line = brCleanUp.readLine();
				logger.severe(msg);
				throw new RuntimeException("Z3 encuntered an error in its input: " + oldline + "\n" + line);
			}
			else if (line.startsWith("((\"model\" \"") && sat) {
				if (line.endsWith("\"))")) break;
				line = brCleanUp.readLine();
				process (line);
				while (!line.endsWith("\"))")) {
					line = brCleanUp.readLine();
					process (line);
				}
				
				break;
			}
			line = brCleanUp.readLine();
			//System.out.println("[Stdout] " + line);
		}
		
	}
	
	public void sendIncMessage219 (String msg) throws IOException{
		sat = false;
		stdin.write((msg + "\n(check-sat)\n(get-info model)").getBytes());
		stdin.flush();
		answers = new HashMap<String, String>();
		String line = brCleanUp.readLine();
		//System.out.println("[Stdout] " + line);
		
		
		while (line != null) {
			
			if (line.equals ("sat")) {
				sat = true;
			}
			else if (line.equals("unsat")) {
				sat = false;
				break;
			}
			if (line.contains("ERROR") || line.contains("error")) {
				String oldline = line;
				line = brCleanUp.readLine();
				logger.severe(msg);
				throw new RuntimeException("Z3 encountered an error in its input: " + oldline + "\n" + line);
			}
			else if (line.startsWith("((\"model\" \"") && sat) {
				if (line.endsWith("\"))")) break;
				line = brCleanUp.readLine();
				process (line);
				while (!line.endsWith("\"))")) {
					line = brCleanUp.readLine();
					process (line);
				}
				
				break;
			}
			line = brCleanUp.readLine();
			//System.out.println("[Stdout] " + line);
		}
		
	}
	
	public Map<String, String> getAns () {
		if (sat == true)
			return answers;
		else
			return null;
	}
	
	private void process (String line) {
		String words[] = line.split(" ");
		String varName = words[1];
		StringBuilder sb = new StringBuilder();
		for (int i = 2; i < words[2].length(); i++) {
			char c = words[2].charAt(i);
			if (Character.isDigit(c)) {
				sb.append (c);
			}
			else {
				break;
			}
		}
		BigInteger bi = new BigInteger(sb.toString());
		sb = new StringBuilder();
		for (int i = 1; i < 8 - bi.bitLength() % 8; i++) {
			sb.append ("0");
		}
		for (int i = bi.bitLength(); i >= 0; i--) {
			if (bi.testBit(i))
				sb.append("1");
			else
				sb.append("0");
		}
		answers.put(varName, sb.toString());
	}
	
	public boolean isSAT () {
		return sat;
	}
	
	public void close () {
		try {
			this.sendMessage("");
			stdin.close();
			stdout.close();
			process.destroy();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void main (String [] args) throws IOException{
		Z3Interface z3 = new Z3Interface();
		
		z3.sendIncMessage("(declare-fun a () (_ BitVec 160))\n(declare-fun b () (_ BitVec 160))\n(assert (= ((_ extract 7 0) a) (_ bv255 8)))\n");
		System.out.println("1: " + z3.isSAT());
		
		z3.sendIncMessage("(assert (= ((_ extract 15 8) a) (_ bv255 8)))\n");
		System.out.println("2: " + z3.isSAT());
		
		z3.sendIncMessage("(assert (= ((_ extract 15 8) a) (_ bv254 8)))\n");
		System.out.println("3: " + z3.isSAT());
		
		z3.close();
	}
}
