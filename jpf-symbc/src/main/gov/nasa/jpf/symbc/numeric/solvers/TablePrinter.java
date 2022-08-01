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
package gov.nasa.jpf.symbc.numeric.solvers;

import java.io.File;
import java.io.IOException;


public class TablePrinter {
	
	public static String TABLE_DIR = "/tmp/compare/";
	public static final String ERR_MSG = 
		"Please, make sure you created directory " +
		TABLE_DIR + " to hold .ser files";

	public static void main(String[] args) {
		
		try {
			
			SolvingDiff general = new SolvingDiff();
			File folder = new File(TABLE_DIR);
			File[] listOfFiles = folder.listFiles();
			
			for(int i = 0; i < listOfFiles.length; i++){
				File file = listOfFiles[i];
				System.out.println(file.toString());
				SolvingDiff obj = SolvingDiff.readFromFile(file);
				obj.print();
				general.concatResult(obj);
			}
			
			System.out.println("merging results of all .ser files");
			System.out.println("==================================");
			general.print();
			System.out.println("in latex format");
			System.out.println("==================================");
			general.printLatex();
			
		} catch (IOException e) {
			System.err.println(ERR_MSG);
			e.printStackTrace();
			System.exit(-1);
		} catch (ClassNotFoundException e) {
			String msg = "Looks like you changed structure or name of the class " +
			"contained in the serialiable files after generating the file.";
			System.err.println(msg);
			e.printStackTrace();
			System.exit(-1);
		}
		
	}

}