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
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Arrays;

public class SolvingDiff implements Serializable {

	private static final long serialVersionUID = 1L;
	private int[][] matrix; 

	public void init(int size) {
		if (matrix == null) {
			matrix = new int[size][size];
		}
	}

	public void update(final boolean[] solutions) {
		for (int i=0; i < solutions.length; i++) {
			for (int j=0; j < solutions.length; j++) {
				if (i == j) continue;
				if (solutions[i] && !solutions[j]) {
					matrix[i][j] += 1;
				}
			}
		}
	}

	public void print() {
		StringBuffer sb = new StringBuffer();
		if (matrix == null) {
			sb.append("Solver difference matrix is null.  Set symbolic.dp=debug");
		} else {
			for (int i=0; i < matrix.length; i++) {
				sb.append(i+": ");
				sb.append(Arrays.toString(matrix[i]));
				sb.append("\n");
			}
		}
		System.out.println(sb);
	}

	public void printLatex() {
		StringBuffer sb = new StringBuffer();
		if (matrix == null) {
			sb.append("Solver difference matrix is null.  Set symbolic.dp=debug");
		} else {
			sb.append(" -");
			for (int i=0; i < matrix.length; i++) {
				sb.append(" & ");
				sb.append("s");
				sb.append(i);
			}
			sb.append(" \\\\ \\hline");
			sb.append("\n");
			for (int i=0; i < matrix.length; i++) {
				sb.append("s");
				sb.append(i);
				for (int j = 0 ; j < matrix.length; j++) {
					sb.append(" & ");
					sb.append(matrix[i][j]);
				}
				sb.append(" \\\\ \\hline");
				sb.append("\n");
			}
		}
		System.out.println(sb);
	}

	public void concatResult(SolvingDiff solvingDiff){
		int [][] matrixOther = solvingDiff.getMatrix();

		if(matrix != null){
			for(int i = 0; i < matrix.length; i++){
				for(int j = 0; j < matrix.length; j++){
					matrix[i][j] += matrixOther[i][j]; 
				}
			}
		}
		else
			matrix = matrixOther;
	}

	public int[][] getMatrix() {
		return matrix;
	}

	public static void writeToFile(String fileName, SolvingDiff obj) throws IOException {
		ObjectOutputStream oos = new ObjectOutputStream(new FileOutputStream(fileName));
		oos.writeObject(obj);
	}

	public static SolvingDiff readFromFile(File file) throws IOException, ClassNotFoundException {
		ObjectInputStream ois = new ObjectInputStream(new FileInputStream(file));
		return (SolvingDiff) ois.readObject();
	}

}
