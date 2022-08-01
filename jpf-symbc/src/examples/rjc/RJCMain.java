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

package rjc;

import java.io.*;
import java.util.ArrayList;

public class RJCMain {
	protected rjc controller;
	protected String filename1, filename2; // 2 CSV files for this example

	public RJCMain() {
		this.controller = new rjc();
		this.controller.Init2();
	}

	public RJCMain(String filename1, String filename2) {
		this();
		this.filename1 = filename1;
		this.filename2 = filename2;
	}

	public void DoSim() {

		ArrayList<ArrayList<String>> cmdInputs = new ArrayList<ArrayList<String>>();
		ArrayList<ArrayList<String>> measInputs = new ArrayList<ArrayList<String>>();
		ArrayList<ArrayList<Double>> cmdVars = new ArrayList<ArrayList<Double>>();
		ArrayList<ArrayList<Double>> measVars = new ArrayList<ArrayList<Double>>();

		try {
			File file1 = new File(this.filename1);
			File file2 = new File(this.filename2);

			FileInputStream fis1 = new FileInputStream(file1);
			FileInputStream fis2 = new FileInputStream(file2);

			BufferedReader br1 = new BufferedReader(new InputStreamReader(fis1));
			BufferedReader br2 = new BufferedReader(new InputStreamReader(fis2));
			String strLine;

			// Read File Line By Line
			while ((strLine = br1.readLine()) != null) {
				if (!strLine.isEmpty()) {
					String[] inputs = strLine.split(",");
					ArrayList<String> line = new ArrayList<String>();
					ArrayList<Double> dubLine = new ArrayList<Double>();
					for (int ix = 0; ix < inputs.length; ix++) {
						line.add(inputs[ix]);
						dubLine.add(Double.parseDouble(inputs[ix]));
					}
					cmdInputs.add(line);
					cmdVars.add(dubLine);
				}
			}

			while ((strLine = br2.readLine()) != null) {
				if (!strLine.isEmpty()) {
					String[] inputs = strLine.split(",");
					ArrayList<String> line = new ArrayList<String>();
					ArrayList<Double> dubLine = new ArrayList<Double>();
					for (int ix = 0; ix < inputs.length; ix++) {
						line.add(inputs[ix]);
						dubLine.add(Double.parseDouble(inputs[ix]));
					}
					measInputs.add(line);
					measVars.add(dubLine);
				}
			}

			fis1.close();
			fis2.close();

			BufferedWriter out = new BufferedWriter(new FileWriter("JavaOutput.csv")); // Write the second output to a file

			for (int i = 0; i < cmdInputs.size() && i < measInputs.size(); i++) {
				ArrayList<Double> currCmd = cmdVars.get(i);
				ArrayList<Double> currMeas = measVars.get(i);
				// For now assume they are the correct size
				double[] output1 = new double[1];
				double[] output2 = new double[2];
				double[] input1 = new double[3];
				double[] input2 = new double[3];
				for (int j = 0; j < 3; j++) {
					input1[j] = currCmd.get(j + 1); // Throw away the time stamp
					input2[j] = currMeas.get(j + 1); // Throw away the time stamp
				}
				this.controller.Main0(input1, input2, output1, output2);

				System.out.println("Output 1 (yaw jets)   : " + output1[0]);
				System.out.println("Output 2 (pitch jets) : " + output2[0] + ", " + output2[1]);
				out.write("" + currCmd.get(0) + "," + output2[0] + "," + output2[1] + "\n");
			}

			out.close();

		}
		catch (Exception e) {
			System.out.println(e.getMessage());
		}
	}

	// Symbolic pathfinder cannot handle arrays, so use this method if you want to run the process symbolically
	public void DoSimSymbolic() {
		double[] out1 = new double[1];
		double[] out2 = new double[2];

		for (int i = 0; i < 2; i++) {
			out1 = new double[1];
			out2 = new double[2];
			this.controller.MainSymbolic(0, 0, 0, 0, 0, 0, out1, out2);
		}
	}

	public static void main(String[] args) {
		RJCMain rjcmain;
		if (args.length < 2) { // Run symbolically if no args
			rjcmain = new RJCMain();
			rjcmain.DoSimSymbolic();
		}
		else {
			rjcmain = new RJCMain(args[0], args[1]);
			rjcmain.DoSim();
		}
	}
}
