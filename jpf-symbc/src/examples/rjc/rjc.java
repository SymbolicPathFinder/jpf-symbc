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

public class rjc {
	private Reaction_Jet_Control0 Reaction_Jet_Control_100000006_class_member0 = new Reaction_Jet_Control0();

	public void Main0(double[] In1_2, double[] In2_3, double[] Out1_4, double[] Out2_5) {
		Reaction_Jet_Control_100000006_class_member0.Main1(In1_2, In2_3, Out1_4, Out2_5);
	}

	public void Init2() {
		Reaction_Jet_Control_100000006_class_member0.Init3();
	}

	// Added by hand so that symbolic pathfinder can be used
	public void MainSymbolic(double in1_0, double in1_1, double in1_2, double in2_0, double in2_1, double in2_2, double[] out1, double[] out2) {
		double[] in1 = new double[3];
		double[] in2 = new double[3];

		in1[0] = in1_0;
		in1[1] = in1_1;
		in1[2] = in1_2;

		in2[0] = in2_0;
		in2[1] = in2_1;
		in2[2] = in2_2;

		this.Reaction_Jet_Control_100000006_class_member0.Main1(in1, in2, out1, out2);
	}
}
