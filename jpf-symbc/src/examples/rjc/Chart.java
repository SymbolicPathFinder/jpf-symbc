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

public class Chart {
	public int activeSubStates[] = new int[1];
	public double TopLevel_Chart_jets = 0;
	public double TopLevel_Chart_enable = 0;
	public double TopLevel_Chart_ton = 0;
	double TopLevel_Chart_tmin = 0.0140;
	double TopLevel_Chart_delt = 0.1;
	double TopLevel_Chart_count = 0;
	int execute_at_initialization_464 = 0;
	private double TopLevel_Chart_Nofjets = 0;
	private double[] TopLevel_Chart_e = new double[2];
	private double TopLevel_Chart_Firefct1 = 0;
	private double TopLevel_Chart_Coastfct1 = 0;
	private double TopLevel_Chart_Firefct2 = 0;
	private double TopLevel_Chart_Coastfct2 = 0;
	private double TopLevel_Chart_tjcalc1 = 0;
	private double TopLevel_Chart_tjcalc = 0;

	final static int CHART0 = 0x0;
	final static int WAIT_FOR_STABLE_RATE1 = 0x1;
	final static int START2 = 0x2;
	final static int FIRE_REGION_13 = 0x3;
	final static int COAST_REGION_24 = 0x4;
	final static int SKIP_A_SAMPLE_25 = 0x5;
	final static int SKIP_A_SAMPLE_16 = 0x6;
	final static int COAST_REGION_17 = 0x7;
	final static int FIRE_REGION_28 = 0x8;

	public void Chart_100000202_enter(int entryMode, int tpp) {
		if (entryMode > -2 && entryMode <= 0) {
			if (((1) != 0)) {
				TopLevel_Chart_count = 2;
				Wait_for_stable_rate_100000203_enter(0, CHART0);
			}

		}

	}

	public void Chart_100000202_exec() {
		if (activeSubStates[CHART0 & 0xFFFF] == WAIT_FOR_STABLE_RATE1) {
			Wait_for_stable_rate_100000203_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == START2) {
			Start_100000204_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == FIRE_REGION_13) {
			Fire_region_1_100000205_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == COAST_REGION_24) {
			Coast_region_2_100000206_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == SKIP_A_SAMPLE_25) {
			Skip_a_Sample_2_100000207_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == SKIP_A_SAMPLE_16) {
			Skip_a_Sample_1_100000208_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == COAST_REGION_17) {
			Coast_region_1_100000209_exec();
		} else if (activeSubStates[CHART0 & 0xFFFF] == FIRE_REGION_28) {
			Fire_region_2_100000210_exec();
		}

	}

	public void Chart_100000202_exit() {
		if (activeSubStates[CHART0 & 0xFFFF] == WAIT_FOR_STABLE_RATE1) {
			Wait_for_stable_rate_100000203_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == START2) {
			Start_100000204_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == FIRE_REGION_13) {
			Fire_region_1_100000205_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == COAST_REGION_24) {
			Coast_region_2_100000206_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == SKIP_A_SAMPLE_25) {
			Skip_a_Sample_2_100000207_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == SKIP_A_SAMPLE_16) {
			Skip_a_Sample_1_100000208_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == COAST_REGION_17) {
			Coast_region_1_100000209_exit();
		} else if (activeSubStates[CHART0 & 0xFFFF] == FIRE_REGION_28) {
			Fire_region_2_100000210_exit();
		}

	}

	public void Wait_for_stable_rate_100000203_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = WAIT_FOR_STABLE_RATE1;
		}

	}

	public void Wait_for_stable_rate_100000203_exec() {
		if (TopLevel_Chart_count == 0) {
			Wait_for_stable_rate_100000203_exit();
			Start_100000204_enter(0, CHART0);
		} else if (((1) != 0)) {
			Wait_for_stable_rate_100000203_exit();
			--TopLevel_Chart_count;
			Wait_for_stable_rate_100000203_enter(0, WAIT_FOR_STABLE_RATE1);
		}

	}

	public void Wait_for_stable_rate_100000203_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -WAIT_FOR_STABLE_RATE1;
	}

	public void Start_100000204_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = START2;
		}

	}

	public void Start_100000204_exec() {
		if (TopLevel_Chart_e[(int) (1)] < 0 && TopLevel_Chart_Firefct2 < 0
				|| TopLevel_Chart_e[(int) (1)] > 0
				&& TopLevel_Chart_Coastfct2 > 0) {
			Start_100000204_exit();
			Fire_region_2_100000210_enter(0, CHART0);
		} else if (TopLevel_Chart_e[(int) (1)] > 0
				&& TopLevel_Chart_Coastfct2 >= 0 && TopLevel_Chart_Firefct1 < 0) {
			Start_100000204_exit();
			Coast_region_2_100000206_enter(0, CHART0);
		} else if (TopLevel_Chart_e[(int) (1)] > 0
				&& TopLevel_Chart_Firefct1 > 0
				|| TopLevel_Chart_e[(int) (1)] < 0
				&& TopLevel_Chart_Coastfct1 < 0) {
			Start_100000204_exit();
			Fire_region_1_100000205_enter(0, CHART0);
		} else if (TopLevel_Chart_e[(int) (1)] < 0
				&& TopLevel_Chart_Coastfct1 <= 0 && TopLevel_Chart_Firefct2 > 0) {
			Start_100000204_exit();
			Coast_region_1_100000209_enter(0, CHART0);
		}

	}

	public void Start_100000204_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -START2;
	}

	public void Fire_region_1_100000205_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = FIRE_REGION_13;
			TopLevel_Chart_jets = -TopLevel_Chart_Nofjets;
			TopLevel_Chart_ton = TopLevel_Chart_tjcalc + TopLevel_Chart_tjcalc1;
		}

	}

	public void Fire_region_1_100000205_exec() {
		if (TopLevel_Chart_e[(int) (1)] < 0 && TopLevel_Chart_Coastfct1 <= 0) {
			Fire_region_1_100000205_exit();
			Coast_region_1_100000209_enter(0, CHART0);
		}
		else if (TopLevel_Chart_ton < (double) (2) * TopLevel_Chart_delt) {
			TopLevel_Chart_enable = 1;
			if (TopLevel_Chart_ton > TopLevel_Chart_tmin) {
				TopLevel_Chart_count = 2;
				Fire_region_1_100000205_exit();
				Skip_a_Sample_1_100000208_enter(0, CHART0);
			} else if (((1) != 0)) {
				TopLevel_Chart_enable = 0;
				Fire_region_1_100000205_exit();
				Coast_region_1_100000209_enter(0, CHART0);
			}

		}
		else if (((1) != 0)) {
			Fire_region_1_100000205_exit();
			Fire_region_1_100000205_enter(0, FIRE_REGION_13);
		}

	}

	public void Fire_region_1_100000205_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -FIRE_REGION_13;
	}

	public void Coast_region_2_100000206_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = COAST_REGION_24;
			TopLevel_Chart_jets = 0;
			TopLevel_Chart_ton = 0;
			TopLevel_Chart_enable = 0;
		}

	}

	public void Coast_region_2_100000206_exec() {
		if (TopLevel_Chart_e[(int) (1)] > 0 && TopLevel_Chart_Firefct1 > 0) {
			Coast_region_2_100000206_exit();
			Fire_region_1_100000205_enter(0, CHART0);
		}

	}

	public void Coast_region_2_100000206_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -COAST_REGION_24;
	}

	public void Skip_a_Sample_2_100000207_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = SKIP_A_SAMPLE_25;
			--TopLevel_Chart_count;
		}

	}

	public void Skip_a_Sample_2_100000207_exec() {
		if (TopLevel_Chart_count == 0) {
			Skip_a_Sample_2_100000207_exit();
			Coast_region_2_100000206_enter(0, CHART0);
		} else if (((1) != 0)) {
			Skip_a_Sample_2_100000207_exit();
			TopLevel_Chart_ton -= TopLevel_Chart_delt;
			Skip_a_Sample_2_100000207_enter(0, SKIP_A_SAMPLE_25);
		}

	}

	public void Skip_a_Sample_2_100000207_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -SKIP_A_SAMPLE_25;
	}

	public void Skip_a_Sample_1_100000208_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = SKIP_A_SAMPLE_16;
			--TopLevel_Chart_count;
		}

	}

	public void Skip_a_Sample_1_100000208_exec() {
		if (TopLevel_Chart_count == 0) {
			Skip_a_Sample_1_100000208_exit();
			Coast_region_1_100000209_enter(0, CHART0);
		} else if (((1) != 0)) {
			Skip_a_Sample_1_100000208_exit();
			TopLevel_Chart_ton -= TopLevel_Chart_delt;
			Skip_a_Sample_1_100000208_enter(0, SKIP_A_SAMPLE_16);
		}

	}

	public void Skip_a_Sample_1_100000208_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -SKIP_A_SAMPLE_16;
	}

	public void Coast_region_1_100000209_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = COAST_REGION_17;
			TopLevel_Chart_jets = 0;
			TopLevel_Chart_ton = 0;
			TopLevel_Chart_enable = 0;
		}

	}

	public void Coast_region_1_100000209_exec() {
		if (TopLevel_Chart_e[(int) (1)] < 0 && TopLevel_Chart_Firefct2 < 0) {
			Coast_region_1_100000209_exit();
			Fire_region_2_100000210_enter(0, CHART0);
		}

	}

	public void Coast_region_1_100000209_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -COAST_REGION_17;
	}

	public void Fire_region_2_100000210_enter(int entryMode, int tpp) {
		if (entryMode <= 0) {
			activeSubStates[CHART0 & 0xFFFF] = FIRE_REGION_28;
			TopLevel_Chart_jets = TopLevel_Chart_Nofjets;
			TopLevel_Chart_ton = TopLevel_Chart_tjcalc - TopLevel_Chart_tjcalc1;
		}

	}

	public void Fire_region_2_100000210_exec() {
		if (TopLevel_Chart_ton < (double) (2) * TopLevel_Chart_delt) {
			TopLevel_Chart_enable = 1;
			if (TopLevel_Chart_ton > TopLevel_Chart_tmin) {
				TopLevel_Chart_count = 2;
				Fire_region_2_100000210_exit();
				Skip_a_Sample_2_100000207_enter(0, CHART0);
			} else if (((1) != 0)) {
				TopLevel_Chart_enable = 0;
				Fire_region_2_100000210_exit();
				Coast_region_2_100000206_enter(0, CHART0);
			}

		}

		else if (TopLevel_Chart_e[(int) (1)] > 0 && TopLevel_Chart_Coastfct2 > 0) {
				Fire_region_2_100000210_exit();
				Coast_region_2_100000206_enter(0, CHART0);
			}
		else if (((1) != 0)) {
			Fire_region_2_100000210_exit();
			Fire_region_2_100000210_enter(0, FIRE_REGION_28);
		}

	}

	public void Fire_region_2_100000210_exit() {
		activeSubStates[CHART0 & 0xFFFF] = -FIRE_REGION_28;
	}

	public void Main(double Nofjets_, double[] e_, double Firefct1_,
			double Coastfct1_, double Firefct2_, double Coastfct2_,
			double tjcalc1_, double tjcalc_, double[] jets_, double[] enable_,
			double[] ton_) {
		{
			TopLevel_Chart_Nofjets = Nofjets_;
		}
		{
			int ix4;
			for (ix4 = 0; ix4 < 2; ++ix4) {
				TopLevel_Chart_e[ix4] = e_[ix4];
			}
		}
		{
			TopLevel_Chart_Firefct1 = Firefct1_;
		}
		{
			TopLevel_Chart_Coastfct1 = Coastfct1_;
		}
		{
			TopLevel_Chart_Firefct2 = Firefct2_;
		}
		{
			TopLevel_Chart_Coastfct2 = Coastfct2_;
		}
		{
			TopLevel_Chart_tjcalc1 = tjcalc1_;
		}
		{
			TopLevel_Chart_tjcalc = tjcalc_;
		}
		if (execute_at_initialization_464 == 1) {
			Chart_100000202_exec();
		}

		execute_at_initialization_464 = 1;
		{
			jets_[0] = TopLevel_Chart_jets;
		}
		{
			enable_[0] = TopLevel_Chart_enable;
		}
		{
			ton_[0] = TopLevel_Chart_ton;
		}
	}

	public void Init() {
		int i = 0;
		int ix503 = 0;

		i = 0;
		while (i < 1) {
			activeSubStates[(int) (i)] = 0;
			++i;
		}

		TopLevel_Chart_jets = 0;
		TopLevel_Chart_Nofjets = 0;
		ix503 = 0;
		while (ix503 < 2) {
			TopLevel_Chart_e[(int) (ix503)] = 0;
			++ix503;
		}

		TopLevel_Chart_enable = 0;
		TopLevel_Chart_ton = 0;
		TopLevel_Chart_Firefct1 = 0;
		TopLevel_Chart_Coastfct1 = 0;
		TopLevel_Chart_Firefct2 = 0;
		TopLevel_Chart_Coastfct2 = 0;
		TopLevel_Chart_tjcalc1 = 0;
		TopLevel_Chart_tjcalc = 0;
		TopLevel_Chart_tmin = 0.0140;
		TopLevel_Chart_delt = 0.1;
		TopLevel_Chart_count = 0;
		execute_at_initialization_464 = (int) (0);
		Chart_100000202_enter(-1, 0);
	}
}
