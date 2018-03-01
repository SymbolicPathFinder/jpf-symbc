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

package gov.nasa.jpf.symbc;

public class DaisyChainControllerNew {
	public static final int MAX_POSITION = 15;//10;
	public static final int MIN_POSITION = 0;
	public static final int STRENGTH1 = 1;
	public static final int STRENGTH5 = 10;

	private static int flapPosition = MIN_POSITION;
	private static int windEffect;
	private static int goalPosition = MIN_POSITION;

	public static void main(String[] args) throws InterruptedException {
		DaisyChainControllerNew daisyChainController = new DaisyChainControllerNew();

		int windStrength = 0;
		int goalPosition = 17;

		daisyChainController.setWindStrength(windStrength);
		daisyChainController.moveFlaps(goalPosition);

		//System.out.println("Current position: " + flapPosition);
	}

	private void setWindStrength(int windStrength) {
		windEffect = windStrength;
	}

	@Preconditions("position==position")
	public void moveFlaps(int position) throws InterruptedException {
		goalPosition = position;
		actuate();
	}

	private void actuate() throws InterruptedException {
		FlapActuator flapActuatorStep5 = new FlapActuator(STRENGTH5);
		FlapActuator flapActuatorStep1 = new FlapActuator(STRENGTH1);

		flapActuatorStep5.start();
		flapActuatorStep1.start();

		//flapActuatorStep5.join();
		//flapActuatorStep1.join();
	}

	public static class FlapActuator extends Thread {
		int actuatorStrength;

		public FlapActuator(int step) {
			this.actuatorStrength = step;
		}

		@Override
		public void run() {
			int actuatorEffect = actuatorStrength;
			while (goalPosition - flapPosition>actuatorStrength || goalPosition-flapPosition<-1*actuatorStrength) {
				if (goalPosition > flapPosition) {
					actuatorEffect = actuatorStrength;
				} else {
					actuatorEffect = -1 * actuatorStrength;
				}

				flapPosition = flapPosition + actuatorEffect + windEffect;
				if (flapPosition > MAX_POSITION || flapPosition < MIN_POSITION) {
					assert false;
				}
				//System.out.println(toString() + " moved " + actuatorStrength
				//		+ " up to " + flapPosition + ". Goal: " + goalPosition);
			}
		}

		@Override
		public String toString() {
			return "Actuator[" + actuatorStrength + ']';
		}
	}
}
