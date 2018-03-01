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


import gov.nasa.jpf.symbc.Debug;


public class FlapController {
	private static int goal;
	private static int currentPosition = 0;
	private static boolean emergencySpeed = false;
	private static final int TIMEOUT = 3;

	public static void main(String[] args) throws InterruptedException {
		emergencySpeed = false;
		int x = 15;
		int y = 0;
		boolean emergency = true;
		startThreads(x, y, emergency);
	}

	//@Preconditions("setGoal==setGoal")
	public static void startThreads(int g, int p,
			boolean e) throws InterruptedException {
		goal=g;
		FlapMovement flapMovement = new FlapMovement(p);
		EmergencySensor emergencySensor = new EmergencySensor(e);
		flapMovement.start();
		emergencySensor.start();

	}

	public static class FlapMovement extends Thread {

		public FlapMovement(int initialPosition) {
			currentPosition = initialPosition;
		}

		@Override
		public void run() {
			// while(true){
			int time = 0;
			while (currentPosition != goal) {
				if (emergencySpeed) {
					if (goal > currentPosition) {
						currentPosition = currentPosition + 10;// (goal-currentPosition)*1/2;
					} else {
						currentPosition = currentPosition - 10;
					}
				} else {
					if (goal > currentPosition) {
						currentPosition = currentPosition + 1;// (goal-currentPosition)*1/2;
					} else {
						currentPosition = currentPosition - 1;
					}
				}
				time++;
				if (time > 1) {
					Debug.printPC("\n Path Condition: ");
					assert false;
				}
			}
			currentPosition=1*currentPosition;
			// }
		}
	}

	public static class EmergencySensor extends Thread {
		private boolean emergency;
		private int oldGoal;

		public EmergencySensor(boolean emergency) {
			this.emergency = emergency;
		}

		@Override
		public void run() {
			if (emergency) {
				oldGoal = goal;
				goal = 30;
				emergencySpeed = true;
			} else {
				emergencySpeed = false;
			}
		}
	}
}
