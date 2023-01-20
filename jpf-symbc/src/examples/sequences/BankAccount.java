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

package sequences;

import gov.nasa.jpf.symbc.Preconditions;



/**
 *
 * @author Mithun Acharya
 * Taken from Inkumsah, Xie's ASE08 paper
 */
public class BankAccount {
	private int balance;
	private int numberOfWithdrawals;


	public BankAccount(int amount){
		balance = amount;
	}

    //@Preconditions("amount<1000&&amount>-1000")
	public void deposit(int amount){
		if (amount>0)
			//System.out.println("I am easily reachable in deposit");
			balance = balance + amount;
	}

    //@Preconditions("amount<1000&&amount>-1000")
	public void withdraw(int amount){
		if(amount>balance){
			//System.out.println("I am easily reachable in withdraw");
			return;
		}
		if (numberOfWithdrawals>=5){// was 10
			assert(false);
			//System.out.println("I am very hard to reach in withdraw");
			return;
		}
		balance = balance - amount;
		numberOfWithdrawals++;
	}
}
