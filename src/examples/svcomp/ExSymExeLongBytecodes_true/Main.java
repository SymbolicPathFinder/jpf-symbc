package svcomp.ExSymExeLongBytecodes_true;/*
 * Origin of the benchmark:
 *     repo: https://babelfish.arc.nasa.gov/hg/jpf/jpf-symbc
 *     branch: updated-spf
 *     root directory: src/tests/gov/nasa/jpf/symbc
 * The benchmark was taken from the repo: 24 January 2018
 */
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

// package gov.nasa.jpf.symbc;
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    long x = Verifier.nondetInt();
    x = x > 0 ? -x : x;
    long y = 5;
    Main inst = new Main();
    inst.test(x, y);
  }

  /*
   * test LADD, LCMP, LMUL, LNEG, LSUB , Invokestatic bytecodes
   * no globals
   */

  public static void test(long x, long z) { // invokestatic

    System.out.println("Testing ExSymExeLongBytecodes");

    long a = x;
    long b = z;
    long c = 34565;

    long sum = a + b; // LADD

    long diff = a - b; // LSUB


    if (diff > c) {
      assert false;
      System.out.println("branch diff > c");
    } else System.out.println("branch diff <= c");
    if (sum < z) System.out.println("branch sum < z");
    else System.out.println("branch sum >= z");
  }
}
