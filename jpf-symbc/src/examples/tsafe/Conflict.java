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

package tsafe;


//import gov.nasa.jpf.continuity.SymbolicRealVars;


public class Conflict {
  private static final double degToRad = Math.PI/180.0;
  private static final double g = 68443.0;

  public static double snippet (double psi1, double vA, double vC, double xC0, double yC0, double psiC, double bank_ang) {
    String PATH = "";
    double dmin = 999;
    double dmst = 2;
    double psiA = psi1 * degToRad;
    int signA = 1;
    int signC = 1;

    if (psiA < 0) {
      PATH += "psiA<0\n";
      signA = -1;
    } else {
      PATH += "psiA>=0\n";
    }
    double rA = Math.pow(vA, 2.0) / Math.tan(bank_ang*degToRad) / g;
    double rC = Math.pow(vC, 2.0) / Math.tan(bank_ang*degToRad) / g; 

    double t1 = Math.abs(psiA) * rA / vA;
    double dpsiC = signC * t1 * vC/rC;
    double xA = signA*rA*(1-Math.cos(psiA));      
    double yA = rA*signA*Math.sin(psiA);

    double xC = xC0 +
      signC*rC* (Math.cos(psiC)-Math.cos(psiC+dpsiC));
    double yC = yC0 -
      signC*rC*(Math.sin(psiC)-Math.sin(psiC+dpsiC));
                                
    double xd1 = xC - xA;
    double yd1 = yC - yA;    
                        
    double d = Math.sqrt(Math.pow(xd1, 2.0) + Math.pow(yd1, 2.0));
    double minsep;

    // min sep in turn                        
    if (d < dmin) {
      PATH += "d < dmin\n";
      dmin = d;
    } else {
      PATH += "d >= dmin\n";
    }

    if (dmin < dmst) {
      PATH += "dmin < dmst\n";
      minsep = dmin;
    } else { 
      PATH += "dmin >= dmst\n";
      minsep = dmst;
    }
    System.out.println(">>> PATH: " + PATH);
    return minsep;
  }


  public static void main(String[] args) {
//    double aPsi = SymbolicRealVars.getSymbolicReal(0.0, 360.0, "aPsi");
//    double aV = SymbolicRealVars.getSymbolicReal(-100.0, 100.0, "av");

//    double c1X = SymbolicRealVars.getSymbolicReal(-100.0, 100.0, "c1X");
//    double c1Y = SymbolicRealVars.getSymbolicReal(-100.0, 100.0, "c1Y");
//    double c1Psi = SymbolicRealVars.getSymbolicReal(-100.0, 100.0, "c1Psi");
//    double c1V = SymbolicRealVars.getSymbolicReal(-100.0, 100.0, "c1v");

//    double cpA0_1_bankAng = SymbolicRealVars.getSymbolicReal(0.0, 50.0, "cpA0_1_bankAng");

//    if ((aV > 0.0) && (cpA0_1_bankAng > 0.0)) {
//      double minsep_sec_result = snippet(aPsi, aV, c1V, c1X, c1Y, c1Psi, cpA0_1_bankAng);
      double minsep_sec_result = snippet(0, 0, 0, 0, 0, 0, 0);
//      SymbolicRealVars.notePathFunction("minsep_sec_result");
//    }
   }
}
