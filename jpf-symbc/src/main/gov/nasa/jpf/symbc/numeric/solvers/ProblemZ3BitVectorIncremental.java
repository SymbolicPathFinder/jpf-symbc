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

package gov.nasa.jpf.symbc.numeric.solvers;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.concurrent.TimeUnit;

import com.microsoft.z3.*;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.string.translate.BVExpr;

public class ProblemZ3BitVectorIncremental extends ProblemGeneral implements IncrementalSolver {

  //This class acts as a safeguard to prevent
  //issues when referencing ProblemZ3 in case the z3 libs are
  //not on the ld_library_path. If the
  //Z3 solver object and context were class fields,
  //we would likely encounter a linker error
  private static class Z3Wrapper {
    private Context ctx;
    private Solver solver;

    private static Z3Wrapper instance = null;

    public static Z3Wrapper getInstance() {
      if (instance != null) {
        return instance;
      }

      return instance = new Z3Wrapper();
    }

    private Z3Wrapper() {
      HashMap<String, String> cfg = new HashMap<String, String>();
      cfg.put("model", "true");
      ctx = new Context(cfg);
      solver = ctx.mkSolver();
    }

    public Solver getSolver() {
      return this.solver;
    }

    public Context getCtx() {
      return this.ctx;
    }
  }

  private Solver solver;
  private Context ctx;

  // Do we use the floating point theory or linear arithmetic over reals
  private boolean useFpForReals;

  // Length of bit vectors and the implied min-max allowed values
  private int bitVectorLength;
  private long minAllowed;
  private long maxAllowed;

  public ProblemZ3BitVectorIncremental() {
    Z3Wrapper z3 = Z3Wrapper.getInstance();
    solver = z3.getSolver();
    ctx = z3.getCtx();

    // load bitvector length (default = 32 bit), then calculate allowed min-max values
    bitVectorLength = SymbolicInstructionFactory.bvlength;
    minAllowed = (long) -(Math.pow(2, bitVectorLength - 1));
    maxAllowed = (long) (Math.pow(2, bitVectorLength - 1) - 1);
    useFpForReals = SymbolicInstructionFactory.fp;
    if (SymbolicInstructionFactory.debugMode) { 
      System.out.println("Z3bitvector using " + bitVectorLength + "-bit bitvectors.");
      System.out.println("Allowed [min,max] values: [" + minAllowed + "," + maxAllowed + "].");
      System.out.println("Using floating point for reals: " + (useFpForReals ? "yes" : "no"));
    }
  }

  @Override
  public void push() {
    solver.push();
  }

  @Override
  public void pop() {
    solver.pop();
  }

  @Override
  public void reset() {
    solver.reset();
  }

  public void cleanup() {
    // nothing to be done here
  }

  /*
   * Throws a runtime exception if the given long is outside of the allowed range for the
   * used bit-vector length.
   */
  private void checkBounds(long l) {
    if (l < minAllowed || l > maxAllowed)
      throw new RuntimeException("Symbolic variable bound " + l + 
          " is outside the permitted range for bitvector length " + bitVectorLength);
  }

  public long getIntValue(Object dpVar) {
    try {
      Model model = null;
      if (Status.SATISFIABLE == solver.check()) {
        model = solver.getModel();
        String strResult = model.eval((Expr)dpVar, false).toString();
        return new BigInteger(strResult).longValue();
      }
      else {
        assert false; // should not be reachable
        return 0;
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in getIntValue: \n" + e);
    }
  }

  @Override
  public Boolean solve() {
    try {
      boolean result = false;
      if(SymbolicInstructionFactory.debugMode == true){
        System.out.println("\n\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
        System.out.println(solver.toString());
        long z3time = 0;
        long t1 = System.nanoTime();
        result = solver.check() == Status.SATISFIABLE ? true : false;
        z3time += System.nanoTime()-t1;
        System.out.println("\nSolving time of z3 bitvector is " + TimeUnit.NANOSECONDS.toMillis(z3time) + " ms");
        System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n");
      }
      else{
        result = solver.check() == Status.SATISFIABLE ? true : false;
      }
      return result;
    } catch(Exception e){
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: solve() failed.\n" + e);
    }
  }

  @Override
  public void post(Object constraint) {
    try{
      solver.add((BoolExpr)constraint);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: post(Object) failed.\n" + e);
    }
  }

  @Override
  public Object makeIntVar(String name, long min, long max) {
    checkBounds(min);
    checkBounds(max);
    try {
      //return ctx.mkIntConst(name);
      BitVecExpr bv = ctx.mkBVConst(name, this.bitVectorLength);
      solver.add(ctx.mkBVSGE(bv, ctx.mkBV(min, this.bitVectorLength)));
      solver.add(ctx.mkBVSLE(bv, ctx.mkBV(max, this.bitVectorLength)));
      return bv;
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: makeIntVar() failed.\n" + e);
    }
  }

  //    @Override
  //    public Object makeRealVar(String name, double min, double max) {
  //        try {
  //            Expr expr = ctx.mkConst(name, ctx.mkFPSortDouble());
  //            solver.add(ctx.mkFPGt((FPExpr) expr, ctx.mkFP(min, ctx.mkFPSortDouble())));
  //            solver.add(ctx.mkFPLt((FPExpr) expr, ctx.mkFP(max, ctx.mkFPSortDouble())));
  //            return expr;
  //        } catch (Exception e) {
  //            e.printStackTrace();
  //            throw new RuntimeException("## Error Z3: makeRealVar() failed.\n" + e);
  //        }
  //    }

  public Object makeRealVar(String name, double min, double max) {
    try {
      if (useFpForReals) {
        if (this.bitVectorLength == 32) {
          Expr expr = ctx.mkConst(name, ctx.mkFPSort32());
          solver.add(ctx.mkFPGt((FPExpr) expr, ctx.mkFP(min, ctx.mkFPSort32())));
          solver.add(ctx.mkFPLt((FPExpr) expr, ctx.mkFP(max, ctx.mkFPSort32())));
          return expr;
        } else {
          Expr expr = ctx.mkConst(name, ctx.mkFPSortDouble());
          solver.add(ctx.mkFPGt((FPExpr) expr, ctx.mkFP(min, ctx.mkFPSortDouble())));
          solver.add(ctx.mkFPLt((FPExpr) expr, ctx.mkFP(max, ctx.mkFPSortDouble())));
          return expr;
        }
      } else {
        RealExpr expr = ctx.mkRealConst(name);
        solver.add(ctx.mkGe(expr, ctx.mkReal("" + min)));
        solver.add(ctx.mkLe(expr, ctx.mkReal("" + max)));
        return expr;
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: makeRealVar() failed.\n" + e);
    }
  }

  @Override
  public Object eq(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkEq(ctx.mkBV(value, this.bitVectorLength), (Expr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkEq(ctx.mkInt(value), (Expr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: eq(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object eq(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkEq((Expr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkEq((Expr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: eq(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object eq(Object exp1, Object exp2){
    try{
      return ctx.mkEq((Expr) exp1, (Expr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: eq(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object neq(long value, Object exp) {
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkNot(ctx.mkEq(ctx.mkBV(value, this.bitVectorLength), (Expr) exp));
      } else if (exp instanceof IntExpr) {
        return ctx.mkNot(ctx.mkEq(ctx.mkInt(value), (Expr) exp));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: neq(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object neq(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkNot(ctx.mkEq((Expr) exp, ctx.mkBV(value, this.bitVectorLength)));
      } else if (exp instanceof IntExpr) {
        return ctx.mkNot(ctx.mkEq((Expr) exp, ctx.mkInt(value)));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: neq(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object neq(Object exp1, Object exp2){
    try{
      return ctx.mkNot(ctx.mkEq((Expr) exp1, (Expr) exp2));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: neq(Object, Object) failed.\n" + e);
    }
  }

  //    public Object not(Object exp1){
  //        try{
  //            return  ctx.mkNot((BoolExpr)exp1);
  //        } catch (Exception e) {
  //            e.printStackTrace();
  //            throw new RuntimeException("## Error Z3: not(Object) failed.\n" + e);
  //        }
  //    }

  @Override
  public Object leq(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSLE(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkLe(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: leq(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object leq(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSLE((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkLe((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: leq(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object leq(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof  BitVecExpr) {
        return ctx.mkBVSLE((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof IntExpr && exp2 instanceof  IntExpr) {
        return ctx.mkLe((IntExpr) exp1, (IntExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: leq(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object geq(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSGE(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkGe(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: geq(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object geq(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSGE((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkGe((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: geq(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object geq(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof  BitVecExpr) {
        return ctx.mkBVSGE((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof IntExpr && exp2 instanceof  IntExpr) {
        return ctx.mkGe((IntExpr) exp1, (IntExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: geq(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object lt(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSLT(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkLt(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: lt(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object lt(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSLT((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkLt((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: lt(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object lt(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof  BitVecExpr) {
        return ctx.mkBVSLT((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof ArithExpr && exp2 instanceof ArithExpr) {
        return ctx.mkLt((ArithExpr) exp1, (ArithExpr) exp2);
      } else if (exp1 instanceof FPExpr && exp2 instanceof FPExpr) {
        return ctx.mkFPLt((FPExpr) exp1, (FPExpr) exp2);
      } else {
        throw new RuntimeException("## Error in Z3: operator lt expected 2 ArithExpr. Received: " +
            exp1.getClass().toString() + " and " + exp2.getClass().toString());
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: lt(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object gt(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSGT(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkGt(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: gt(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object gt(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSGT((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkGt((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: gt(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object gt(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof  BitVecExpr) {
        return ctx.mkBVSGT((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof ArithExpr && exp2 instanceof ArithExpr) {
        return ctx.mkGt((ArithExpr) exp1, (ArithExpr) exp2);
      } else if (exp1 instanceof FPExpr && exp2 instanceof FPExpr) {
        return ctx.mkFPGt((FPExpr) exp1, (FPExpr) exp2);
      } else {
        throw new RuntimeException("## Error Z3: gt(Object, Object) expected 2 ArithExprs.");
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: gt(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object plus(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVAdd(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkAdd(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: plus(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object plus(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVAdd((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkAdd((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: plus(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object plus(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof BitVecExpr) {
        return ctx.mkBVAdd((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof IntExpr && exp2 instanceof IntExpr) {
        return ctx.mkAdd((IntExpr) exp1, (IntExpr) exp2);
      } else if (exp1 instanceof RealExpr && exp2 instanceof RealExpr) {
          return ctx.mkAdd((RealExpr) exp1, (RealExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: plus(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object minus(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSub(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkSub(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: minus(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object minus(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSub((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkSub((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: minus(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object minus(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof BitVecExpr) {
        return ctx.mkBVSub((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof ArithExpr && exp2 instanceof ArithExpr) {
        return  ctx.mkSub(new ArithExpr[] { (ArithExpr)exp1, (ArithExpr)exp2});
      } else if (exp1 instanceof FPExpr && exp2 instanceof FPExpr) {
        return ctx.mkFPSub(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp1, (FPExpr) exp2);
      } else {
        throw new RuntimeException("## Error in Z3: operator minus expected 2 ArithExpr. Received: " +
            exp1.getClass().toString() + " and " + exp2.getClass().toString());
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: minus(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object mult(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVMul(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkMul(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: mult(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object mult(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVMul((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkMul((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: mult(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object mult(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof BitVecExpr) {
        return ctx.mkBVMul((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof IntExpr && exp2 instanceof IntExpr) {
        return ctx.mkMul((IntExpr) exp1, (IntExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: mult(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object div(long value, Object exp){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSDiv(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else if (exp instanceof IntExpr) {
        return ctx.mkDiv(ctx.mkInt(value), (IntExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: div(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object div(Object exp, long value){
    checkBounds(value);
    try {
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSDiv((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else if (exp instanceof IntExpr) {
        return ctx.mkDiv((IntExpr) exp, ctx.mkInt(value));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: div(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object div(Object exp1, Object exp2){
    try {
      if (exp1 instanceof BitVecExpr && exp2 instanceof BitVecExpr) {
        return ctx.mkBVSDiv((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else if (exp1 instanceof IntExpr && exp2 instanceof IntExpr) {
        return ctx.mkDiv((IntExpr) exp1, (IntExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: div(Object, Object) failed.\n" + e);
    }
  }

  public Object rem(Object exp, long value) {
    checkBounds(value);
    try{
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSRem((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: rem(Object, int) failed.\n" + e);
    }
  }

  public Object rem(long value, Object exp) {
    checkBounds(value);
    try{
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSRem(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: rem(int, Object) failed.\n" + e);
    }
  }

  public Object rem(Object exp1, Object exp2) {
    try{
      if (exp1 instanceof BitVecExpr && exp2 instanceof BitVecExpr) {
        return ctx.mkBVSRem((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: rem(Object, Object) failed.\n" + e);
    }
  }

  public Object mod(Object exp, int value) {
    checkBounds(value);
    try{
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSMod((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: rem(Object, int) failed.\n" + e);
    }
  }

  public Object mod(int value, Object exp) {
    checkBounds(value);
    try{
      if (exp instanceof BitVecExpr) {
        return ctx.mkBVSMod(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: rem(int, Object) failed.\n" + e);
    }
  }

  public Object mod(Object exp1, Object exp2) {
    try{
      if (exp1 instanceof BitVecExpr && exp2 instanceof BitVecExpr) {
        return ctx.mkBVSMod((BitVecExpr) exp1, (BitVecExpr) exp2);
      } else {
        throw new RuntimeException();
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: rem(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object and(long value, Object exp) {
    try {
      return ctx.mkBVAND(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: and(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object and(Object exp, long value) {
    try {
      return ctx.mkBVAND((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: and(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object and(Object exp1, Object exp2) {
    try {
      return ctx.mkBVAND((BitVecExpr) exp1, (BitVecExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: and(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object or(long value, Object exp) {
    checkBounds(value);
    try {
      return ctx.mkBVOR(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: or(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object or(Object exp, long value) {
    checkBounds(value);
    try {
      return ctx.mkBVOR((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: or(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object or(Object exp1, Object exp2) {
    try {
      return ctx.mkBVOR((BitVecExpr) exp1, (BitVecExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: or(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object xor(long value, Object exp) {
    checkBounds(value);
    try {
      return ctx.mkBVXOR(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: xor(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object xor(Object exp, long value) {
    checkBounds(value);
    try {
      return ctx.mkBVXOR((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: xor(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object xor(Object exp1, Object exp2) {
    try {
      return ctx.mkBVXOR((BitVecExpr) exp1, (BitVecExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: xor(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object shiftL(long value, Object exp) {
    checkBounds(value);
    try {
      return ctx.mkBVSHL(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftL(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object shiftL(Object exp, long value) {
    checkBounds(value);
    try {
      return ctx.mkBVSHL((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftL(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object shiftL(Object exp1, Object exp2) {
    try {
      return ctx.mkBVSHL((BitVecExpr) exp1, (BitVecExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftL(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object shiftR(long value, Object exp) {
    checkBounds(value);
    try {
      return ctx.mkBVASHR(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftR(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object shiftR(Object exp, long value) {
    checkBounds(value);
    try {
      return ctx.mkBVASHR((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftR(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object shiftR(Object exp1, Object exp2) {
    try {
      return ctx.mkBVASHR((BitVecExpr) exp1, (BitVecExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftR(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object shiftUR(long value, Object exp) {
    checkBounds(value);
    try {
      return ctx.mkBVLSHR(ctx.mkBV(value, this.bitVectorLength), (BitVecExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftUR(int, Object) failed.\n" + e);
    }
  }

  @Override
  public Object shiftUR(Object exp, long value) {
    checkBounds(value);
    try {
      return ctx.mkBVLSHR((BitVecExpr) exp, ctx.mkBV(value, this.bitVectorLength));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftUR(Object, int) failed.\n" + e);
    }
  }

  @Override
  public Object shiftUR(Object exp1, Object exp2) {
    try {
      return ctx.mkBVLSHR((BitVecExpr) exp1, (BitVecExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: shiftUR(Object, Object) failed.\n" + e);
    }
  }

  @Override
  public Object eq(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPEq(ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkEq(ctx.mkReal("" + value), (Expr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: eq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object eq(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPEq((FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkEq((Expr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: eq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object neq(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkNot(ctx.mkFPEq(ctx.mkFPNumeral(value, sort), (FPExpr) exp));
      } else {
        return ctx.mkNot(ctx.mkEq(ctx.mkReal("" + value), (Expr) exp));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: neq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object neq(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkNot(ctx.mkFPEq((FPExpr) exp, ctx.mkFPNumeral(value, sort)));
      } else {
        return ctx.mkNot(ctx.mkEq((Expr) exp, ctx.mkReal("" + value)));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: neq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object leq(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPLEq(ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkLe(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: leq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object leq(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPLEq((FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkLe((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: leq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object geq(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPGEq(ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkGe(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: geq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object geq(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPGEq((FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkGe((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: geq(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object lt(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPLt(ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkLt(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: lt(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object lt(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPLt((FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkLt((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: lt(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object gt(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPGt(ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkGt(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: gt(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object gt(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPGt((FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkGt((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: gt(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object plus(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPAdd(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkAdd(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: plus(Object, double) failed.\n" + e);
    }
  }

  @Override
  public Object plus(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPAdd(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkAdd((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: plus(Object, double) failed.\n" + e);
    }
  }

  @Override
  public Object minus(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPSub(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkSub(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: minus(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object minus(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPSub(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkSub((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: minus(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object mult(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPMul(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkMul(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: mult(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object mult(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPMul(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkMul((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: mult(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object div(double value, Object exp) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPDiv(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, sort), (FPExpr) exp);
      } else {
        return ctx.mkDiv(ctx.mkReal("" + value), (ArithExpr) exp);
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: div(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object div(Object exp, double value) {
    try {
      if (useFpForReals) {
        FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
        return ctx.mkFPDiv(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, sort));
      } else {
        return ctx.mkDiv((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: div(double, Object) failed.\n" + e);
    }
  }

  private int bvCount = 0;

  @Override
  public Object mixed(Object exp1, Object exp2) {
    BitVecExpr bvExpr = null;
    bvExpr = (exp1 instanceof BitVecExpr ? ((BitVecExpr) exp1) : ((BitVecExpr) exp2));

    if (useFpForReals) {
      FPExpr converted = null;
      FPExpr fpExpr = null;

      fpExpr = (exp1 instanceof FPExpr ? ((FPExpr) exp1) : ((FPExpr) exp2));

      FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
      converted = ctx.mkFPToFP(bvExpr, sort);

      return ctx.mkFPEq(fpExpr, converted);
    } else {
      RealExpr realExpr = (exp1 instanceof RealExpr ? ((RealExpr) exp1) : ((RealExpr) exp2));

      // From jConstraints
      BitVecExpr exprAlias = null;
      BitVecSort sort = null;
      BitVecExpr zero = null;
      BoolExpr eq1 = null, eq2 = null;
      BoolExpr ltz = null;
      IntExpr bv2i = null, unsigned = null;
      IntExpr bound = null;
      IntExpr sub = null;

      sort = ctx.mkBitVecSort(this.bitVectorLength);
      exprAlias = (BitVecExpr)ctx.mkBVConst("__bv2i" + bvCount++, this.bitVectorLength);

      eq1 = ctx.mkEq(exprAlias, bvExpr);
      solver.add(eq1);
      bv2i = ctx.mkBV2Int(exprAlias, false);
      unsigned = ctx.mkIntConst("__bv2i" + bvCount++);
      eq2 = ctx.mkEq(bv2i, unsigned);
      solver.add(eq2);

      zero = (BitVecExpr) ctx.mkBV(0, this.bitVectorLength);
      ltz = ctx.mkBVSLT(exprAlias, zero);
      bound = ctx.mkInt(BigInteger.valueOf(2).pow(this.bitVectorLength).toString());
      sub = (IntExpr) ctx.mkSub(unsigned, bound);

      IntExpr intExpr = (IntExpr)ctx.mkITE(ltz, sub, unsigned);
      RealExpr converted = ctx.mkInt2Real(intExpr);
      return ctx.mkEq(realExpr, converted);
    }
  }

  private double getFPValue(FPExpr fpExpr) {
    Model model = solver.getModel();
    String rawValue = model.getConstInterp(fpExpr.getFuncDecl()).toString();
    String[] pieces = rawValue.split(" ");

    if (pieces.length < 2) {
      throw new RuntimeException("Error extracting value of FPExpr!");
    }

    double sig = Double.parseDouble(pieces[0]);
    int exp = Integer.parseInt(pieces[1]);

    return sig * Math.pow(2.0,  (double)exp);
  }

  @Override
  public double getRealValueInf(Object dpvar) {
    try {
      Model model = null;
      if (Status.SATISFIABLE == solver.check()) {
        if (dpvar instanceof FPExpr) {
          return getFPValue((FPExpr)dpvar);
        }

        model = solver.getModel();
        // TODO: clean this up
        String strResult = model.eval((Expr)dpvar, true).toString().replaceAll("\\s+","");
        Expr temp = model.eval((Expr)dpvar, false);
        if (temp instanceof com.microsoft.z3.RatNum) {
          // TODO: decide on the precision when calling toDecimalString
          strResult = ((com.microsoft.z3.RatNum)temp).toDecimalString(10);
        }

       // return Double.parseDouble(strResult);
        return Double.parseDouble(strResult.replace('?', '0'));
      }
      else {
        assert false; // should not be reachable
        return 0;
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  @Override
  public double getRealValueSup(Object dpVar) {
    // TODO Auto-generated method stub
    throw new RuntimeException("## Error Z3 \n");//return 0;
  }

  @Override
  public double getRealValue(Object dpVar) {
    return getRealValueInf(dpVar);
  }

  @Override
  public void postLogicalOR(Object[] constraint) {
    // TODO Auto-generated method stub
    throw new RuntimeException("## Error Z3 \n");
  }

    // Added by Aymeric to support arrays
    @Override
    public Object makeArrayVar(String name) {
        try {
			Sort sort = ctx.mkBitVecSort(this.bitVectorLength);
            return ctx.mkArrayConst(name, sort, sort);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object makeRealArrayVar(String name) {
        try {
            Sort int_type = ctx.mkBitVecSort(this.bitVectorLength);
            Sort real_type = ctx.mkRealSort();
            if (useFpForReals) {
                if (this.bitVectorLength == 32) {
                    real_type = ctx.mkFPSort32();
                } else {
                    real_type = ctx.mkFPSortDouble();
                }
            }
            return ctx.mkArrayConst(name, int_type, real_type);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }
    
    @Override
    public Object select(Object exp1, Object exp2) {
        try {
            return ctx.mkSelect((ArrayExpr)exp1, (BitVecExpr)exp2);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object store(Object exp1, Object exp2, Object exp3) {
        try {
            return ctx.mkStore((ArrayExpr)exp1, (BitVecExpr)exp2, (BitVecExpr)exp3);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object realSelect(Object exp1, Object exp2) {
        try {
            return ctx.mkSelect((ArrayExpr)exp1, (BitVecExpr)exp2);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object realStore(Object exp1, Object exp2, Object exp3) {
        try {
            if (useFpForReals) {
                return ctx.mkStore((ArrayExpr)exp1, (BitVecExpr)exp2, (FPExpr)exp3);
            }
            return ctx.mkStore((ArrayExpr)exp1, (BitVecExpr)exp2, (RealExpr)exp3);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object makeIntConst(long value) {
        checkBounds(value);
        try {
            return ctx.mkBV(value, this.bitVectorLength);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object makeRealConst(double value) {
        try {
            if (useFpForReals) {
                FPSort sort = this.bitVectorLength == 32 ? ctx.mkFPSort32() : ctx.mkFPSort64();
                return ctx.mkFPNumeral(value, sort);
            }
            return ctx.mkReal("" + value);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }
}
