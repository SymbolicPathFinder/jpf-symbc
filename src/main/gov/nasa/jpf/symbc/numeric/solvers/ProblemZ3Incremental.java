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

import java.util.*;

//TODO: problem: we do not distinguish between ints and reals?
// still needs a lot of work: do not use!


import com.microsoft.z3.*;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import symlib.Util;

public class ProblemZ3Incremental extends ProblemGeneral implements IncrementalSolver  {

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
  private boolean useFpForReals = false;

  public ProblemZ3Incremental() {
    Z3Wrapper z3 = Z3Wrapper.getInstance();
    solver = z3.getSolver();
    ctx = z3.getCtx();
    useFpForReals = SymbolicInstructionFactory.fp;
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


  public Object makeIntVar(String name, long min, long max) {
    try {
      IntExpr intConst = ctx.mkIntConst(name);
      solver.add(ctx.mkGe(intConst, ctx.mkInt(min)));
      solver.add(ctx.mkLe(intConst, ctx.mkInt(max)));
      return intConst;
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in makeIntVar: \n" + e);
    }
  }

  public Object makeRealVar(String name, double min, double max) {
    try {
      if (useFpForReals) {
        Expr expr = ctx.mkConst(name, ctx.mkFPSortDouble());
        solver.add(ctx.mkFPGt((FPExpr) expr, ctx.mkFP(min, ctx.mkFPSortDouble())));
        solver.add(ctx.mkFPLt((FPExpr) expr, ctx.mkFP(max, ctx.mkFPSortDouble())));
        return expr;
      } else {
        RealExpr expr = ctx.mkRealConst(name);
        solver.add(ctx.mkGe(expr, ctx.mkReal("" + min)));
        solver.add(ctx.mkLe(expr, ctx.mkReal("" + max)));
        return expr;
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object eq(long value, Object exp){
    try {
      return ctx.mkEq( ctx.mkInt(value), (Expr)exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object eq(Object exp, long value){

    return ctx.mkEq(ctx.mkInt(value), (Expr)exp);
  }

  // should we use Expr or ArithExpr?
  public Object eq(Object exp1, Object exp2){
    try{
      return  ctx.mkEq((Expr)exp1, (Expr)exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  // TODO: should convert double to rational
  //	public Object eq(double value, Object exp){
  //		try{
  //			return  ctx.MkEq(ctx.MkReal(arg0, arg1), (RealExpr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}

  //	public Object eq(Object exp, double value){
  //		try{
  //			return  ctx.MkEq(ctx.MkReal(arg0, arg1), (RealExpr)exp);;
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}

  public Object neq(long value, Object exp){
    return ctx.mkNot(ctx.mkEq(ctx.mkInt(value), (Expr)exp));
  }


  public Object neq(Object exp, long value){
    return ctx.mkNot(ctx.mkEq(ctx.mkInt(value), (Expr) exp));
  }

  public Object neq(Object exp1, Object exp2){
    try{
      return  ctx.mkNot(ctx.mkEq((Expr)exp1, (Expr)exp2));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object not(Object exp1){
    try{
      return  ctx.mkNot((BoolExpr)exp1);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  // TODO: convert doubles to rationals
  //	public Object neq(double value, Object exp){
  //		try{
  //			return  vc.notExpr(vc.eqExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //	public Object neq(Object exp, double value){
  //		try{
  //			return  vc.notExpr(vc.eqExpr((Expr)exp, vc.ratExpr(Double.toString(value), base)));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}

  public Object leq(long value, Object exp){
    try{
      return  ctx.mkLe(ctx.mkInt(value), (IntExpr)exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object leq(Object exp, long value){
    try{
      return  ctx.mkLe((IntExpr)exp,ctx.mkInt(value));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object leq(Object exp1, Object exp2){
    try{
      return  ctx.mkLe((ArithExpr)exp1, (ArithExpr)exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  //	public Object leq(double value, Object exp){
  //		try{
  //			return  vc.leExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //	public Object leq(Object exp, double value){
  //		try{
  //			return  vc.leExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  public Object geq(long value, Object exp){
    try{
      return  ctx.mkGe(ctx.mkInt(value),(IntExpr)exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object geq(Object exp, long value){
    try{
      return  ctx.mkGe((IntExpr)exp,ctx.mkInt(value));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object geq(Object exp1, Object exp2){
    try{
      return  ctx.mkGe((ArithExpr)exp1,(ArithExpr)exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  //	public Object geq(double value, Object exp){
  //		try{
  //			return  vc.geExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //	public Object geq(Object exp, double value){
  //		try{
  //			return  vc.geExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  public Object lt(long value, Object exp){
    try{
      return  ctx.mkLt(ctx.mkInt(value),(IntExpr)exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object lt(Object exp, long value){
    try{
      return  ctx.mkLt((IntExpr)exp,ctx.mkInt(value));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object lt(Object exp1, Object exp2){
    try{
      return  ctx.mkLt((ArithExpr)exp1,(ArithExpr)exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  //	public Object lt(double value, Object exp){
  //		try{
  //			return  vc.ltExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //	public Object lt(Object exp, double value){
  //		try{
  //			return  vc.ltExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //
  public Object gt(long value, Object exp){
    try{
      return  ctx.mkGt(ctx.mkInt(value),(IntExpr)exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object gt(Object exp, long value){
    try{
      return  ctx.mkGt((IntExpr)exp,ctx.mkInt(value));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  public Object gt(Object exp1, Object exp2){
    try{
      return  ctx.mkGt((ArithExpr)exp1,(ArithExpr)exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);

    }
  }

  //	public Object implies(Object exp1, Object exp2){
  //		try{
  //			return  vc.impliesExpr((Expr)exp1, (Expr)exp2);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}

  //	public Object gt(double value, Object exp){
  //		try{
  //			return  vc.gtExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //	public Object gt(Object exp, double value){
  //		try{
  //			return  vc.gtExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //
  //	    }
  //	}
  //
  //
  //
  //
  public Object plus(long value, Object exp) {
    try{
      return  ctx.mkAdd(new ArithExpr[] { ctx.mkInt(value), (IntExpr)exp});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object plus(Object exp, long value) {
    try{
      return  ctx.mkAdd(new ArithExpr[] { ctx.mkInt(value), (IntExpr)exp});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object plus(Object exp1, Object exp2) {
    try{
      return  ctx.mkAdd(new ArithExpr[] { (ArithExpr)exp1, (ArithExpr)exp2});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  //	public Object plus(double value, Object exp) {
  //		try{
  //			return  vc.plusExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}
  //
  //	public Object plus(Object exp, double value) {
  //		try{
  //			return  vc.plusExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}

  public Object minus(long value, Object exp) {
    try{
      return  ctx.mkSub(new ArithExpr[] { ctx.mkInt(value), (IntExpr)exp});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object minus(Object exp, long value) {
    try{
      return  ctx.mkSub(new ArithExpr[] {(IntExpr)exp, ctx.mkInt(value)});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object minus(Object exp1, Object exp2) {
    try{
      return  ctx.mkSub(new ArithExpr[] { (ArithExpr)exp1, (ArithExpr)exp2});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  //	public Object minus(double value, Object exp) {
  //		try{
  //			return  vc.minusExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}
  //
  //	public Object minus(Object exp, double value) {
  //		try{
  //			return  vc.minusExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}

  public Object mult(long value, Object exp) {
    try{
      return  ctx.mkMul(new ArithExpr[] {(IntExpr)exp, ctx.mkInt(value)});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object mult(Object exp, long value) {
    try{
      return  ctx.mkMul(new ArithExpr[] {(IntExpr)exp, ctx.mkInt(value)});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object mult(Object exp1, Object exp2) {
    try{
      return  ctx.mkMul(new ArithExpr[] {(ArithExpr)exp1, (ArithExpr)exp2});
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }
  //	public Object mult(double value, Object exp) {
  //		try{
  //			return  vc.multExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}
  //	public Object mult(Object exp, double value) {
  //		try{
  //			return  vc.multExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}
  //
  //	

  public Object div(long value, Object exp) {
    try{
      return  ctx.mkDiv(ctx.mkInt(value), (IntExpr)exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object div(Object exp, long value) {
    try{
      return  ctx.mkDiv((IntExpr)exp,ctx.mkInt(value));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object div(Object exp1, Object exp2) {
    try{
      return  ctx.mkDiv((ArithExpr)exp1,(ArithExpr)exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  public Object rem(Object exp, long value) {// added by corina
    try{

      return  ctx.mkRem((IntExpr) exp, ctx.mkInt(value));
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }
  public Object rem(long value, Object exp) {// added by corina
    try{

      return  ctx.mkRem(ctx.mkInt(value), (IntExpr) exp);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }
  public Object rem(Object exp1, Object exp2) {// added by corina
    try{
      if(exp2 instanceof Integer)
        return  ctx.mkRem((IntExpr)exp1,ctx.mkInt((Integer)exp2));
      return  ctx.mkRem((IntExpr) exp1, (IntExpr) exp2);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  //	public Object div(double value, Object exp) {
  //		try{
  //			return  vc.divideExpr(vc.ratExpr(Double.toString(value), base), (Expr)exp);
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}
  //	public Object div(Object exp, double value) {
  //		try{
  //			return  vc.divideExpr((Expr)exp, vc.ratExpr(Double.toString(value), base));
  //		} catch (Exception e) {
  //			e.printStackTrace();
  //			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
  //		}
  //	}

  public long getIntValue(Object dpVar) {
    try {
      Model model = null;
      if (Status.SATISFIABLE == solver.check()) {
        model = solver.getModel();
        return Long.parseLong((model.evaluate((IntExpr)dpVar,false)).toString());
      }
      else {
        System.out.println("Error retrieving int value from Z3.");
        assert false; // should not be reachable
        return 0;
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
    }
  }

  private Expr test(){
    Expr e = (Expr)makeIntVar("Z",-10, 10);
    Expr f = (Expr)makeIntVar("f", -10,10);
    Expr plus = (Expr)plus(10,e);
    Expr plus2 = (Expr)plus(1,e);
    Expr eq = (Expr)eq(plus, plus2);
    return eq;
  }

  public Boolean solve() {
    try {
      /* find model for the constraints above */
      Model model = null;                

      if (Status.SATISFIABLE == solver.check()) {   
        return true;
      } else {       
        return false;
      }
    } catch(Exception e){
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: " + e);
    }
  }

  public void post(Object constraint) {
    try{
      //solver.Assert((BoolExpr)constraint);
      solver.add((BoolExpr)constraint);
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error posting constraint to Z3 \n" + e);
    }
  }

  @Override
  public Object eq(double value, Object exp) {
    try {
      if (useFpForReals) {
        return ctx.mkFPEq(ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPEq((FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkNot(ctx.mkFPEq(ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp));
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
        return ctx.mkNot(ctx.mkFPEq((FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64())));
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
        return ctx.mkFPLEq(ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPLEq((FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPGEq(ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPGEq((FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPLt(ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPLt((FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPGt(ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPGt((FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPAdd(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPAdd(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPSub(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPSub(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPMul(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPMul(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
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
        return ctx.mkFPDiv(ctx.mkFPRoundNearestTiesToEven(), ctx.mkFPNumeral(value, ctx.mkFPSort64()), (FPExpr) exp);
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
        return ctx.mkFPDiv(ctx.mkFPRoundNearestTiesToEven(), (FPExpr) exp, ctx.mkFPNumeral(value, ctx.mkFPSort64()));
      } else {
        return ctx.mkDiv((ArithExpr) exp, ctx.mkReal("" + value));
      }
    } catch (Exception e) {
      e.printStackTrace();
      throw new RuntimeException("## Error Z3: div(double, Object) failed.\n" + e);
    }
  }

  @Override
  public Object and(long value, Object exp) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object and(Object exp, long value) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object and(Object exp1, Object exp2) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object or(long value, Object exp) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object or(Object exp, long value) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object or(Object exp1, Object exp2) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object xor(long value, Object exp) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object xor(Object exp, long value) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object xor(Object exp1, Object exp2) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftL(long value, Object exp) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftL(Object exp, long value) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftL(Object exp1, Object exp2) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftR(long value, Object exp) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftR(Object exp, long value) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftR(Object exp1, Object exp2) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftUR(long value, Object exp) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftUR(Object exp, long value) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object shiftUR(Object exp1, Object exp2) {
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public Object mixed(Object exp1, Object exp2) {
    // TODO Auto-generated method stub
    throw new RuntimeException("## Error Z3 \n");
  }

  @Override
  public double getRealValueInf(Object dpvar) {
    try {
      Model model = null;
      if (Status.SATISFIABLE == solver.check()) {
        model = solver.getModel();
        // TODO: clean this up
        String strResult = model.eval((Expr)dpvar, true).toString().replaceAll("\\s+","");
        Expr temp = model.eval((Expr)dpvar, false);
        if (temp instanceof com.microsoft.z3.RatNum) {
          strResult = ((com.microsoft.z3.RatNum)temp).toDecimalString(10);
        }
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
    // TODO Auto-generated method stub
    throw new RuntimeException("## Error Z3 \n");//return 0;
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
            Sort int_type = ctx.mkIntSort();
            return ctx.mkArrayConst(name, int_type, int_type);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object makeRealArrayVar(String name) {
        try {
            Sort int_type = ctx.mkIntSort();
            Sort real_type = ctx.mkRealSort();
            return ctx.mkArrayConst(name, int_type, real_type);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object select(Object exp1, Object exp2) {
        try {
            return ctx.mkSelect((ArrayExpr)exp1, (IntExpr)exp2);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object store(Object exp1, Object exp2, Object exp3) {
        try {
            return ctx.mkStore((ArrayExpr)exp1, (IntExpr)exp2, (IntExpr)exp3);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object realSelect(Object exp1, Object exp2) {
        try {
            return ctx.mkSelect((ArrayExpr)exp1, (IntExpr)exp2);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object realStore(Object exp1, Object exp2, Object exp3) {
        try {
            return ctx.mkStore((ArrayExpr)exp1, (IntExpr)exp2, (RealExpr)exp3);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object makeIntConst(long value) {
        try {
            return ctx.mkInt(value);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
    public Object makeRealConst(double value) {
        try {
            return ctx.mkReal("" + value);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("## Error Z3 : Exception caught in Z3 JNI: " + e);
        }
    }

    @Override
	public boolean isNonLinearSolver() {
		return true; //Returns true as Z3Incremental can solve NonLinearIntegerExpressions
	}
}
