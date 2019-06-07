package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.ISSABasicBlock;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This represents a phi condition, that associates a "condition" with the "then" and the "else side.
 */
public class PhiCondition {
    public enum Branch {Then, Else};

    public final Branch branch;
    public final Expression condition;

    public PhiCondition(Branch branch, Expression condition) {
        this.branch = branch;
        this.condition = condition;
    }


}
