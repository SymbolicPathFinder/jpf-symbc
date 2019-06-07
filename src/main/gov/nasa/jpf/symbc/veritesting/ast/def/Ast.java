package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

/**
 * Interface that provides the signature of accept method which all Statements in RangerIR supports.
 */
public interface Ast {
     public abstract <T> T accept(AstVisitor<T> visitor);

}
