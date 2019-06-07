package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

/**
 * This is the first pass of SPFCases that creates SPFCases nodes. It assumes substitution has run. The purpose of this transformation is to provide a place holder for specific instructions to become SPFCase Statements in RangerIR.
 */

public enum SpfCasesInstruction {
    THROWINSTRUCTION,
    NEWINSTRUCTION,
    ARRAYINSTRUCTION,
    INVOKE, //any invoke that has reached SPFCase pass, is an invoke that we couldn't deal with, and so we leave it up to SPF.
    RETURN,
    ALL
}
