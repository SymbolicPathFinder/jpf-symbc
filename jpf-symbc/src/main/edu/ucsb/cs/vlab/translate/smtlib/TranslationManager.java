package edu.ucsb.cs.vlab.translate.smtlib;

import edu.ucsb.cs.vlab.translate.smtlib.generic.NumericConstraintTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.NumericExpressionTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.StringConstraintTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.StringExpressionTranslator;

public class TranslationManager {
	public NumericConstraintTranslator numCons;
	public NumericExpressionTranslator numExpr;
	public StringConstraintTranslator strCons;
	public StringExpressionTranslator strExpr;
	
	public TranslationManager() {}
}
