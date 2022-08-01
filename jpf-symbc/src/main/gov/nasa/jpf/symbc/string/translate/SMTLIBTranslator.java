package gov.nasa.jpf.symbc.string.translate;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.DerivedStringExpression;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringConstraint;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicCharAtInteger;
import gov.nasa.jpf.symbc.string.SymbolicIndexOf2Integer;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfChar2Integer;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfCharInteger;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOf2Integer;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfChar2Integer;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfCharInteger;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicLengthInteger;

public class SMTLIBTranslator {

	public Set<String> constraints = new HashSet<String>();
	public Set<String> stringVariables = new HashSet<String>();
	public Set<String> numericVariables = new HashSet<String>();
	public String constraintsExpression = null;
	public String declarations = null;
	public String numericExpression = null;
	public String finalTranslation = null;
	
	public String translate(StringPathCondition pc){
		return translate(pc, "");
	}
	
	public String translate(StringPathCondition pc, String AdditionalConstraints){
		StringConstraint sc = pc.header;
		Constraint npc = pc.getNpc().header;
		this.constraintsExpression = stringConstraintToSMTLIB(sc);
		this.numericExpression = numericConstraintToSMTLIB(npc);
		this.declarations = symbolicStringDeclarations(stringVariables) + symbolicNumericDeclarations(numericVariables);
		this.finalTranslation = this.declarations + this.constraintsExpression + this.numericExpression + AdditionalConstraints + "\n(check-sat)\n";
		pc.smtlib = this.finalTranslation;
		return this.finalTranslation;
	}
	
	public String symbolicStringDeclarations(Set<String> symbolicVars){
		String symbolicDecs = "";
		for (String var : symbolicVars) {
		    symbolicDecs += "(declare-fun " + var.toString() + " () String)\n";
		}
		return symbolicDecs;
	}
	
	public String symbolicNumericDeclarations(Set<String> symbolicVars){
		String symbolicDecs = "";
		for (String var : symbolicVars) {
		    symbolicDecs += "(declare-fun " + var.toString() + " () Int)\n";
		}
		return symbolicDecs;
	}
	
	public void saveSMTLIB(String file){
		PrintWriter writer;
		try {
			writer = new PrintWriter(file);
			writer.println(";--------------------------\n;" + file + "\n\n"  + this.finalTranslation);
			writer.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		
	}
	
	private String stringConstraintToSMTLIB(StringConstraint sc){
		if (sc == null){return "";}
		StringConstraint and_sc = sc.and();
		String result;
		
		switch(sc.getComparator()){
			case CONTAINS:
				result = translateContains(sc);
				break;
			case NOTCONTAINS:
				result = translateNotContains(sc);
				break;
			case STARTSWITH:
				result = translateStartsWith(sc);
				break;
			case NOTSTARTSWITH:
				result = translateNotStartsWith(sc);
				break;
			case EQUALS:
				result = translateEquals(sc);
				break;
			case NOTEQUALS:
				result = translateNotEquals(sc);
				break;
			case EQUALSIGNORECASE:
				result = translateEqualsIgnoreCase(sc);
				break;
			case NOTEQUALSIGNORECASE:
				result = translateNotEqualsIgnoreCase(sc);
				break;
			case ENDSWITH:
				result = translateEndsWith(sc);
				break;
			case NOTENDSWITH:
				result = translateNotEndsWith(sc);
				break;
			case EMPTY:
				result = translateEmpty(sc);
				break;
			case NOTEMPTY:
				result = translateNotEmpty(sc);
				break;
			case MATCHES:
				result = translateMatches(sc);
				break;
			case NOMATCHES:
				result = translateNoMatches(sc);
				break;
			case REGIONMATCHES:
				result = translateRegionMatches(sc);
				break;
			case NOREGIONMATCHES:
				result = translateNoRegionMatches(sc);
				break;
			case ISINTEGER:
				result = translateIsInteger(sc);
				break;
			case NOTINTEGER:
				result = translateNotInteger(sc);
				break;
			case ISFLOAT:
				result = translateIsFloat(sc);
				break;
			case NOTFLOAT:
				result = translateNotFloat(sc);
				break;
			case ISLONG:
				result = translateIsLong(sc);
				break;
			case NOTLONG:
				result = translateNotLong(sc);
				break;
			case ISDOUBLE:
				result = translateIsDouble(sc);
				break;
			case NOTDOUBLE:
				result = translateNotDouble(sc);
				break;
			case ISBOOLEAN:
				result = translateIsBoolean(sc);
				break;
			case NOTBOOLEAN:
				result = translateNotBoolean(sc);
				break;			
			default:
				result = sc.getComparator().toString() + "-not-implemented"; 
				break;
		}
		
		if(and_sc != null){
			return "(assert " + result + ")" + "\n" + stringConstraintToSMTLIB(and_sc);
		}
		else{
			return "(assert " + result + ")";
		}
	}
	
	private String stringExpressionToSMTLIB(StringExpression se){
		if( se == null){ return "";}
		
		if (se instanceof StringConstant) {
			return translateStringConstant(se);
		}
		else if (se instanceof StringSymbolic) {
			return translateStringSymbolic(se);
		}
		else if (se instanceof DerivedStringExpression) {
			switch (((DerivedStringExpression) se).op) {
				case CONCAT:
					return translateConcat(se);
				case SUBSTRING:
					return translateSubstring(se);
				case TRIM:
					return translateTrim(se);
				case REPLACE:
					return translateReplace(se);
				case REPLACEALL:
					return translateReplaceAll(se);
				case REPLACEFIRST:
					return translateReplaceFirst(se);
				case TOLOWERCASE:
					return translateToLowerCase(se);
				case TOUPPERCASE:
					return translateToUpperCase(se);
				case VALUEOF:
					return translateValueOf(se);
						
				default:
					return "String-Expression-OP-" + ((DerivedStringExpression) se).op + "-not-yet-implemented";
			}
		}
		else{
			return "String-expression-" + se.toString() + "-not-handled";
		}
	}

	private String numericExpressionToSMTLIB(IntegerExpression ie){
		if(ie instanceof IntegerConstant){
			return Integer.toString((int)((IntegerConstant) ie).value);
		}
		else if (ie instanceof SymbolicLastIndexOfCharInteger){
			return translateSymbolicLastIndexOfChar(ie);
		}
		else if (ie instanceof SymbolicLastIndexOfChar2Integer){
			return translateSymbolicLastIndexOfChar2Integer(ie);
		}
		else if (ie instanceof BinaryLinearIntegerExpression){
			return translateBinaryLinearIntegerExpression(ie);
		}
		else if (ie instanceof SymbolicIndexOfCharInteger){
			return translateSymbolicIndexOfCharInteger(ie);
		}
		else if (ie instanceof SymbolicIndexOfChar2Integer){
			return translateSymbolicIndexOfChar2Integer(ie);
		}
		else if (ie instanceof SymbolicCharAtInteger){
			return translateSymbolicCharAtInteger(ie);
		}
		else if (ie instanceof SymbolicIndexOf2Integer){
			return translateSymbolicIndexOf2Integer(ie);
		}
		else if (ie instanceof SymbolicIndexOfInteger){
			return translateSymbolicIndexOfInteger(ie);
		}
		else if (ie instanceof SymbolicLastIndexOf2Integer){
			return translateSymbolicLastIndexOf2Integer(ie);
		}
		else if (ie instanceof SymbolicLastIndexOfInteger){
			return translateSymbolicLastIndexOfInteger(ie);
		}
		else if (ie instanceof SymbolicLengthInteger){
			return translateSymbolicLengthInteger(ie);
		}
		else if(ie instanceof SymbolicInteger){
			return translateSymbolicInteger(ie);
		}
		else{
			println("Integer Expression " + ie.toString() + " of type "+ ie.getClass().toString() + " not handled.\n");
			return ie.toString() + "-Integer-Expression-not-yet-handled.";
		}			
	}

	private String numericConstraintToSMTLIB(Constraint npc){
		if (SymbolicInstructionFactory.debugMode)
			System.out.println("numeric constraint: " + npc);
		
		String result="", finalResult = "";
		
		boolean stringCastLeft, stringCastRight;
		
		//if( npc.getLeft() instanceof SymbolicCharAtInteger)
			
		while(npc != null){
		
			String op = npc.getComparator().toString();
			
			stringCastRight = false;
			stringCastLeft = false;
			String arg1, arg2;
			
			if( npc.getRight() instanceof SymbolicCharAtInteger && npc.getLeft() instanceof IntegerConstant ){
				stringCastLeft = true;
				int x = (int)((IntegerConstant)npc.getLeft()).value;
				arg1 = "\"" + Character.toString((char) x) + "\"";
			}
			else{
				arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
			}
			if( npc.getLeft() instanceof SymbolicCharAtInteger && npc.getRight() instanceof IntegerConstant ){
				int y = (int)((IntegerConstant)npc.getRight()).value;
				arg2 = "\"" + Character.toString((char) y) + "\"";
			}
			else{
				arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
			}
			
			finalResult = finalResult + "\n" + "(assert (" + op + " " + arg1 + " " + arg2 + "))";
			npc = npc.and;
		}
		return finalResult;
		
//		while(npc != null){
//			switch (npc.getComparator()){
//				case EQ:
//					result = translateEquals(npc);
//					break;
//				case NE:
//					result = translateNotEquals(npc);
//					break;
//				case LT:
//					result = translateLessThan(npc);
//					break;
//				case LE:
//					result = translateLessThanEquals(npc);
//					break;
//				case GT:
//					result = translateGreaterThan(npc);
//					break;
//				case GE:
//					result = translateGreaterThanEquals(npc);				
//					break;
//				default:
//					result = npc.getComparator().toString() + "-not-implemented"; 
//					break;
//			}
//			npc = npc.and;
//			finalResult = finalResult + "\n" + "(assert (" + result + ")";
//		}
//		return finalResult;
	}	
	
//	private String translateGreaterThanEquals(Constraint npc) {
//		String arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
//		String arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
//		return "(>= " + arg1 + " " + arg2 + ")";
//	}
//
//	private String translateGreaterThan(Constraint npc) {
//		String arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
//		String arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
//		return "(> " + arg1 + " " + arg2 + ")";
//	}
//
//	private String translateLessThanEquals(Constraint npc) {
//		String arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
//		String arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
//		return "(<= " + arg1 + " " + arg2 + ")";
//	}
//
//	private String translateLessThan(Constraint npc) {
//		String arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
//		String arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
//		return "(< " + arg1 + " " + arg2 + ")";
//	}
//
//	private String translateNotEquals(Constraint npc) {
//		String arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
//		String arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
//		return "(!= " + arg1 + " " + arg2 + ")";
//	}
//
//	private String translateEquals(Constraint npc) {
//		String arg1 = numericExpressionToSMTLIB((IntegerExpression) npc.getLeft());
//		String arg2 = numericExpressionToSMTLIB((IntegerExpression) npc.getRight());
//		return "(== " + arg1 + " " + arg2 + ")";
//	}

	
	private String translateStringSymbolic(StringExpression se) {
		String symVarName = ((StringSymbolic) se).fixName(((StringSymbolic) se).getName());
		stringVariables.add(symVarName);
		return symVarName;
	}
	
	private String translateSymbolicCharAtInteger(IntegerExpression ie) {
		SymbolicCharAtInteger scai = (SymbolicCharAtInteger) ie;
		String arg1 = stringExpressionToSMTLIB(scai.getExpression());
		
		String arg2 = numericExpressionToSMTLIB(scai.getIndex());
		return "(charAt " + arg1 + " " + arg2 + ")";
	}

	private String translateSymbolicLengthInteger(IntegerExpression ie) {
		SymbolicLengthInteger sli = (SymbolicLengthInteger) ie;
		String arg1 = stringExpressionToSMTLIB(sli.getExpression());
		return "(len " + arg1 + ")";
	}

	private String translateSymbolicLastIndexOfInteger(IntegerExpression ie) {
		SymbolicLastIndexOfInteger si = (SymbolicLastIndexOfInteger) ie;
		String arg1 = stringExpressionToSMTLIB(si.getSource());
		String arg2 = stringExpressionToSMTLIB(si.getExpression());
		return "(lastIndexOf" + " " + arg1 + " " + arg2 + ")";
	}

	private String translateSymbolicLastIndexOf2Integer(IntegerExpression ie) {
		SymbolicLastIndexOf2Integer si = (SymbolicLastIndexOf2Integer) ie;
		String arg1 = stringExpressionToSMTLIB(si.getSource());
		String arg2 = stringExpressionToSMTLIB(si.getExpression());
		String arg3 = numericExpressionToSMTLIB(si.getMinIndex());
		return "(lastIndexOf" + " " + arg1 + " " + arg2 + " " + arg3 + ")";
	}

	private String translateSymbolicIndexOfInteger(IntegerExpression ie) {
		SymbolicIndexOfInteger si = (SymbolicIndexOfInteger) ie;
		String arg1 = stringExpressionToSMTLIB(si.getSource());
		String arg2 = stringExpressionToSMTLIB(si.getExpression());
		return "(indexOf" + " " + arg1 + " " + arg2 + ")";
	}

	private String translateSymbolicIndexOf2Integer(IntegerExpression ie) {
		SymbolicIndexOf2Integer si = (SymbolicIndexOf2Integer) ie;
		String arg1 = stringExpressionToSMTLIB(si.getSource());
		String arg2 = stringExpressionToSMTLIB(si.getExpression());
		String arg3 = numericExpressionToSMTLIB(si.getMinIndex());
		return "(indexOf" + " " + arg1 + " " + arg2 + " " + arg3 + ")";
	}

	
	private String translateSymbolicIndexOfChar2Integer(IntegerExpression ie) {
		SymbolicIndexOfChar2Integer si = (SymbolicIndexOfChar2Integer) ie;
		String arg1 = stringExpressionToSMTLIB(si.getSource());
		String arg2 = numericExpressionToSMTLIB(si.getExpression());
		String arg3 = numericExpressionToSMTLIB(si.getMinDist());
		return "(indexOf" + " " + arg1 + " " + arg2 + " " + arg3 + ")";
	}

	private String translateSymbolicIndexOfCharInteger(IntegerExpression ie) {
		SymbolicIndexOfCharInteger sioci = (SymbolicIndexOfCharInteger) ie;
		String arg1 = stringExpressionToSMTLIB(sioci.getSource());
		String arg2 = numericExpressionToSMTLIB(sioci.getExpression());
		return "(indexOf" + " " + arg1 + " " + arg2 + ")";
	}

	private String translateSymbolicLastIndexOfChar2Integer(IntegerExpression ie) {
		SymbolicLastIndexOfChar2Integer si = (SymbolicLastIndexOfChar2Integer) ie;
		String arg1 = stringExpressionToSMTLIB(si.getSource());
		String arg2 = numericExpressionToSMTLIB(si.getExpression());
		String arg3 = numericExpressionToSMTLIB(si.getMinDist());
		return "(lastIndexOf" + " " + arg1 + " " + arg2 + " " + arg3 + ")";
	}
	
	private String translateBinaryLinearIntegerExpression(IntegerExpression ie) {
		BinaryLinearIntegerExpression blie = (BinaryLinearIntegerExpression) ie;
		String op = blie.getOp().toString();
		String arg1 = numericExpressionToSMTLIB(blie.getLeft());
		String arg2 = numericExpressionToSMTLIB(blie.getRight());
		return "(" + op + " " + arg1 + " " + arg2 +")";
	}

	private String translateSymbolicInteger(IntegerExpression ie) {
		SymbolicInteger si = (SymbolicInteger) ie;
		numericVariables.add(si.getName());
		return si.getName();	
	}

	private String translateValueOf(StringExpression se) {
		String arg = null;
		DerivedStringExpression dse = (DerivedStringExpression) se;
		if ( dse.oprlist[0] instanceof StringExpression){
			arg = stringExpressionToSMTLIB((StringExpression) dse.oprlist[0]);
		}
		else if (dse.oprlist[0] instanceof IntegerExpression){
			arg = numericExpressionToSMTLIB((IntegerExpression) dse.oprlist[0]);
		}
		return "(valueOf " + arg + ")";
	}

	private String translateToUpperCase(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String arg = stringExpressionToSMTLIB((StringExpression) dse.right);
		return "(toUpperCase " + arg + ")";
	}


	private String translateToLowerCase(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String arg = stringExpressionToSMTLIB((StringExpression) dse.right);
		return "(toLowerCase " + arg + ")";
	}

	private String translateReplaceFirst(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		
		String arg0 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[0]);
		String arg1 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[1]);
		String arg2 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[2]);
		
		return "(replaceFirst " + arg0 + " " + arg1 + " " + arg2 + ")";
	}

	private String translateReplaceAll(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String arg0 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[0]);
		String arg1 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[1]);
		String arg2 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[2]);
		return "(replaceAll " + arg0 + " " + arg1 + " " + arg2 + ")";
	}

	private String translateReplace(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String arg0 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[0]);
		String arg1 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[1]);
		String arg2 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[2]);
		return "(replace " + arg0 + " " + arg1 + " " + arg2 + ")";
	}
	private String translateTrim(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String arg = stringExpressionToSMTLIB((StringExpression) dse.right);
		return "(trim " + arg + ")";
	}

	private String translateSubstring(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String arg1 = stringExpressionToSMTLIB((StringExpression) dse.oprlist[0]);
		String arg2 = numericExpressionToSMTLIB((IntegerExpression) dse.oprlist[1]);
		String arg3 = "";
		if(dse.oprlist.length == 3){
			arg3 = numericExpressionToSMTLIB((IntegerExpression) dse.oprlist[2]);
		}
		return "(subString " + arg1 + " " + arg3 + " " + arg2 + ")";
	}

	private String translateConcat(StringExpression se) {
		DerivedStringExpression dse = (DerivedStringExpression) se;
		String leftArg = stringExpressionToSMTLIB(dse.left);
		String rightArg = stringExpressionToSMTLIB(dse.right);
		return "(concat " + leftArg + " " + rightArg + ")";
	}

	private String translateStringConstant(StringExpression se) {
		return "\"" + ((StringConstant) se).value + "\"";
	}

	private String translateSymbolicLastIndexOfChar(IntegerExpression ie) {
		SymbolicLastIndexOfCharInteger slioci = (SymbolicLastIndexOfCharInteger) ie;
		String leftArg = stringExpressionToSMTLIB(slioci.getSource());
		String rightArg = numericExpressionToSMTLIB(slioci.getExpression());
		return "(lastIndexOfChar" + " " + leftArg + " " + rightArg + ")";
	}

	private String translateNotContains(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (contains " + leftArg + " " + rightArg + " ))";
	}

	private String translateContains(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(contains " + leftArg + " " + rightArg + " )";
	}
	
	private String translateEquals(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(= " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotEquals(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (= " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateEqualsIgnoreCase(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(equalsIgnoreCase " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotEqualsIgnoreCase(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (equalsIgnoreCase " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateStartsWith(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(startsWith " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotStartsWith(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (startsWith " + leftArg + " " + rightArg + " ))";
	}

	private String translateEndsWith(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(endsWith " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotEndsWith(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (endsWith " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateEmpty(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(empty " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotEmpty(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (empty " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateRegionMatches(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(regionMatches " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNoRegionMatches(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (regionMatches " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateMatches(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(matches " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNoMatches(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (matches " + leftArg + " " + rightArg + " ))";
	}

	private String translateIsInteger(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(isInteger " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotInteger(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (isInteger " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateIsFloat(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(isFloat " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotFloat(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (isFloat " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateIsLong(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(isLong " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotLong(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (isLong " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateIsDouble(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(isDouble " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotDouble(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (isDouble " + leftArg + " " + rightArg + " ))";
	}
	
	private String translateIsBoolean(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(isBoolean " + leftArg + " " + rightArg + " )";
	}
	
	private String translateNotBoolean(StringConstraint sc) {
		String leftArg  = stringExpressionToSMTLIB(sc.getLeft());
		String rightArg = stringExpressionToSMTLIB(sc.getRight());
		return "(not (isBoolean " + leftArg + " " + rightArg + " ))";
	}
	
	private void println(String string) {
		System.out.println("[SMTLIBTranslator] " + string);
	}
}
