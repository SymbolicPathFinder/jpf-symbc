package fuzz.gram.test;

import java.util.Scanner;

import fuzz.gram.test.ExpLexer.TokenKind;
import gov.nasa.jpf.symbc.Debug;

/**
 * This is a parser for a simple expression grammar (E) either in infix (Ei) or
 * prefix (Ep) notation
 * <p>
 * (r0) E -> 'i' Ei
 * </p>
 * <p>
 * (r1) E -> 'p' Ep
 * </p>
 * <p>
 * (r2) Ei -> Num
 * </p>
 * <p>
 * (r3) Ei -> Num Op Num
 * </p>
 * <p>
 * (r4) Num -> [1-9][0-9]*
 * </p>
 * ( The following 4 parsing rules for Op, could also be considered a single
 * lexer rule
 * <p>
 * (r58) Op-> '+'|'-'| '*' | '/'
 * </p>
 * )
 * <p>
 * (r5) Op -> '+'
 * </p>
 * <p>
 * (r6) Op -> '-'
 * </p>
 * <p>
 * (r7) Op -> '*'
 * </p>
 * <p>
 * (r8) Op -> '/'
 * </p>
 * <p>
 * (r9) Ep -> Num
 * </p>
 * <p>
 * (r10) Ep -> Op Num '," Num
 * </p>
 * The grammar is not supposed to require/allow spaces. In case of parse error
 * should throw ParseException, other exceptions are considered bugs. E.g.: bad
 * space in "i 1"
 * 
 */
public class ExpParser {
	/**
	 * This implementation uses a lexer. The intent is to mark the tokens it
	 * returns as symbolic, as in the paper "Grammar-based Whitebox Fuzzing" by P.
	 * Godefroid In addition to having lexer.nextToken() symbolic, we plan to also
	 * use lexer.get_num() and lexer.get_op();
	 */
	ExpLexer lexer;

	ExpParser(String input) {
		lexer = new ExpLexer(input);
	}

	private void parse_error(String msg) {
		throw new ParseException(String.format("Parse error at %s: %s", lexer.get_location(), msg));
	}

	private int i_eval() {
		
		int res = -1;
		if (lexer.nextToken() == TokenKind.NUM) { //match the '12' in 'i12+1", (r2 or r3)
			
			res = lexer.get_num();
			TokenKind token = lexer.nextToken();
			if (token == TokenKind.OP) {          //match the Op ('+') in 'i12+1" (r3)
				
				char op = lexer.get_op();
				if (lexer.nextToken() == TokenKind.NUM) { //match final '1' in 'i12+1"
					if(op=='/') {
						System.out.println("found... ");
						//Debug.printPC("PC");
					}
					
					switch (op) {
					case '+':                     //match the '+' in 'i12+1"
						res = res + lexer.get_num();
						break;
					case '-':
						res = res - lexer.get_num();
						break;
					case '*':
						res = res * lexer.get_num();
						break;
					case '/':
						System.out.println("found again... "+op);
						int num = lexer.get_num();
						if (num == 0) {
							assert(false);
						  Debug.printPC("PC before passed assert : solved= "+Debug.getSolvedPC()+"\n---\n");
						  res = res / num; // possible error!
						} 
						else {
						   Debug.printPC("PC before failed assert : solved= "+Debug.getSolvedPC()+"\n---\n");
						   assert(num!=0);
						}
						break;
					default:
						parse_error("Looks like lexer was broken op=" + op);
					}
					
				} else
					parse_error("Second operand/number expected");
			} else if (token != TokenKind.END)
				parse_error("Unexpected token");
		} else
			parse_error("Number expected");
		return res;
	}

	private int p_eval() {
		int res = -1;
		TokenKind token = lexer.nextToken();
		if (token == TokenKind.NUM)
			res = lexer.get_num();
		else if (token == TokenKind.OP) {
			char op = lexer.get_op();
			if (lexer.nextToken() != TokenKind.NUM)
				parse_error("First operand expected");
			res = lexer.get_num();
			if (lexer.nextToken() != TokenKind.COLUMN)
				parse_error("Parse error: ':' expected");
			if (lexer.nextToken() != TokenKind.NUM)
				parse_error("Second operand expected");
			switch (op) {
			case '+':
				res = res + lexer.get_num();
				break;
			case '-':
				res = res - lexer.get_num();
				break;
			case '*':
				res = res * lexer.get_num();
				break;
			case '/':
				res = res / lexer.get_num(); // possible error!
				break;
			default:
				parse_error("Looks like lexer was broken");
			}
		} else if (token != TokenKind.END)
			parse_error("Unexpected token");
		return res;
	}

	/**
	 * Consider the string "i12+1". The leftmost derivation for this is
	 * <p>
	 * E (r0)-> "i" Ei (r3)-> "i" Num Op Num (r4)-> "i12" Op Num (r5)-> "i12+" Num
	 * (r4)-> "i12+1".
	 * </p>
	 * This derivation forms a parse tree.
	 **/
	int eval() {
		
		int res = -1;
		TokenKind token = lexer.nextToken();
		if (token == TokenKind.INFIX) {//match the 'i' in 'i12+1", (r0)
			res = i_eval(); // Wish: res tainted by rule (r0)
		}
		else if (token == TokenKind.PREFIX)
			res = p_eval(); // Wish: res tainted by rule (r1)
		else
			parse_error("Unexpected token");
		if (lexer.nextToken() != TokenKind.END)
			parse_error("Unexpected, extra input");
		return res;
	}

	/*
	 * Some testing functions
	 */
	static int eval_str(String str) {
		ExpParser expparser = new ExpParser(str);
		int res = expparser.eval();
		return res;
	}

	static Boolean check(String str, int expected) {
		int val = eval_str(str);
		Boolean res = val == expected;
		System.out.println(String.format("eval(%s) = %d, %b", str, val, res));
		return res;
	}

	static void basic_tests() {
		System.out.println("TESTING");
		check("i1", 1);
		check("i10", 10);
		check("i10+1", 11);
		check("i10+3", 13);
		check("i10-3", 7);
		check("i10*3", 30);
		check("i10/4", 2);

		check("p1", 1);
		check("p10", 10);
		check("p+10:1", 11);
		check("p+10:3", 13);
		check("p-10:3", 7);
		check("p*10:3", 30);
		check("p/10:4", 2);
	}

	static void user_test() {
		Scanner scanner = new Scanner(System.in);
		System.out.println("Other expression:");
		// String exp_str = scanner.next(); This stops at space.

		String exp_str = scanner.nextLine();
		System.out.println(eval_str(exp_str));
		//scanner.close();
	}

	public static void main(String[] args) {
		//basic_tests();
		//user_test();
		// modified by corina
		try {
			
			int SIZE=5;
			char[] in = new char[SIZE];
			
			in[0]=Debug.addSymbolicChar('i',"in"+0);
			in[1]=Debug.addSymbolicChar('1',"in"+1);
			in[2]=Debug.addSymbolicChar('0',"in"+2);
			in[3]=Debug.addSymbolicChar('/',"in"+3);
			in[4]=Debug.addSymbolicChar('4',"in"+4);
			String in_str = new String(in);
			eval_str(in_str);
			Debug.printPC("****PC");
			
			//check("i10/4", 2);
			/*
			int SIZE=6;
			char[] in = new char[SIZE];
			in[0]='i';
			//in[1]='1';
			//in[2]='0';
			in[1]=Debug.makeSymbolicChar("num_0");
			in[2]=Debug.makeSymbolicChar("num_1");
			in[3]='/';
			in[4]=Debug.makeSymbolicChar("num_2");
			in[5]=Debug.makeSymbolicChar("num_3");
			String in_str = new String(in);
			eval_str(in_str);
			Debug.printPC("****PC");
			*/
			
		}
		catch(Exception e) {
			//System.out.println("Ignore Parse exception");
		}
	}
}
