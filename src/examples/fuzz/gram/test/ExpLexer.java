package fuzz.gram.test;

import gov.nasa.jpf.symbc.Debug;

public class ExpLexer {
	public enum TokenKind {
		INFIX, PREFIX, NUM, OP, COLUMN, END
	};

	private TokenKind kind;
	private int num;
	private char op;

	private int current_index;
	private String input;
	private char current;

	ExpLexer(String input) {
		if (input == null || input.length() == 0)
			throw new ParseException("empty parse string");
		this.input = input;
		this.current_index = 0;
		read_current();
	}

	String get_location() { 
		return String.format("position %d in %s", current_index, input);
	}
	private void lexer_error(String msg) {
		throw new ParseException(String.format("Lexer error at %s: %s", get_location(), msg));
	}

	private void read_current() {
		if (current_index < 0 || current_index >= input.length())
			lexer_error("outside string bounds");
		current = input.charAt(current_index);
	}

	private int read_num() {
		int start = current_index;
		while (current_index < input.length() && Character.isDigit(input.charAt(current_index)))
			++current_index;
		int end = current_index;
		//assert end > start;
		if(end<=start)
			throw new RuntimeException("assert violation in  in read_num");
		String str_num = input.substring(start, end);
		return Integer.parseInt(str_num, 10);
	}

	int get_num() { return num;}
	char get_op() { return op; }
	
	TokenKind nextToken() {
		if (current_index == input.length())
			kind = TokenKind.END;
		else {
			read_current();
			switch (current) {
			case 'i': kind = TokenKind.INFIX; ++current_index; break;
			case 'p': kind = TokenKind.PREFIX; ++current_index; break;
			case '+': case '-' : case '*' : case '/': kind = TokenKind.OP; ++current_index; op = current; break;
			case ':' :kind = TokenKind.COLUMN; ++current_index; break;
			default: 
				if (Character.isDigit(current)) {
					kind = TokenKind.NUM;
					num = read_num();
				} else {
					lexer_error("Unexpected character "+ current);
				}
			}
		}
		
		return kind;
	}
}