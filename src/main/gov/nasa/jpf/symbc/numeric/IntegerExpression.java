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


//Copyright (C) 2005 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.

//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.

//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.


package gov.nasa.jpf.symbc.numeric;

//import java.util.*;
import static gov.nasa.jpf.symbc.numeric.Operator.*;

public abstract class IntegerExpression extends Expression {

    //returns -1 if (this < i), 0 if equal and 1 otherwise
    public IntegerExpression _cmp (long i)
    {
        return new BinaryNonLinearIntegerExpression(this, CMP, new IntegerConstant(i));
    }

    public IntegerExpression _cmp_reverse (long i)
    {
        return new BinaryNonLinearIntegerExpression(new IntegerConstant(i), CMP, this);
    }

    public IntegerExpression _cmp (IntegerExpression e)
    {
        return new BinaryNonLinearIntegerExpression(this, CMP, e);
    }

//------------------------------------------------------

	public IntegerExpression _minus_reverse (long i)
	{
		return new BinaryNonLinearIntegerExpression(new IntegerConstant(i), MINUS, this);
	}

	public IntegerExpression _minus (long i)
	{
		//simplify
		if (i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, MINUS, new IntegerConstant(i));
	}

	public IntegerExpression _minus (IntegerExpression e)
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 0)
				return this;
		}
		if (e == this)
			return new IntegerConstant(0);

		return new BinaryNonLinearIntegerExpression(this, MINUS, e);
	}

	public IntegerExpression _mul (long i)
	{
		//simplify
		if (i == 1)
			return this;
		if (i == 0)
			return new IntegerConstant(0);

		return new BinaryNonLinearIntegerExpression(this, MUL, new IntegerConstant(i));
	}

	public IntegerExpression _mul (IntegerExpression e)
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 1)
				return this;
			if (ic.value == 0)
				return new IntegerConstant(0);
		}

		return new BinaryNonLinearIntegerExpression(this, MUL, e);
	}

	public IntegerExpression _plus (long i)
	{
		//simplify
		if (i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, PLUS, new IntegerConstant(i));
	}

	public IntegerExpression _plus (IntegerExpression e)
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 0)
				return this;
		}

		return new BinaryNonLinearIntegerExpression(this, PLUS, e);
	}

	public IntegerExpression _shiftR(IntegerExpression i) {
		//simplify
		if (i instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)i;
			if (ic.value == 0)
				return this;
		}

		return new BinaryNonLinearIntegerExpression(this, SHIFTR, i);
	}

	public IntegerExpression _shiftL(IntegerExpression i) {
		if (i instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)i;
			if (ic.value == 0)
				return this;
		}

		return new BinaryNonLinearIntegerExpression(this, SHIFTL, i);
	}

	public IntegerExpression _shiftUR(IntegerExpression i) {
		if (i instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)i;
			if (ic.value == 0)
				return this;
		}

		return new BinaryNonLinearIntegerExpression(this, SHIFTUR, i);
	}

	public IntegerExpression _and(IntegerExpression e)
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 0)
				return new IntegerConstant(0);
		}

		return new BinaryNonLinearIntegerExpression(this, AND, e);
	}

	public IntegerExpression _or(IntegerExpression e) {
		if(e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant) e;
			if(ic.value == 0) {
				return this;
			}
		}
		return new BinaryNonLinearIntegerExpression(this, OR, e);
	}

	public IntegerExpression _xor(IntegerExpression e) {
		return new BinaryNonLinearIntegerExpression(this, XOR, e);
	}

	public IntegerExpression _shiftR(long i)
	{
		if(i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, SHIFTR,
											new IntegerConstant( i));

	}

	public IntegerExpression _shiftL(long i) {
		if(i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, SHIFTL,
											new IntegerConstant( i));
	}

	public IntegerExpression _shiftUR(long i) {
		if(i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, SHIFTUR,
											new IntegerConstant( i));
	}

	public IntegerExpression _and(long i)
	{
		if(i == 0)
			return new IntegerConstant(0);
		return new BinaryNonLinearIntegerExpression(this, AND, new IntegerConstant(i));
	}

	public IntegerExpression _or(long i)
	{
		if(i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, OR, new IntegerConstant( i));
	}

	public IntegerExpression _xor(long i)
	{
		return new BinaryNonLinearIntegerExpression(this, XOR, new IntegerConstant( i));
	}

	public IntegerExpression _rem(long i)
	{
		return new BinaryNonLinearIntegerExpression(this, REM, new IntegerConstant( i));
	}
	
	public IntegerExpression _rem_reverse(long i)
	{
		//throw new RuntimeException( "## Error: Operation not supported!" );
		return new BinaryNonLinearIntegerExpression(new IntegerConstant( i), REM, this);
	}
	
	public IntegerExpression _rem(IntegerExpression i)
	{
		return new BinaryNonLinearIntegerExpression(this, REM, i);
	}

	public IntegerExpression _neg()
	{
		return new BinaryNonLinearIntegerExpression(new IntegerConstant(0), MINUS, this);
	}

	public IntegerExpression _div (long i)
	{
		// simplify
		assert (i != 0);
		if (i == 1)
			return this;
		return new BinaryNonLinearIntegerExpression(this, DIV, new IntegerConstant(i));
	}

	public IntegerExpression _div (IntegerExpression e)
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			assert (ic.value != 0);
			if (ic.value == 1)
				return this;
		}
		if (e == this)
			return new IntegerConstant(1);

		return new BinaryNonLinearIntegerExpression(this, DIV, e);
	}

	public IntegerExpression _div_reverse (long i)
	{
		if (i == 0)
			return new IntegerConstant(0);
		return new BinaryNonLinearIntegerExpression(new IntegerConstant(i), DIV, this);
	}

	//TODO test this
	public long solution() {
		throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
		//System.out.println("Expression Solution request Error: " + this);
		//return -666;
	}
	public int solutionInt() {
		throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
	}
	public char solutionChar() {
		throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
	}

	public abstract Object accept(ConstraintExpressionVisitor2 visitor);
	//protected void finalize() throws Throwable {
    //	System.out.println("Finalized LIExp -> " + this);
    //}
}
