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
// 
//implements real expressions
package gov.nasa.jpf.symbc.numeric;

//import java.util.*;
import static gov.nasa.jpf.symbc.numeric.Operator.*;

public abstract class RealExpression extends Expression {

	public RealExpression _minus_reverse (double i) 
	{
		return new BinaryRealExpression(new RealConstant(i), MINUS, this);
	}
	
	public RealExpression _minus (double i) 
	{
		return new BinaryRealExpression(this, MINUS, new RealConstant(i));
	}

	public RealExpression _minus (RealExpression e) 
	{
		return new BinaryRealExpression(this, MINUS, e);
	}

	public RealExpression _mul (double i) 
	{
		return new BinaryRealExpression(this, MUL, new RealConstant(i));
	}

	public RealExpression _mul (RealExpression e) 
	{
		return new BinaryRealExpression(this, MUL, e);
	}

	public RealExpression _plus (double i) 
	{
		return new BinaryRealExpression(this, PLUS, new RealConstant(i));
	}

	public RealExpression _plus (RealExpression e) 
	{
		return new BinaryRealExpression(this, PLUS, e);
	}
	
	public RealExpression _div_reverse(double i) 
	{
		//assert (i!=0);
		return new BinaryRealExpression(new RealConstant(i), DIV, this );
	}

	public RealExpression _div (double i) 
	{
		assert (i!=0);
		return new BinaryRealExpression(this, DIV, new RealConstant(i));
	}
	
	public RealExpression _div (RealExpression e) 
	{
		return new BinaryRealExpression(this, DIV, e);
	}
	
	public RealExpression _neg () 
	{
		return new BinaryRealExpression(new RealConstant(0), MINUS, this);
	}
	

	//TODO test this
	public double solution() {
		throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
		//System.out.println("Expression Solution request Error: " + this);
		//return -666;
	}
}
