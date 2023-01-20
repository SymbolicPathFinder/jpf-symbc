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

package gov.nasa.jpf.symbc.string.graph;

import java.util.ArrayList;
import java.util.List;

import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicIntegerGenerator;

public class Vertex {
	String name;
	StringBuilder solution;
	boolean constant;
	//int length;
	IntegerExpression symbolic_length;
	private static int count = 0;
	List<StringSymbolic> represents;
	int uniqueNumber;
	
	public Vertex (String name, SymbolicIntegerGenerator sig) {
		this.name = name;
		this.constant = false;
		//symbolic_length = new SymbolicInteger(name + ".length_" +count+ "_", 0, MinMax.MAXINT); //Must start with 0, for concat
		long l = MinMax.getVarMaxInt("");
		assert(l>=Integer.MIN_VALUE && l<=Integer.MAX_VALUE);
		symbolic_length = sig.create (name, 0, (int) l);
		this.uniqueNumber = count++;
	}
	
	public Vertex (String name, int length) {
		this.name = name;
		this.constant = false;
		symbolic_length = new IntegerConstant(length);
		this.uniqueNumber = count++;
	}
	
	public Vertex (String name, String solution, boolean constant) {
		this.name = name;
		this.solution = new StringBuilder(solution);
		this.constant = constant;
		this.symbolic_length = new IntegerConstant(solution.length());
		this.uniqueNumber = count++;
	}
	
	public Vertex (Vertex v) {
		this.name = v.name;
		this.solution = v.solution;
		this.constant = v.constant;
		this.symbolic_length = v.symbolic_length;
		this.count = v.count;
		this.represents = v.represents;
		this.uniqueNumber = v.uniqueNumber;
	}
	
	public String getName () {
		return name;
	}
	
	public int getLength () {
		if (constant) {
			return solution.length();
		}
		return (int) symbolic_length.solution();
	}
	
	public void setSolution (String s) {
		if (constant) throw new RuntimeException ("Can't set constant's solution");
		solution = new StringBuilder(s);
	}
	
	public String getSolution () {
		if (solution == null || this.getLength() == 0) return "";
		//if (solution == null) return "";
		return solution.toString();
	}
	
	public boolean isConstant () {
		return constant;
	}
	
	public void setCharSolution (char c, int index) {
		if (constant) throw new RuntimeException ("Can't set constant's solution");
		if (solution == null) {
			solution = new StringBuilder (index + 1);
		}
		while (solution.length() <= index) {
			solution.append("x");
		}
		solution.setCharAt(index, c);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Vertex other = (Vertex) obj;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}
	
	public String toString () {
		if (constant) {
			return "C_" + name;
		}
		return name;
	}
	
	public String uniqueName () {
		return name + "_" + uniqueNumber;
	}
	
	public IntegerExpression getSymbolicLength () {
		return symbolic_length;
	}
	
	public void setConstant (boolean b) {
		constant = b;
	}
	
	public void setLength (int l) {
		if (constant) {
			symbolic_length = new IntegerConstant(l);
		}
	}
	
	public void setRepresent (StringSymbolic ss) {
		represents = new ArrayList<StringSymbolic>();
		represents.add(ss);
	}
	
	public void addToRepresent (Vertex v) {
		if (represents != null) {
			if (v.represents != null) {
				represents.addAll(v.represents);
			}
		}
		else {
			represents = new ArrayList<StringSymbolic>();
			if (v.represents != null) {
				represents.addAll(v.represents);
			}
		}
	}
	
	public List<StringSymbolic> getRepresents () {
		return represents;
	}
}
