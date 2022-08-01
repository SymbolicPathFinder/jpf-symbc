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

import gov.nasa.jpf.symbc.numeric.SymbolicInteger;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class EdgeConcat implements Edge{
	Vertex left, right, dest;
	String name;
	
	public EdgeConcat (String name, Vertex left, Vertex right, Vertex dest) {
		this.name = name;
		this.left = left;
		this.right = right;
		this.dest = dest;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((dest == null) ? 0 : dest.hashCode());
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
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
		EdgeConcat other = (EdgeConcat) obj;
		if (dest == null) {
			if (other.dest != null)
				return false;
		} else if (!dest.equals(other.dest))
			return false;
		if (left == null) {
			if (other.left != null)
				return false;
		} else if (!left.equals(other.left))
			return false;
		if (right == null) {
			if (other.right != null)
				return false;
		} else if (!right.equals(other.right))
			return false;
		return true;
	}

	@Override
	public Vertex getDest() {
		return dest;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Vertex getSource() {
		throw new UnsupportedOperationException("getSource() can not be called on EdgeConcat");
	}

	@Override
	public List<Vertex> getSources() {
		List<Vertex> result = new ArrayList<Vertex>();
		result.add (left);
		result.add (right);
		return result;
	}

	@Override
	public boolean isDirected() {
		return true;
	}

	@Override
	public boolean isHyper() {
		return true;
	}

	@Override
	public void setDest(Vertex v) {
		dest = v;
		
	}

	@Override
	public void setSource(Vertex v) {
		throw new UnsupportedOperationException("setSource(Vertex) can not be called on EdgeConcat");
	}
	
	public void setSource (Vertex v, int i) {
		if (i == 0) {
			left = v;
		}
		else {
			right = v;
		}
	}

	@Override
	public boolean allVertecisAreConstant() {
		return left.isConstant() && right.isConstant() && dest.isConstant();
	}

	@Override
	public Edge cloneAndSwapVertices(Map<Vertex, Vertex> oldToNew) {
		return new EdgeConcat(name, oldToNew.get(left), oldToNew.get(right),
				oldToNew.get(dest));
	}
}
