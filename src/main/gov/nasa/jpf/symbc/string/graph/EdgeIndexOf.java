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

import gov.nasa.jpf.symbc.string.SymbolicIndexOfInteger;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class EdgeIndexOf implements Edge {

	Vertex source, dest;
	SymbolicIndexOfInteger sioi;
	String name;
	
	public EdgeIndexOf (String name, Vertex source, Vertex dest, SymbolicIndexOfInteger sioi) {
		this.name = name;
		this.source = source;
		this.dest = dest;
		this.sioi = sioi;
	}
	
	@Override
	public boolean allVertecisAreConstant() {
		return source.isConstant() && dest.isConstant();
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
		return source;
	}

	@Override
	public List<Vertex> getSources() {
		List<Vertex> result = new ArrayList<Vertex>();
		result.add (source);
		return result;
	}

	@Override
	public boolean isDirected() {
		return true;
	}

	@Override
	public boolean isHyper() {
		return false;
	}

	@Override
	public void setDest(Vertex v) {
		this.dest = v;
	}

	@Override
	public void setSource(Vertex v) {
		this.source= v;
	}
	
	public SymbolicIndexOfInteger getIndex () {
		return sioi;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((dest == null) ? 0 : dest.hashCode());
		result = prime * result + ((source == null) ? 0 : source.hashCode());
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
		EdgeIndexOf other = (EdgeIndexOf) obj;
		if (dest == null) {
			if (other.dest != null)
				return false;
		} else if (!dest.equals(other.dest))
			return false;
		if (source == null) {
			if (other.source != null)
				return false;
		} else if (!source.equals(other.source))
			return false;
		return true;
	}

	@Override
	public Edge cloneAndSwapVertices(Map<Vertex, Vertex> oldToNew) {
		return new EdgeIndexOf(name, oldToNew.get(source), oldToNew.get(dest),
				sioi);
	}
}
