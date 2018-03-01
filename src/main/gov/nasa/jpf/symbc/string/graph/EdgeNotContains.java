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
import java.util.Map;

public class EdgeNotContains implements Edge{

	Vertex source, dest;
	String name;
	
	public EdgeNotContains (String name, Vertex source, Vertex dest) {
		this.name = name;
		this.source = source;
		this.dest = dest;
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
		this.source = v;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		int smallest, biggest, v1HashCode, v2HashCode;
		v1HashCode = source.hashCode();
		v2HashCode = dest.hashCode();
		if (v1HashCode > v2HashCode) {
			smallest = v2HashCode;
			biggest = v1HashCode;
		}
		else {
			smallest = v1HashCode;
			biggest = v2HashCode;
		}
		result = prime * result + ((source == null) ? 0 : smallest);
		result = prime * result + ((dest == null) ? 0 : biggest);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof EdgeNotContains)) {
			return false;
		}
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		EdgeNotContains other = (EdgeNotContains) obj;
		if (source == null) {
			if (other.source != null)
				return false;
		} 
		if (dest == null) {
			if (other.dest != null)
				return false;
		} 
		
		if (source.equals(other.source) && dest.equals(other.dest)) {
			//System.out.println("[NOTE] " + this.toString() + " is equal to " + other.toString());
			return true;
		}
		else if (source.equals(other.dest) && dest.equals(other.source)) {
			//System.out.println("[NOTE] " + this.toString() + " is equal to " + other.toString());
			return true;
		}
		
		return false;
	}

	@Override
	public Edge cloneAndSwapVertices(Map<Vertex, Vertex> oldToNew) {
		return new EdgeNotContains(name, oldToNew.get(source),
				oldToNew.get(dest));
	}
}
