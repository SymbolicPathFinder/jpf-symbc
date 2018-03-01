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

public class EdgeNoCharAt implements Edge{

	Vertex v1, v2;
	String name;
	
	public EdgeNoCharAt (String name, Vertex v1, Vertex v2) {
		this.v1 = v1;
		this.v2 = v2;
		this.name = name;
	}
	
	@Override
	public boolean allVertecisAreConstant() {
		return v1.isConstant() && v2.isConstant();
	}

	@Override
	public Vertex getDest() {
		return v2;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Vertex getSource() {
		return v1;
	}

	@Override
	public List<Vertex> getSources() {
		List<Vertex> result = new ArrayList<Vertex>();
		result.add(v1);
		return result;
	}

	@Override
	public boolean isDirected() {
		return false;
	}

	@Override
	public boolean isHyper() {
		return false;
	}

	@Override
	public void setDest(Vertex v) {
		v2 = v;
		
	}

	@Override
	public void setSource(Vertex v) {
		v1 = v;
	}

	@Override
	public Edge cloneAndSwapVertices(Map<Vertex, Vertex> oldToNew) {
		return new EdgeNoCharAt(name, oldToNew.get(v1), oldToNew.get(v2));
	}

}
