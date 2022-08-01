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

import java.util.List;
import java.util.Map;

public interface Edge {
	public String getName ();
	
	public Vertex getSource();
	
	public void setSource(Vertex v);
	
	public List<Vertex> getSources ();
	
	public Vertex getDest ();
	
	public void setDest (Vertex v);
	
	public boolean isHyper ();
	
	public boolean isDirected ();
	
	public boolean allVertecisAreConstant();

	/**
	 * Create a deep clone of the edge, replacing any vertexes with the ones in
	 * 'oldToNew'
	 * 
	 * @param oldToNew
	 *            Map with vertices to be replaced
	 * @return Cloned Edge with vertices replaced
	 */
	
	public Edge cloneAndSwapVertices(Map<Vertex, Vertex> oldToNew); 
}
