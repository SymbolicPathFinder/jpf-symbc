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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class StringGraph {
	private List<Vertex> vertices; /* Maybe make this a hashmap */
	private List<Edge> edges;
	
	public StringGraph () {
		vertices = new ArrayList<Vertex>();
		edges = new ArrayList<Edge>();
	}

	/**
	 * Create a new StringGraph that is a deep clone of 'toClone'
	 * 
	 * @param toClone
	 *            Graph to be cloned
	 */
	public StringGraph (StringGraph toClone) {
		List<Vertex> originalVertices = toClone.getVertices();
		List<Edge> originalEdges = toClone.getEdges();
		this.vertices = new ArrayList<Vertex>(originalVertices.size());
		this.edges = new ArrayList<Edge>(originalEdges.size());
		
		// we need to replace original vertices with the cloned ones
		// in the edges
		Map<Vertex,Vertex> oldToNew = new HashMap<Vertex,Vertex>(); 
		
		//clone vertices
		for(Vertex v : originalVertices) {
			Vertex newVertex = new Vertex(v);
			this.vertices.add(newVertex);
			oldToNew.put(v, newVertex);
		}
		
		//clone edges
		for(Edge e : originalEdges) {
			Edge newEdge = e.cloneAndSwapVertices(oldToNew);
			this.edges.add(newEdge);
		}
	}
	
	/*public void addEquals (String n1, String n2) {
		Vertex v1 = new Vertex (n1);
		Vertex v2 = new Vertex (n2);
		addEdge (v1, v2, new EdgeEqual("EqualsEdge_" + n1 + "=" + n2, v1, v2));
	}
	
	public void addNotEquals (String n1, String n2) {
		Vertex v1 = new Vertex (n1);
		Vertex v2 = new Vertex (n2);
		addEdge (v1, v2, new EdgeNotEqual("EqualsNotEdge_" + n1 + "=" + n2, v1, v2));
	}*/
	
	public void addEdge (Vertex v1, Vertex v2, Edge e) {
		if (!vertices.contains(v1)) vertices.add(v1);
		else {
			//println ("[StringGraph] Source already in: " + v1.uniqueName() + " @ " + vertices.indexOf(v1) + " which is " +  vertices.get(vertices.indexOf(v1)).uniqueName());
			e.setSource(vertices.get(vertices.indexOf(v1)));
			//println ("[StringGraph] Source changed to: " + e.getSource().uniqueName());
		}
		if (!vertices.contains(v2)) vertices.add(v2);
		else {
			e.setDest(vertices.get(vertices.indexOf(v2)));
		}
		if (!edges.contains(e)) edges.add(e);
	}
	
	public void addEdge (Vertex s1, Vertex s2, Vertex d1, EdgeConcat e) {
		if (s1 == null || s2 == null) throw new RuntimeException();
		
		if (!vertices.contains(s1)) vertices.add(s1);
		else e.setSource(vertices.get(vertices.indexOf(s1)), 0);
		if (!vertices.contains(s2)) vertices.add(s2);
		else e.setSource(vertices.get(vertices.indexOf(s2)), 1);
		if (!vertices.contains(d1)) vertices.add(d1);
		else {
			e.setDest(vertices.get(vertices.indexOf(d1)));
		}
		if (!edges.contains(e)) edges.add(e);
	}
	
	/*public void addVertex (String n1) {
		addVertex (new Vertex (n1));
	}*/
	
	public void addConstantVertex (String name, String solution) {
		addVertex (new Vertex (name, solution, true));
	}
	
	public void addVertex (Vertex v) {
		if (v == null) throw new RuntimeException();
		if (!vertices.contains(v)) vertices.add(v);
	}
	
	
	public void mergeIn (StringGraph g) {
		for (Vertex v: g.vertices) {
			if (v == null) throw new RuntimeException();
			if (!vertices.contains(v)) vertices.add(v);
		}
		for (Edge e: g.edges) {
			if (!edges.contains(e)) edges.add(e);
		}
	}
	
	public String toString () {
		return "Vertices: " + vertices.toString() + "\nEdges: " + edges.toString();
	}
	
	public String toDot () {
		StringBuilder sb = new StringBuilder();
		int concatTemp = 0;
		sb.append ("digraph test123 {\n");
		for (Edge e: edges) {
			if (e instanceof EdgeConcat) {
				sb.append("\t");
				sb.append ("\"");
				sb.append (e.getSources().get(0));
				sb.append ("\"");
				sb.append ("->");
				sb.append("c");
				sb.append (String.valueOf(concatTemp));
				sb.append(" [label=\"Concat left\"]\n");
				
				sb.append("\t");
				sb.append ("\"");
				sb.append (e.getSources().get(1));
				sb.append ("\"");
				sb.append ("->");
				sb.append("c");
				sb.append (String.valueOf(concatTemp));
				sb.append(" [label=\"Concat right\"]\n");
				
				sb.append("\t");
				sb.append("c");
				sb.append (String.valueOf(concatTemp));
				sb.append ("->");
				sb.append ("\"");
				sb.append (e.getDest());
				sb.append ("\"");
				sb.append(" [label=\"Concat dest\"]\n");
				concatTemp++;
				
			}
			else {
				sb.append("\t");
				sb.append ("\"");
				sb.append (e.getSource());
				sb.append ("\"");
				sb.append ("->");
				sb.append ("\"");
				sb.append(e.getDest());
				sb.append ("\"");
				sb.append(" [label=\"");
				//sb.append(e.getName());
				if (e instanceof EdgeNotStartsWith) {
					sb.append ("!StartsWith");
				}
				else if (e instanceof EdgeStartsWith) {
					sb.append ("StartsWith");
				}
				else if (e instanceof EdgeNotEqual) {
					sb.append ("!Equal");
				}
				else if (e instanceof EdgeEqual) {
					sb.append ("Equal");
				}
				else if (e instanceof EdgeTrimEqual) {
					sb.append ("Trim");
				}
				else if (e instanceof EdgeSubstring1Equal) {
					sb.append ("Substring.1");
				}
				else if (e instanceof EdgeSubstring2Equal) {
					sb.append ("Substring.2");
				}			
				else if (e instanceof EdgeNotEndsWith) {
					sb.append ("!EndsWith");
				}
				else if (e instanceof EdgeEndsWith) {
					sb.append ("EndsWith");
				}
				else if (e instanceof EdgeCharAt) {
					sb.append ("EdgeCharAt");
				}
				else if (e instanceof EdgeIndexOf) {
					sb.append ("EdgeIndexOf");
				}
				else if (e instanceof EdgeIndexOf2) {
					sb.append ("EdgeIndexOf2");
				}
				else if (e instanceof EdgeContains) {
					sb.append ("EdgeContains");
				}
				else if (e instanceof EdgeNotContains) {
					sb.append ("EdgeNotContains");
				}
				else {
					sb.append (e.getClass().toString());
				}
				sb.append("\"");
				if (!e.isDirected()) {
					sb.append(", dir=both");
				}
				sb.append("]\n");
			}
		}
		sb.append ("}\n");
		
		return sb.toString();
	}
	
	public String toPlainText () {
		StringBuilder sb = new StringBuilder("\n--- --- --- ---\n");
		int concatTemp = 0;
		for (Edge e: edges) {
			if (e instanceof EdgeCharAt) {
				sb.append("charAt ");
				sb.append(e.getSource());
				sb.append (", ");
				sb.append(e.getDest());
				sb.append (", ");
				sb.append(((EdgeCharAt) e).getIndex());
			}
			else if (e instanceof EdgeConcat) {
				sb.append ("equal ");
				sb.append(e.getSources().get(0));
				sb.append (", ");
				sb.append ("concatTemp" + concatTemp);
				sb.append ("\nequal ");
				sb.append(e.getSources().get(1));
				sb.append (", ");
				sb.append ("concatTemp" + concatTemp);
				sb.append ("\nequal ");
				sb.append("concatTemp" + concatTemp);
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeContains) {
				sb.append ("contains ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeEndsWith) {
				sb.append ("endsWith ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeIndexOf) {
				sb.append ("indexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeIndexOf) e).getIndex());
			}
			else if (e instanceof EdgeIndexOfChar) {
				sb.append ("indexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeIndexOfChar) e).getIndex());
			}
			else if (e instanceof EdgeIndexOf2) {
				sb.append ("indexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeIndexOf2) e).getIndex());
				sb.append (", ");
				sb.append (((EdgeIndexOf2) e).getIndex().getMinIndex());
			}
			else if (e instanceof EdgeIndexOfChar2) {
				sb.append ("lastindexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeIndexOfChar2) e).getIndex());
				sb.append (", ");
				sb.append (((EdgeIndexOfChar2) e).getIndex().getMinDist());
			}
			else if (e instanceof EdgeLastIndexOf) {
				sb.append ("lastindexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeLastIndexOf) e).getIndex());
			}
			else if (e instanceof EdgeLastIndexOfChar) {
				sb.append ("lastindexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeLastIndexOfChar) e).getIndex());
			}
			else if (e instanceof EdgeLastIndexOf2) {
				sb.append ("lastindexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeLastIndexOf2) e).getIndex());
				sb.append (", ");
				sb.append (((EdgeLastIndexOf2) e).getIndex().getMinIndex());
			}
			else if (e instanceof EdgeLastIndexOfChar2) {
				sb.append ("lastindexOf ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				sb.append (((EdgeLastIndexOfChar2) e).getIndex());
				sb.append (", ");
				sb.append (((EdgeLastIndexOfChar2) e).getIndex().getMinDist());
			}
			else if (e instanceof EdgeNotContains) {
				sb.append ("notcontains ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeNotEndsWith) {
				sb.append ("notendsWith ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeNotEqual) {
				sb.append ("notequal ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeNotStartsWith) {
				sb.append ("notstartsWith ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeStartsWith) {
				sb.append ("startsWith ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else if (e instanceof EdgeSubstring1Equal) {
				sb.append ("substring ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				if (((EdgeSubstring1Equal) e).getArgument1Symbolic() == null) {
					sb.append (((EdgeSubstring1Equal) e).getArgument1());
				}
				else {
					sb.append (((EdgeSubstring1Equal) e).getArgument1Symbolic());
				}
			}
			else if (e instanceof EdgeSubstring2Equal) {
				sb.append ("substring ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
				sb.append (", ");
				if (((EdgeSubstring2Equal) e).getSymbolicArgument1() == null) {
					sb.append (((EdgeSubstring2Equal) e).getArgument1());
				}
				else {
					sb.append (((EdgeSubstring2Equal) e).getSymbolicArgument1());
				}
				sb.append (", ");
				if (((EdgeSubstring2Equal) e).getSymbolicArgument2() == null) {
					sb.append (((EdgeSubstring2Equal) e).getArgument2());
				}
				else {
					sb.append (((EdgeSubstring2Equal) e).getSymbolicArgument2());
				}
			}
			else if (e instanceof EdgeTrimEqual) {
				sb.append ("trim ");
				sb.append (e.getSource());
				sb.append (", ");
				sb.append (e.getDest());
			}
			else {
				throw new RuntimeException ("Not recognised: " + e.getClass());
			}
			sb.append("\n");
		}
		sb.append ("\n--- --- --- ---\n");
		return sb.toString();
	}
	
	public List<Edge> getEdges () {
		return edges;
	}
	
	public List<Vertex> getVertices () {
		return vertices;
	}
	
	/**
	 * Returns false if inconsistent
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public boolean mergeVertices (Vertex v1, Vertex v2) { 
		Vertex sticks, dissapears;
		if (v2.isConstant() && v1.isConstant()) {
			if (!v1.solution.equals(v2.solution)) {
				return false;
			}
			renameVertex(v2, v1);
			sticks = v1;
			dissapears = v2;
		}
		else if (v1.isConstant()) {
			renameVertex(v2, v1);
			sticks = v1;
			dissapears = v2;
			v2.setSolution(v1.getSolution());
		}
		else if (v2.isConstant()) {
			renameVertex(v1, v2);
			sticks = v2;
			dissapears = v1;
			v1.setSolution(v2.getSolution());
		}
		else { // All is symbolic
			renameVertex(v2, v1);
			sticks = v1;
			dissapears = v2;
		}
		sticks.addToRepresent(dissapears);
		
		//Merge startswith and endswith
		//TODO: Improve speed
		List<Edge> edgesToAdd = new ArrayList<Edge>();
		for (Edge e1: edges) {
			for (Edge e2: edges) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!(e1.getSource().equals(sticks) && e2.getSource().equals(sticks))) continue;
				if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeStartsWith) {
					//They must be equal
					edgesToAdd.add(new EdgeEqual("EdgeEqual_" + e1.getDest().getName() + "_" + e2.getDest().getName(), e1.getDest(), e2.getDest()));
				}
				else if (e1 instanceof EdgeEndsWith && e2 instanceof EdgeEndsWith) {
					//They must be equal
					edgesToAdd.add(new EdgeEqual("EdgeEqual_" + e1.getDest().getName() + "_" + e2.getDest().getName(), e1.getDest(), e2.getDest()));
				}
			}
		}
		//println ("[mergeVertices] Edges to add: "+ edgesToAdd);
		for (Edge e: edgesToAdd) {
			addEdge(e.getSource(), e.getDest(), e);
		}
		
		for (Vertex v: getVertices()) {
			if (v == null) throw new RuntimeException();
		}
		
		return true;
	}
	
	private void renameVertex (Vertex oldV, Vertex newV) {
		vertices.remove(oldV);
		newV.name = newV.name + " && " + oldV.name;
		for (Edge e: edges) {
			if (e instanceof EdgeConcat) {
				EdgeConcat ec = (EdgeConcat) e;
				if (ec.getSources().get(0).equals(oldV)) {
					ec.setSource(newV, 0);
				}
				if (ec.getSources().get(1).equals(oldV)) {
					ec.setSource(newV, 1);
				}
			}
			else {
				if (e.getSource().equals(oldV)) { 
					e.setSource(newV);
				} 
			}
			
			if (e.getDest().equals(oldV)) {
				e.setDest(newV);
			}
		}
		removeSelfLoops (newV);
		
	}
	
	public void removeSelfLoops (Vertex v) {
		List<Edge> edgesToRemove = new ArrayList<Edge>();
		for (Edge e: edges) {
			if (e instanceof EdgeConcat) {
				//Do nothing, for now
			}
			else if (e.getSource().equals(v) && e.getDest().equals(v)) {
				edgesToRemove.add(e);
			}
		}
		//println ("[removeSelfLoops] Edges to remove: " + edgesToRemove);
		for (Edge e: edgesToRemove) {
			edges.remove(e);
		}
	}
	
	/**
	 * Checks if there are a pair of vertices with a comparator equals and not equals between them
	 * @return
	 */
	public boolean inconsistent () {
		for (Vertex v1: vertices) {
			for (Vertex v2: vertices) {
				if (edges.contains(new EdgeEqual("", v1, v2)) &&
					edges.contains(new EdgeNotEqual("", v1, v2))) {
					//println ("[inconsistent] Between " + v1.getName() + " and " + v2.getName() + " there's a inconsitency");
					//println ("[inconsistent] " + this.toString());
					return true;
				}
			}
		}
		return false;
	}
	
	
	public Vertex findVertex (String name) {
		for (Vertex v: getVertices()) {
			if (v.getName().equals(name)) {
				return v;
			}
		}
		return null;
	}
	
	private static void println (String msg) {
		System.out.println("[StringGraph] " + msg);
	}
	
	public List<Vertex> getNeighbours (Vertex v) {
		List<Vertex> result = new ArrayList<Vertex>();
		for (Edge e: this.getEdges()) {
			if (e instanceof EdgeConcat) {
				if (e.getSources().get(0).equals(v)) {
					if (!result.contains(e.getDest())) result.add(e.getDest());
					if (!result.contains(e.getSources().get(1))) result.add(e.getSources().get(1));					
				}
				if (e.getSources().get(1).equals(v)) {
					if (!result.contains(e.getDest())) result.add(e.getDest());
					if (!result.contains(e.getSources().get(0))) result.add(e.getSources().get(0));					
				}
				if (e.getDest().equals(v)) {
					if (!result.contains(e.getSources().get(0))) result.add(e.getSources().get(0));										
					if (!result.contains(e.getSources().get(1))) result.add(e.getSources().get(1));										
				}
			}
			else {
				if (e.getSource().equals(v)) {
					if (!result.contains(e.getDest())) result.add(e.getDest());
				}
				else if (e.getDest().equals(v)) {
					if (!result.contains(e.getSource())) result.add(e.getSource());
				}
			}
		}
		return result;
	}
	
	/*private static Edge cloneAndSwapVertices(Edge e, Map<Vertex, Vertex> oldToNew) {
		Edge newEdge;
		
		//possible edges
		if (e instanceof EdgeCharAt) {
			
		} else if (e instanceof EdgeConcat) {
			
		} else if (e instanceof EdgeContains) {
			
		} else if (e instanceof EdgeEndsWith) {
			
		} else if (e instanceof EdgeEqual) {
			
		} else if (e instanceof EdgeIndexOf) {
			
		} else if (e instanceof EdgeIndexOf2) {
			
		} else if (e instanceof EdgeIndexOfChar) {
			
		} else if (e instanceof EdgeIndexOfChar2) {
			
		} else if (e instanceof EdgeLastIndexOf) {
			
		} else if (e instanceof EdgeLastIndexOf2) {
			
		} else if (e instanceof EdgeLastIndexOfChar) {
			
		} else if (e instanceof EdgeLastIndexOfChar2) {
			
		} else if (e instanceof EdgeNoCharAt) {
			
		} else if (e instanceof EdgeNotCharAt) {
			
		} else if (e instanceof EdgeNotContains) {
			
		} else if (e instanceof EdgeNotEndsWith) {
			
		} else if (e instanceof EdgeNotEqual) {
			
		} else if (e instanceof EdgeReplaceCharChar) {
			
		} else if (e instanceof EdgeStartsWith) {
			
		} else if (e instanceof EdgeSubstring1Equal) {
			
		} else if (e instanceof EdgeSubstring2Equal) {
			
		} else if (e instanceof EdgeTrimEqual) {
			
		} else {
			throw new UnsupportedOperationException("missing case:" + e.getClass());
		}
	}*/
}
