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

package gov.nasa.jpf.symbc.abstraction;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

// OSM stands for Object State Machine
// OSM is a directed graph


/**
 * 
 * represents a vertex in the OSM graph
 *
 */
class Vertex{
	public String label;
	public Vertex(String _label){
		label = _label;
	}
}

/**
 * 
 * represents an edge in the OSM graph
 */
class Edge{
	public Vertex beginVertex;
	public Vertex endVertex;
	public String label;
	public String pc; // path-condition at the time when the edge is first created
	public Edge(Vertex _beginVertex, Vertex _endVertex, String _label, String _pc){
		beginVertex = _beginVertex;
		endVertex = _endVertex;
		label = _label;
		pc = _pc;
	}
}

/**
 * 
 * @author Mithun Acharya
 * Singleton class used to hold the Object State Machine (OSM)
 * 
 * Manages the OSM graph and the associated .dot file. 
 * 
 * there are 2 graphs and 2 .dot files
 * one at method granularity
 * and the other at sequence granularity
 * 
 * KNOWN PROBLEMS
 * 
 * None. 
 * 
 * 
 * TODO: Refactor
 * Make OSM base class and derive OSM_sequence and OSM_method
 * separately. 
 * Currently, everything is under one OSM class!
 * Better, it might be useful to derive OSM itself from a graph library
 * such as JGraphT http://jgrapht.sourceforge.net/ as some inference algorithms might use graph algorithms
 * but the problem is dependency of JPF on JGraphT. 
 *
 */
public class OSM {
	
	// singleton instance
	private static OSM _instance = null;
	
	// OSM at method granularity
	// graph related
	// to hold the adjacency list
	private static HashMap<Vertex, LinkedList<Vertex>> adjacencyMap_method;
	// holds all the vertices separately
	private static HashSet<Vertex> vertices_method;
	// holds all the edges separately
	private static HashSet<Edge> edges_method;	
	private static String initialState_method = null;
	// last recorded state (represented as a String sequence)
	private static String lastRecordedState_method = null;
	private static String newState_method = null;	
	// OSM DOT FILE RELATED (for visualization)
	private static BufferedWriter bufferedWriter_method;
	private static FileWriter fileWriter_method;
	// Use graphviz (http://www.graphviz.org/) to open the .dot file
	private static final String dotFile_method = "osm_method.dot";
	
	// OSM at sequence granularity
	// to hold the adjacency list
	private static HashMap<Vertex, LinkedList<Vertex>> adjacencyMap_sequence;
	// holds all the vertices separately
	private static HashSet<Vertex> vertices_sequence;
	// holds all the edges separately
	private static HashSet<Edge> edges_sequence;
	private static String initialState_sequence = null;
	// last recorded state (represented as a String sequence)
	private static String lastRecordedState_sequence = null;
	// OSM DOT FILE RELATED (for visualization)
	private static BufferedWriter bufferedWriter_sequence;
	private static FileWriter fileWriter_sequence;
	// Use graphviz (http://www.graphviz.org/) to open the .dot file
	private static final String dotFile_sequence = "osm_sequence.dot";
	
	
	/**
	 * private constructor
	 */
	private OSM(){
		//--method granularity
		adjacencyMap_method = new HashMap<Vertex, LinkedList<Vertex>>();
		vertices_method = new HashSet<Vertex>();
		edges_method = new HashSet<Edge>();
		try{
			fileWriter_method = new FileWriter(dotFile_method);
			bufferedWriter_method = new BufferedWriter(fileWriter_method);
		}catch(IOException e){System.out.println(e);}
		
		//--sequence granularity
		adjacencyMap_sequence = new HashMap<Vertex, LinkedList<Vertex>>();
		vertices_sequence = new HashSet<Vertex>();
		edges_sequence = new HashSet<Edge>();
		try{
			fileWriter_sequence = new FileWriter(dotFile_sequence);
			bufferedWriter_sequence = new BufferedWriter(fileWriter_sequence);
		}catch(IOException e){System.out.println(e);}
		
	}
	
	/**
	 * 
	 * returns the singleton instance
	 */
	public static OSM getSingletonOSMInstance(){
		if (_instance == null)
			_instance = new OSM();
		return _instance;
	}
	
	
	// ------------------------------------------------------- 
	// methods to manipulate/query the OSM graph
	// -------------------------------------------------------
	
	/**
	 * returns number of vertices 
	 */
	public int numVertices_method(){
		return vertices_method.size();
	}
	
	/**
	 * returns number of vertices 
	 */
	public int numVertices_sequence(){
		return vertices_sequence.size();
	}
	
	
	/**
	 * return number of edges
	 */
	public static int numEdges_method(){
		return edges_method.size();
	}
	
	/**
	 * return number of edges
	 */
	public static int numEdges_sequence(){
		return edges_sequence.size();
	}
	
	
	/**
	 * add vertex. returns true if vertex is new. 
	 */
	public boolean addVertex_method(Vertex vertex){
		if(adjacencyMap_method.containsKey(vertex))
			return false;
		adjacencyMap_method.put(vertex, new LinkedList<Vertex>());
		vertices_method.add(vertex);
		return true;
	}
	
	/**
	 * add vertex. returns true if vertex is new. 
	 */
	public boolean addVertex_sequence(Vertex vertex){
		if(adjacencyMap_sequence.containsKey(vertex))
			return false;
		adjacencyMap_sequence.put(vertex, new LinkedList<Vertex>());
		vertices_sequence.add(vertex);
		return true;
	}
	
	
	/**
	 * 
	 * add edge
	 */
	public boolean addEdge_method(Edge edge){
		if (edge == null) 
			return false;
		// add only if not previously added
		if(!containsEdge_method(edge)){
			// first add vertices
			addVertex_method(edge.beginVertex); 
			addVertex_method(edge.endVertex);
			LinkedList<Vertex> l = (LinkedList<Vertex>)adjacencyMap_method.get(edge.beginVertex);
			l.add(edge.endVertex);
			edges_method.add(edge);
			return true;
		}
		return false;
	}
	
	
	/**
	 * 
	 * add edge
	 */
	public boolean addEdge_sequence(Edge edge){
		if (edge == null) 
			return false;
		// add only if not previously added
		if(!containsEdge_sequence(edge)){
			// first add vertices
			addVertex_sequence(edge.beginVertex); 
			addVertex_sequence(edge.endVertex);
			LinkedList<Vertex> l = (LinkedList<Vertex>)adjacencyMap_sequence.get(edge.beginVertex);
			l.add(edge.endVertex);
			edges_sequence.add(edge);
			return true;
		}
		return false;
	}
	
	/**
	 * 
	 * 
	 */
	public void setInitialState_method(String state){
		initialState_method = state;
		// also update the last recorded state
		setLastRecordedState_method(initialState_method);
	}
	
	
	/**
	 * 
	 * 
	 */
	public void setInitialState_sequence(String state){
		initialState_sequence = state;
		// also update the last recorded state
		setLastRecordedState_sequence(initialState_sequence);
	}
	
	
	
	/**
	 * 
	 * 
	 */
	public void setLastRecordedState_method(String state){
		lastRecordedState_method = state; 
	}
	
	
	/**
	 * 
	 * 
	 */
	public void setLastRecordedState_sequence(String state){
		lastRecordedState_sequence = state; 
	}
	

	
	/**
	 * Updates the graph and dot file for the method part. 
	 * 
	 * edge is drawn between the last recorded state and the new state. 
	 * 
	 */
	public void update_method(String state, String lastInvokedMethod, String pc, boolean APPENDPC){
		// update the new state
		newState_method = state;
		// construct the vertices for the new edge
		Vertex beginVertex = new Vertex(lastRecordedState_method);
		Vertex endVertex = new Vertex(newState_method);
		// create the edge
		Edge edge = new Edge(beginVertex, endVertex, lastInvokedMethod, pc);
		// Add edge to the OSM graph, if not present
		if (!containsEdge_method(edge)){
			addEdge_method(edge);
			// Do some printing
			String temp = lastRecordedState_method + "--" + lastInvokedMethod + "-->" + newState_method;
			System.out.println(temp);
			// Update the dot file
			String dotFileString = null;
			if (APPENDPC){
				// with PC appended
				dotFileString = "\"" + lastRecordedState_method + "\"" + "  -> " + "\"" + newState_method + "\"" + " [label=\"" + lastInvokedMethod + " {" + pc + "} " + "\"];";
			}
			else{
				// without PC
				dotFileString = "\"" + lastRecordedState_method + "\"" + "  -> " + "\"" + newState_method + "\"" + " [label=\"" + lastInvokedMethod + "\"];";
			}
			
			
			writeDot_method(dotFileString);
		}
	}
	
	
	/**
	 * Updates the graph and dot file for the sequence part. 
	 * the new edge is always between initialState_sequence and the lastRecordedState_sequence
	 */
	public void update_sequence(String lastInvokedSequence, String pc, boolean APPENDPC){
		// construct the vertices for the new edge
		Vertex beginVertex = new Vertex(initialState_sequence);
		Vertex endVertex = new Vertex(lastRecordedState_sequence);
		// create the edge
		Edge edge = new Edge(beginVertex, endVertex, lastInvokedSequence, pc);
		// Add edge to the OSM graph, if not present
		if (!containsEdge_sequence(edge)){
			addEdge_sequence(edge);
			// Do some printing
			String temp = initialState_sequence + "--" + lastInvokedSequence + "-->" + lastRecordedState_sequence;
			System.out.println(temp);
			// Update the dot file
			String dotFileString = null;
			if(APPENDPC){
				// with PC appended
				dotFileString = "\"" + initialState_sequence + "\"" + "  -> " + "\"" + lastRecordedState_sequence + "\"" + " [label=\"" + lastInvokedSequence + " {" + pc + "} " +"\"];";
			}
			else {
				// without PC
				dotFileString = "\"" + initialState_sequence + "\"" + "  -> " + "\"" + lastRecordedState_sequence + "\"" + " [label=\"" + lastInvokedSequence + "\"];";
			}
			writeDot_sequence(dotFileString);
		}
	}
	
	
	
	/**
	 * 
	 */
	public boolean containsVertex_method(Vertex vertex){
		return vertices_method.contains(vertex);
	}
	
	
	/**
	 * 
	 */
	public boolean containsVertex_sequence(Vertex vertex){
		return vertices_sequence.contains(vertex);
	}
	
	
	/**
	 * 
	 */
	public boolean containsEdge_method(Edge edge){
		return edges_method.contains(edge);
	}
	
	
	/**
	 * 
	 */
	public boolean containsEdge_sequence(Edge edge){
		return edges_sequence.contains(edge);
	}
	
	
	// ------------------------------------------------------- 
	// methods to manipulate the .dot file of the OSM graph
	// -------------------------------------------------------
	
	
	/**
	 * start writing into the dot file
	 */
	public void beginDot_method(){
		try{
			bufferedWriter_method.write("digraph osm_method");
			bufferedWriter_method.newLine();
			bufferedWriter_method.write("{");
			bufferedWriter_method.newLine();
		}catch(IOException e){System.out.println(e);}
	}
	
	/**
	 * start writing into the dot file
	 */
	public void beginDot_sequence(){
		try{
			bufferedWriter_sequence.write("digraph osm_sequence");
			bufferedWriter_sequence.newLine();
			bufferedWriter_sequence.write("{");
			bufferedWriter_sequence.newLine();
		}catch(IOException e){System.out.println(e);}
	}
	
	
	/**
	 * end the dot file and close it
	 */
	public void endDot_method(){
		try{
			bufferedWriter_method.write("}");
			bufferedWriter_method.newLine();
			bufferedWriter_method.close();
			fileWriter_method.close();
		}catch(IOException e){System.out.println(e);}
	}
	
	
	/**
	 * end the dot file and close it
	 */
	public void endDot_sequence(){
		try{
			bufferedWriter_sequence.write("}");
			bufferedWriter_sequence.newLine();
			bufferedWriter_sequence.close();
			fileWriter_sequence.close();
		}catch(IOException e){System.out.println(e);}
	}
	

	
	/**
	 * 
	 * Write a String into the dot file
	 */
	public void writeDot_method(String s){
		try{
			bufferedWriter_method.write(s);
			bufferedWriter_method.newLine();
		}catch(IOException e){System.out.println(e);}
	}
	
	
	/**
	 * 
	 * Write a String into the dot file
	 */
	public void writeDot_sequence(String s){
		try{
			bufferedWriter_sequence.write(s);
			bufferedWriter_sequence.newLine();
		}catch(IOException e){System.out.println(e);}
	}
		
}
