package edu.ucsb.cs.vlab;
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

import java.io.Closeable;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import edu.ucsb.cs.vlab.modelling.Output;
import edu.ucsb.cs.vlab.modelling.Output.Model;
import edu.ucsb.cs.vlab.versions.Z3StringProcessor;

public class Z3Interface {
	/**
	 * A lazily evaluated process envelope used as a lambda later on.
	 * 
	 * @author miroslav
	 *
	 */
	public interface ProcessLambda {
		Process getProcess() throws IOException;
	}

	/**
	 * A processable interface which different versions of Z3 shouild inherit.
	 * 
	 * @author miroslav
	 *
	 */
	public static interface Processable {
		/**
		 * Sends a message. Nothing else.
		 * 
		 * @param message
		 *            String the message to be sent
		 * @return nothing
		 */
		void send(String message, Processor proc) throws IOException;

		/**
		 * Sends a message and exits.
		 * 
		 * @param message
		 *            String the message to be sent
		 * @return nothing
		 */
		void query(final String message, Processor proc) throws IOException;

		/**
		 * Gets the output from the processor
		 * 
		 * @param proc
		 *            Processor the processor to read and parse
		 * @return some form of output -- a structure and a flag saying whether
		 *         the result is satisfiable
		 */
		Output getOutput(Processor proc) throws IOException;

		/**
		 * Processes one or multiple lines of input
		 * 
		 * @param line
		 *            the string passed from the processor
		 */
		void process(String line);

		/**
		 * Assembles the model from the processed input
		 * 
		 * @return a model corresponding to the processed data
		 */
		Model assembleModel();
	}

	/**
	 * A processor of Z3-string output.
	 * 
	 * @author miroslav
	 *
	 */
	public static class Processor implements Closeable {
		public static class Factory {
			public static <Kind extends Processable> Processor create(Class<Kind> processableClass) {
				try {
					final Kind processableInstance = processableClass.newInstance();
					final ProcessLambda process = () -> Runtime.getRuntime().exec(Z3.getInteractive());
					return new Processor(processableInstance, process);
				} catch (InstantiationException | IllegalAccessException e) {
					e.printStackTrace();
					return null;
				}
			}
		}

		private final Processable processable;
		private final ProcessLambda process;

		private Process startedProcess = null;

		public Process startProcess() throws IOException {
			if (startedProcess == null)
				startedProcess = process.getProcess();

			return startedProcess;
		}

		/**
		 * Construct processor capable of working with any process and any kind
		 * of Z3 solver
		 * 
		 * @param processable
		 *            the solver process/parser/reader/writer
		 * @param process
		 *            the literal process from which to pick input and output
		 */
		public <Kind extends Processable> Processor(final Kind processable, final ProcessLambda process) {
			this.processable = processable;
			this.process = process;
		}

		@Override
		public void close() throws IOException {
			if (startedProcess != null) {
				startedProcess.destroy();
			}

			if (!Z3.saveTempFileAfterRun())
				Files.deleteIfExists(Paths.get(Z3.getTempFile()));
		}

		/**
		 * A non-ending send message to processable
		 * 
		 * @param message
		 *            String the message being sent
		 * @return self
		 * @throws IOException
		 */
		public Processor send(String message) throws IOException {
			processable.send(message, this);
			return this;
		}

		/**
		 * An ending send message to processable
		 * 
		 * @param message
		 *            String the message being sent
		 * @return self
		 * @throws IOException
		 */
		public Processor query(String message) throws IOException {
			processable.query(message, this);
			return this;
		}

		public Output read() throws IOException, RuntimeException {
			return processable.getOutput(this);
		}

		public Output finish(String message) throws IOException, RuntimeException {
			processable.query(message, this);
			return processable.getOutput(this);
		}
	}

	/**
	 * Creates a processor for the current Z3 implementation.
	 * 
	 * @return the processor to use
	 */
	public static Z3Interface.Processor create() {
		return Z3Interface.Processor.Factory.create(Z3StringProcessor.class);
	}

	public static class ExternalToolException extends RuntimeException {
		public ExternalToolException(String message) {
			super(message);
		}
	}
}
