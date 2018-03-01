package edu.ucsb.cs.vlab.versions;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Paths;

import edu.ucsb.cs.vlab.Z3;
import edu.ucsb.cs.vlab.Z3Interface.ExternalToolException;
import edu.ucsb.cs.vlab.Z3Interface.Processable;
import edu.ucsb.cs.vlab.Z3Interface.Processor;
import edu.ucsb.cs.vlab.modelling.Output;
import edu.ucsb.cs.vlab.modelling.Output.Model;

public class Z3StringProcessor implements Processable {
	final Model model = new Model();
	final StringBuilder currentQuery = new StringBuilder();

	@Override
	public void send(String message, Processor proc) throws IOException {
		currentQuery.append(message + "\n");
	}

	@Override
	public void query(String message, Processor proc) throws IOException {
		currentQuery.append(message + "\n");

		Files.write(Paths.get(Z3.getTempFile()), currentQuery.toString().getBytes());
	}

	@Override
	public Output getOutput(Processor proc) throws IOException, RuntimeException, NullPointerException {
		boolean sat = false; 

		final Process process = proc.startProcess();
		try (final BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
			String line = reader.readLine();

			if (!line.startsWith("*")) {
				throw new ExternalToolException(line);
			}

			reader.readLine();

			line = reader.readLine();
			sat = line.replace(">> ", "").trim().equalsIgnoreCase("SAT");
			reader.readLine();

			if (sat) {
				while (!(line = reader.readLine()).startsWith("*")) {
					process(line);
				}
			}
		}

		return new Output(sat, assembleModel());
	}

	public void process(String line) {
		final String[] parts = line.split(" -> ");
		final String[] typeAndName = parts[0].split(" : ");

		final String name = typeAndName[0].trim();
		final String type = typeAndName[1].trim();
		final String value = parts[1].trim();

		model.put(name, value);
	}

	public Model assembleModel() {
		return model;
	}

}
