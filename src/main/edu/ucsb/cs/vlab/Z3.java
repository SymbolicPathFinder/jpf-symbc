package edu.ucsb.cs.vlab;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Properties;
import java.util.Random;

import edu.ucsb.cs.vlab.Z3Interface.Processor;

public class Z3 {
	private static final Properties PROPERTIES;

	static {
		PROPERTIES = new Properties();
		try (final FileInputStream in = new FileInputStream(System.getProperty("user.home") + "/.jpf/site.properties")) {
			PROPERTIES.load(in);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static Properties getProperties() {
		return PROPERTIES;
	}

	public static String getBinary() {
		return getProperties().getProperty("strings.z3", "./lib/z3");
	}

	public static String getInteractive() {
		return getBinary() + " " + getProperties().getProperty("strings.interactive_flags", " -smt2 -in");
	}

	public static boolean saveTempFileAfterRun() {
		return getProperties().getProperty("strings.keep_temp", "no").equalsIgnoreCase("yes");
	}
	
	public static Processor create() {
		return Z3Interface.create();
	}

	public static final int random = new Random(System.currentTimeMillis()).nextInt();

	public static String getTempFile() {
		return "./temp.z3str";
	}
}
