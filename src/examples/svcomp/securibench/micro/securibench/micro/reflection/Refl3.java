// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

/*
   @author Benjamin Livshits <livshits@cs.stanford.edu>

   $Id: Refl3.java,v 1.6 2006/04/04 20:00:40 livshits Exp $
*/
package svcomp.securibench.micro.securibench.micro.reflection;

import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.BasicTestCase;
import svcomp.securibench.micro.securibench.micro.MicroTestCase;

import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Field;

/**
 * @servlet description = "reflectively create a class and access its field"
 * @servlet vuln_count = "1"
 */
public class Refl3 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";
  private String name;

  public static class ReflectivelyCreated {
    public String value;
  }

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    name = req.getParameter(FIELD_NAME);
    PrintWriter writer = resp.getWriter();

    try {
      Class clazz = Class.forName("svcomp.securibench.micro.securibench.micro.reflection.Refl3$ReflectivelyCreated");
      ReflectivelyCreated rc = (ReflectivelyCreated) clazz.newInstance();
      Field field = clazz.getField("value");
      field.set(rc, name);

      writer.println(rc.value); /* BAD */
    } catch (ClassNotFoundException e) {
      System.err.println("An error occurred (1)");
    } catch (InstantiationException e) {
      System.err.println("An error occurred (2)");
    } catch (IllegalAccessException e) {
      System.err.println("An error occurred (3)");
    } catch (SecurityException e) {
      System.err.println("An error occurred (4)");
    } catch (NoSuchFieldException e) {
      System.err.println("An error occurred (5)");
    }
  }

  public String getDescription() {
    return "reflectively create a class and access its field";
  }

  public int getVulnerabilityCount() {
    return 1;
  }
}
