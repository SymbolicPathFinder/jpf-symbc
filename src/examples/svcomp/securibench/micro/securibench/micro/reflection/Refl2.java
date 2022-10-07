// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

/*
   @author Benjamin Livshits <livshits@cs.stanford.edu>

   $Id: Refl2.java,v 1.6 2006/04/04 20:00:41 livshits Exp $
*/
package svcomp.securibench.micro.securibench.micro.reflection;

import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Field;
// import javax.servlet.ServletResponse;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.BasicTestCase;
import svcomp.securibench.micro.securibench.micro.MicroTestCase;

/**
 * @servlet description="reflectively access a field"
 * @servlet vuln_count = "1"
 */
public class Refl2 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";
  public String name;

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    name = req.getParameter(FIELD_NAME);

    try {
      f(resp);
    } catch (Exception e) {
      System.err.println("An error occurred");
    }
  }

  public void f(HttpServletResponse resp)
          throws IOException, SecurityException, NoSuchFieldException, ClassNotFoundException,
          IllegalArgumentException, IllegalAccessException {
    PrintWriter writer = resp.getWriter();
    Field field = Class.forName("svcomp.securibench.micro.securibench.micro.reflection.Refl2").getField("name");
    String myName = (String) field.get(this);
    writer.println(myName); /* BAD */
  }

  public String getDescription() {
    return "reflectively access a field";
  }

  public int getVulnerabilityCount() {
    return 1;
  }
}
