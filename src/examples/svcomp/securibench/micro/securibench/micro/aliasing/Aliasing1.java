// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

/*
   @author Benjamin Livshits <livshits@cs.stanford.edu>

   $Id: Aliasing1.java,v 1.1 2006/04/21 17:14:27 livshits Exp $
*/
package svcomp.securibench.micro.securibench.micro.aliasing;

import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.BasicTestCase;
import svcomp.securibench.micro.securibench.micro.MicroTestCase;

import java.io.IOException;
import java.io.PrintWriter;

/**
 * @servlet description="simple aliasing because of assignment"
 * @servlet vuln_count = "1"
 */
public class Aliasing1 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    String name = req.getParameter(FIELD_NAME);
    String str = name;

    PrintWriter writer = resp.getWriter();
    writer.println(str); /* BAD */
  }

  public String getDescription() {
    return "simple test of field assignment";
  }

  public int getVulnerabilityCount() {
    return 1;
  }
}
