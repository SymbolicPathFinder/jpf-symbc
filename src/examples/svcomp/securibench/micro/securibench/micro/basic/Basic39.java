// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
/**
 * @author Benjamin Livshits <livshits@cs.stanford.edu>
 *     <p>$Id: Basic39.java,v 1.2 2006/04/04 20:00:40 livshits Exp $
 */
package svcomp.securibench.micro.securibench.micro.basic;

import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.BasicTestCase;
import svcomp.securibench.micro.securibench.micro.MicroTestCase;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.StringTokenizer;

/**
 * @servlet description="StringTokenizer test"
 * @servlet vuln_count = "1"
 */
public class Basic39 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    String name = req.getParameter(FIELD_NAME);
    StringTokenizer tok = new StringTokenizer(name, "\t");
    while (tok.hasMoreElements()) {
      PrintWriter writer = resp.getWriter();
      writer.println(tok.nextElement()); /* BAD */
    }
  }

  public String getDescription() {
    return "StringTokenizer test";
  }

  public int getVulnerabilityCount() {
    return 1;
  }
}
