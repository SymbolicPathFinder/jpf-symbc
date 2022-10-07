// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
/**
 * @author Benjamin Livshits <livshits@cs.stanford.edu>
 *     <p>$Id: Basic38.java,v 1.2 2006/04/04 20:00:40 livshits Exp $
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
 * @servlet description="StringTokenizer test with a false positive"
 * @servlet vuln_count = "1"
 */
public class Basic38 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    String name = req.getParameter(FIELD_NAME);
    StringTokenizer tok1 = new StringTokenizer(name, "\t");
    StringTokenizer tok2 = new StringTokenizer("abc\tdef", "\t");

    while (tok1.hasMoreTokens() && tok2.hasMoreElements()) {
      PrintWriter writer = resp.getWriter();
      writer.println(tok1.nextToken()); /* BAD */
      writer.println(tok2.nextToken()); /* OK */
    }
  }

  public String getDescription() {
    return "StringTokenizer test with a false positive";
  }

  public int getVulnerabilityCount() {
    return 1;
  }
}
