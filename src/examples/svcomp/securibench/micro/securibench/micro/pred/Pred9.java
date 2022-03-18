// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

/**
 * @author Benjamin Livshits <livshits@cs.stanford.edu>
 *     <p>$Id: Pred9.java,v 1.3 2006/04/04 20:00:40 livshits Exp $
 *     <p>// changed verdict: in SVCOMP mock this is ok
 */
package svcomp.securibench.micro.securibench.micro.pred;

import java.io.IOException;
import java.io.PrintWriter;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.BasicTestCase;
import svcomp.securibench.micro.securibench.micro.MicroTestCase;

/**
 * @servlet description="using an array element as in a predicate"
 * @servlet vuln_count = "0"
 */
public class Pred9 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    String name = req.getParameter(FIELD_NAME);
    String array[] = new String[] {name, "abc"};

    if (array[1].equals(name)) {
      PrintWriter writer = resp.getWriter();
      writer.println(name); /* BAD */ // could be equal
    }
  }

  public String getDescription() {
    return "using an array element as in a predicate";
  }

  public int getVulnerabilityCount() {
    return 0;
  }
}
