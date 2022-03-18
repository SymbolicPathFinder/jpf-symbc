// SPDX-FileCopyrightText: 2006 Benjamin Livshits livshits@cs.stanford.edu
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

/*
   @author Benjamin Livshits <livshits@cs.stanford.edu>

   $Id: Sanitizers2.java,v 1.7 2006/04/04 20:00:41 livshits Exp $
*/
package svcomp.securibench.micro.securibench.micro.sanitizers;

import java.io.IOException;
import java.io.PrintWriter;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.BasicTestCase;
import svcomp.securibench.micro.securibench.micro.MicroTestCase;

/**
 * @servlet description="simple sanitization check"
 * @servlet vuln_count = "0"
 */
public class Sanitizers2 extends BasicTestCase implements MicroTestCase {
  private static final String FIELD_NAME = "name";
  private PrintWriter writer;

  public void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
    String name = req.getParameter(FIELD_NAME);
    String clean = clean(name);

    writer = resp.getWriter();
    resp.setContentType("text/html");

    writer.println("<html>" + clean + "</html>"); /* OK */
  }

  /** @sanitizer javascript sanitization routine */
  private String clean(String name) {
    StringBuffer buf = new StringBuffer();
    for (int i = 0; i < name.length(); i++) {
      char ch = name.charAt(i);
      switch (ch) {
        case '<':
          buf.append("&lt;");
          break;
        case '>':
          buf.append("&gt;");
          break;
        case '&':
          buf.append("&amp;");
          break;
        default:
          if (Character.isLetter(ch) || Character.isDigit(ch) || ch == '_') {
            buf.append(ch);
          } else {
            buf.append('?');
          }
      }
    }

    return buf.toString();
  }

  public String getDescription() {
    return "simple sanitization check";
  }

  public int getVulnerabilityCount() {
    return 0;
  }
}
