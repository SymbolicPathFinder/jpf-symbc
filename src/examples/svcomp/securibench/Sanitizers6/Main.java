package svcomp.securibench.Sanitizers6;// SPDX-FileCopyrightText: 2021 Falk Howar falk.howar@tu-dortmund.de
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

import java.io.IOException;
import org.sosy_lab.sv_benchmarks.Verifier;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletRequest;
import svcomp.securibench.micro.mockx.servlet.http.HttpServletResponse;
import svcomp.securibench.micro.securibench.micro.sanitizers.Sanitizers6;

import static svcomp.securibench.micro.securibench.micro.sanitizers.Sanitizers6.clean;

public class Main {

//  public static void main(String[] args) {
//    String s1 = Verifier.nondetString();
//    HttpServletRequest req = new HttpServletRequest();
//    HttpServletResponse res = new HttpServletResponse();
//    req.setTaintedValue(s1);
//
//    Sanitizers6 sut = new Sanitizers6();
//    try {
//      sut.doGet(req, res);
//    } catch (IOException e) {
//
//    }
//  }

  public static void main(String[] args) {
    String s1 = Verifier.nondetString();
    StringBuffer buf = new StringBuffer();
    for (int i = 0; i < s1.length(); i++) {
      char ch = s1.charAt(i);

      if (Character.isLetter(ch) || Character.isDigit(ch) || ch == '_') {
        buf.append(ch);
      } else {
        buf.append('?');
      }
    }

    String s = buf.toString();
    if (s.contains("<bad/>")) {
      assert false;
    }
  }
}
