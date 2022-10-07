// SPDX-FileCopyrightText: 2021 Falk Howar falk.howar@tu-dortmund.de
// SPDX-License-Identifier: Apache-2.0

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks

package svcomp.securibench.micro.mock.sql;

public class Statement {

  public void execute(String s) throws SQLException {
    if (s.contains("<bad/>")) {
      assert false;
    }
  }

  public void executeUpdate(String s, Object... o) throws SQLException {
    if (s.contains("<bad/>")) {
      assert false;
    }
  }

  public void executeQuery(String s) {
    if (s.contains("<bad/>")) {
      assert false;
    }
  }
}
