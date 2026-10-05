package svcomp.objects.objects01;/*
 * Contributed to SV-COMP by Marvin Lazar and Falk Howar
 * License: MIT (see /java/objects/LICENSE-MIT)
 *
 * SPDX-FileCopyrightText: 2025 Marvin Lazar and Falk Howar, TU Dortmund University
 * SPDX-FileCopyrightText: 2025 The SV-Benchmarks Community
 * SPDX-License-Identifier: MIT
 */

import org.sosy_lab.sv_benchmarks.Verifier;
import svcomp.objects.*;
import svcomp.objects.classes.svcomp.objects.A;
import svcomp.objects.classes.svcomp.objects.Factories;

public class Main {

  public static void main(String[] args) {
    A a = Verifier.nondetObject(A.class, new Factories.AFactory());
    // NPE reachable
    a.getX();
  }
}
