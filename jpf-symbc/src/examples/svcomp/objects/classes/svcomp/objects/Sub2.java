/*
 * Contributed to SV-COMP by Marvin Lazar and Falk Howar
 * License: MIT (see /java/objects/LICENSE-MIT)
 *
 * SPDX-FileCopyrightText: 2025 Marvin Lazar and Falk Howar, TU Dortmund University
 * SPDX-FileCopyrightText: 2025 The SV-Benchmarks Community
 * SPDX-License-Identifier: MIT
 */

package svcomp.objects.classes.svcomp.objects;

public class Sub2 extends Sub {

  private int z;

  public Sub2(int z) {
    this.z = z;
  }

  public Sub2() {}

  public int getZ() {
    return z;
  }

  @Override
  public void bar() {
    assert false : "Error in Sub2.bar()";
  }
}
