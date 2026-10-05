// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: Contributed by Falk Howar
// SPDX-FileCopyrightText: 2025 The SV-Benchmarks Community
//
// SPDX-License-Identifier: Apache-2.0

package svcomp.common.org.sosy_lab.sv_benchmarks;

public interface ObjectFactory<T> {
  T createObject();
}
