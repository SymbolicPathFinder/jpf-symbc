/*
 * Contributed to SV-COMP by Marvin Lazar and Falk Howar
 * License: MIT (see /java/objects/LICENSE-MIT)
 *
 * SPDX-FileCopyrightText: 2025 Marvin Lazar and Falk Howar, TU Dortmund University
 * SPDX-FileCopyrightText: 2025 The SV-Benchmarks Community
 * SPDX-License-Identifier: MIT
 */

package svcomp.objects.classes.svcomp.objects;

//import svcomp.objects.Any;
//import svcomp.objects.Sub;

public class A extends Any {

  private int x;
  private int y;
  private Sub sub;

  public A() {}

  public A(int x) {
    this.x = x;
  }

  public A(int x, int y) {
    this.x = x;
    this.y = y;
  }

  public A(int x, int y, Sub sub) {
    this.x = x;
    this.y = y;
    this.sub = sub;
  }

  public Sub getSub() {
    return sub;
  }

  public int getX() {
    return this.x;
  }

  public void setX(int x) {
    this.x = x;
  }

  public int getY() {
    return this.y;
  }

  public void setY(int y) {
    this.y = y;
  }

  public void foo() {
    System.out.println("A correctly executed method foo()");
  }
}
