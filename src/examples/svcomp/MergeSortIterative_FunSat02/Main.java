
package svcomp.MergeSortIterative_FunSat02;


import org.sosy_lab.sv_benchmarks.Verifier;

/**
 * Type : Functional Safety Expected Verdict : True Last modified by : Zafer Esen
 * <zafer.esen@it.uu.se> Date : 11 November 2019
 *
 * <p>This benchmark is just like IterativeMergeSort-FunSat01, but with a stronger sortedness
 * assertion.
 *
 * <p>Permission to freely use and modify the file granted via e-mail on 26.10.2019 by the original
 * author David Kosbie <koz@cmu.edu>.
 */

// IterativeMergeSort.java
// By David Kosbie

// To see iterative mergesort in action, check out the (really great!) xSortLab:
//   http://math.hws.edu/TMCM/java/xSortLab/
// Select "mergesort" and step through the algorithm visually.  Neat!

// How it works:  on the first pass, we merge a[0] and a[1], then we merge
// a[2] and a[3], and so on.  So the array of n elements contains n/2 sorted
// subarrays of size 2.  On the second pass, we merge a[0]-a[3], a[4]-a[7],
// and so on, so the array of n elements contains n/4 sorted subarrays of size
// 4.  We keep doubling our "blockSize" until it reaches n, and we're done.

public class Main {

  public static void main(String[] args) {
    final int N = Verifier.nondetInt();

    Verifier.assume(N > 0);

    int data[] = new int[N];
    for (int i = 0; i < N; i++) {
      data[i] = i;
    }
    iterativeMergesort(data);

    int i1 = Verifier.nondetInt();
    int i2 = Verifier.nondetInt();
    Verifier.assume(0 <= i1 && i1 < i2 && i2 < N);
    assert (data[i1] <= data[i2]);
  }

  /////////////////////////////////////////
  // Iterative mergeSort
  /////////////////////////////////////////

  public static void iterativeMergesort(int[] a) {
    int[] aux = new int[a.length];
    for (int blockSize = 1; blockSize < a.length; blockSize *= 2)
      for (int start = 0; start < a.length; start += 2 * blockSize)
        merge(a, aux, start, start + blockSize, start + 2 * blockSize);
  }

  /////////////////////////////////////////
  // Iterative mergeSort without copy
  /////////////////////////////////////////

  public static void iterativeMergesortWithoutCopy(int[] a) {
    int[] from = a, to = new int[a.length];
    for (int blockSize = 1; blockSize < a.length; blockSize *= 2) {
      for (int start = 0; start < a.length; start += 2 * blockSize)
        mergeWithoutCopy(from, to, start, start + blockSize, start + 2 * blockSize);
      int[] temp = from;
      from = to;
      to = temp;
    }
    if (a != from)
      // copy back
      for (int k = 0; k < a.length; k++) a[k] = from[k];
  }

  private static void mergeWithoutCopy(int[] from, int[] to, int lo, int mid, int hi) {
    // DK: cannot just return if mid >= a.length, but must still copy remaining elements!
    // DK: add two tests to first verify "mid" and "hi" are in range
    if (mid > from.length) mid = from.length;
    if (hi > from.length) hi = from.length;
    int i = lo, j = mid;
    for (int k = lo; k < hi; k++) {
      if (i == mid) to[k] = from[j++];
      else if (j == hi) to[k] = from[i++];
      else if (from[j] < from[i]) to[k] = from[j++];
      else to[k] = from[i++];
    }
    // DO NOT copy back
    // for (int k = lo; k < hi; k++)
    //   a[k] = aux[k];
  }

  /////////////////////////////////////////
  // Recursive mergeSort, adapted from:
  // Sedgewick and Wayne, Introduction to Programming in Java
  // http://www.cs.princeton.edu/introcs/42sort/MergeSort.java.html
  /////////////////////////////////////////

  private static void merge(int[] a, int[] aux, int lo, int mid, int hi) {
    // DK: add two tests to first verify "mid" and "hi" are in range
    if (mid >= a.length) return;
    if (hi > a.length) hi = a.length;
    int i = lo, j = mid;
    for (int k = lo; k < hi; k++) {
      if (i == mid) aux[k] = a[j++];
      else if (j == hi) aux[k] = a[i++];
      else if (a[j] < a[i]) aux[k] = a[j++];
      else aux[k] = a[i++];
    }
    // copy back
    for (int k = lo; k < hi; k++) a[k] = aux[k];
  }

  public static void recursiveMergesort(int[] a, int[] aux, int lo, int hi) {
    // base case
    if (hi - lo <= 1) return;
    // sort each half, recursively
    int mid = lo + (hi - lo) / 2;
    recursiveMergesort(a, aux, lo, mid);
    recursiveMergesort(a, aux, mid, hi);
    // merge back together
    merge(a, aux, lo, mid, hi);
  }

  public static void recursiveMergesort(int[] a) {
    int n = a.length;
    int[] aux = new int[n];
    recursiveMergesort(a, aux, 0, n);
  }
}
