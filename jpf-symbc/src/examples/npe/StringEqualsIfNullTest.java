package npe;

import org.sosy_lab.sv_benchmarks.Verifier;

public class StringEqualsIfNullTest {
    public static void main(String[] args) {
        // Tests for String.equals() method with symbolic execution to check for null pointer exception
        // Each test explores different variation add individual methods to run specific test scenarios
        // In contrast, conditions like str == null or str != null add branching when str is symbolic,
        // meaning both null and non-null paths are explored for str.
    }

    // Test 1: if str is not null - branch check (arg != null) => (IFNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNotNull1() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str != null) {
            System.out.println("str is not null");
            if (str.equals(arg)) {
                System.out.println("Test 1: Then Side");
            } else {
                System.out.println("Test 1: Else Side");
            }
        } else {
            System.out.println("str is null");
        }
    }

    // Test 2: if str is not null - branch check (arg == null) => (IFNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNotNull2() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str != null) {
            System.out.println("str is not null");
        } else {
            System.out.println("str is null");
            if (str.equals(arg)) {
                System.out.println("Test 2: Then Side");
            } else {
                System.out.println("Test 2: Else Side");
            }
        }
    }

    // Test 3: if str is not null - branch check (arg != null) and (arg == null) => (IFNULL)
    // Branching occurs because str is symbolic and can be either null or not null
    public static void testNotNull3() {
        String arg = "Hello";
        String str = Verifier.nondetString();
        if (str != null) {
            System.out.println("str is not null");
            if (str.equals(arg)) {
                System.out.println("Test 3: Then Side");
            } else {
                System.out.println("Test 3: Else Side");
            }
        } else {
            System.out.println("str is null");
            if (str.equals(arg)) {
                System.out.println("Test 3: Then Side");
            } else {
                System.out.println("Test 3: Else Side");
            }
        }
    }
}
