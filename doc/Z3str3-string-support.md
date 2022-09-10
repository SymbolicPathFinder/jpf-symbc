# Z3str3 String Solving 

## Acknowledge
This work is supported by [GSoC 2022](https://summerofcode.withgoogle.com/), an international annual program focused on bringing new contributors to open source projects. 

## Introduction
Java Pathfinder (JPF) is a Java bytecode analysis tool mostly used for model checking.
Symbolic Pathfinder (SPF) is a symbolic execution tool for Java bytecode based on JPF.
In SPF, preliminary Z3str3 integration has been implemented during GSoC 2021.
However, the existing implementation only support string functions explicitly implemented by SMTLib. 
A full list of string methods supported by the previous work can be found in [this document](z3str3-integration.md).

We extended SPF string solving by adding support to more complicated string methods.
Due to time limit, we only added full support for 3 methods and partial support for another 3.
For the rest methods, we evaluate the difficulty of supporting them, and proposed ideas for some of them.
In addition, we also augmented current string examples and tests by fixing minor bugs in SPF string solving and run configurations.


## Contributions
All the code we have contributed can be found at [this url](https://github.com/marlinroberts21/jpf-symbc/compare/mjr/dev_init_igen...yanxx297:jpf-symbc:mjr/dev_init_igen).

With Those changes, 6 more methods are fully or partially supported, and 5 previously failed examples under src/example/strings can pass now.
More details about the current status of SPF's string solving support can be found in the first 2 tabs of [this spreadsheet](https://docs.google.com/spreadsheets/d/1c5TlmLC2TiL83K7531vKj7874NFxmZ7gC3P8TMUunJk/edit#gid=0).

### Newly supported functions
Based on the result running examples in [src/examples/strings](../src/examples/strings), we prioritized methods that are required by more examples and less complicated to implement.

`isEmpty()`, `valueOf(char)` and `valueOf(int)` are now fully supported. 
`isEmpty()` is implemented based on existing support to `length()`.
`valueOf(char)` is modeled by `str.from_code`.
To model `valueOf(int)`, the input integer is converted to its absolute value, and then converted to string by str.from_int.  

Note: SPF sometimes cannot tell whether the `valueOf()` function should be modeled as `valueOf(char)` or `valueOf(Int)`.
Add more pattern checking on demand.

Integer `AND`, `ParseInt()` and `trim()` are partially supported due to limited time.
We discuss what already works and what left unfinished.

Integer `AND` and all other bitwise operations for integer are not supported in existing SPF, while `AND` is required by [ChallengeTest](../src/examples/strings/ChallengeTest.java) and [IndexOfTest](../src/examples/strings/IndexOfTest.java) when converting an integer to a char.
To model integer `AND` in SMTLib, we convert the input integer to a bit vector, perform bitwise `AND` and convert the result back to integer.
Unfortunately, this implementation is too slow to use in practical. 
As a workaround, we check whether the input integer is the result of `charAt()`, and whether it is converted to a char (`AND` with 65535 in java bytecode.) 
If both conditions are satisfied, then we simply remove the `AND` operation.

Although `ParseInt()` is an Integer method rather than a string method, we decide to add support to it since it is required by [MasterMind](../src/examples/strings/MasterMind.java).
In SPF, `ParseInt()` translates to an internal operation named `isInteger` when added to string path conditions.
We have modeled this operation mostly using `str.to_int`.
The problem is that the output of `ParseInt()` output will appear in numeric path conditions, and special handling is required to make it fully functioning.
See [this section](#Complete-partially-supported-methods) for more discussions.

A preliminary prototype of `trim()` has been implemented using on SMTLib regex.
Current implementation only works when there is only one occurrence of trim() in one solver query (e.g. `testTrim()` in [E5](../src/examples/E5.java)).

### Run testSymString with Z3str3
[TestSymString](../src/tests/gov/nasa/jpf/symbc/strings/TestSymString.java) contains string tests based on JUnit.
As far as we can tell, those tests haven't been tested recently.
Currently, we can run them automatically by ``ant test``.
In the future, testing automation will switch to Gradle.

We run those tests and found they are inconsistent with the real Z3str3 string solving implementation.
To fix this problem, we modified both [SPF](https://github.com/yanxx297/jpf-symbc/commit/fdfcb2053d239d63deee0aa9082af57e88ea2e56) and the tests.
See [TestZ3SymString](../src/tests/gov/nasa/jpf/symbc/strings/TestZ3SymString.java) for an example porting those tests to Z3.

### Minor fixes
While running some string examples, we found that `startsWith()` are modeled as ``str.prefixof str prefix``, while the correct order should be ``str.prefixof prefix str``.
The same problem exists in endsWith().
This bug has been fixed in our work.

In addition, we augmented string examples.
[MasterMind](../src/examples/strings/MasterMind.java) previously exists in `src/examples/strings` but haven't been set up.
We created the configuration file and refactor it so that we can easily set the important inputs to symbolic.
Existing [Tricky](../src/examples/strings/Tricky.java) doesn't result in any string path condition, which is undesirable for a string example.
As an augmentation, we added a branch on a symbolic string to this example.

We also fixed minor bugs such as [6fca10e](https://github.com/yanxx297/jpf-symbc/commit/6fca10e00e7a31e32e53d5cc5dd8d681ea7f94dd) and [520398a](https://github.com/yanxx297/jpf-symbc/commit/520398a4e3fcc2c65c4a18965cc60330e81b6975).
Those small fixes can help passing more examples.

## Future Work
Below is a list of works left unfinished.
For those unfinished tasks, we discuss what we learned and propose approaches to handle them in the future.

### Complete partially supported methods

Currently, Integer `AND` can be modeled efficiently only for a special case.
The intuitive approach that converting between integers and vectors back-and-forth is too slow. 
We should either model this operation in an optimized way or wait until Z3 can handle integer-vector converting more efficiently.

Since `ParseInt()` affects both numeric and string path conditions, special handling is required to make it work.
It should be handled in the same way `length()` is handled. 
See how `SymbolicLengthInteger` is used to handle `length()` as an example.
To reproduce this problem, run MasterMind.

For complete support to `trim()`, SPF should create difference SMT variables for each unique occurrence of `trim()`.

### Support more string methods
`codePointAt()`, `toLowerCase()`, `toUpperCase()` and `equalsIgnoreCase()` can be supported by a combination of SMTLib methods.
`codePointAt()` can be modeled mostly accurate using `str.at` and `str.to_code`.
Note that it may covert either one or two chars to its code point, and the details should be handled carefully.
`toLowerCase()` and `toUpperCase()`  can be modeled by replacing all 26 lower (upper) case letters to upper (lower) case.
`equalsIgnoreCase()` can be implemented using `equal()` and `toLowerCase()` (or `toUpperCase()`).

`lastIndexOf()` can be supported by regex. See how we [implement trim() using regex](trim.smt) as an example. 

The rest methods are more difficult.
To support `matches()`, `replaceAll()` and `split()`, Java regex support is required.
Implementing Java regex in SMTLib can be a lot of engineering work, since SMTLib only support a subset of Java regex operations.
`format()`, `codePointCount()`, `compareTo()` and `valueOf(float)` are fundamentally difficult both because of their complexity and because there is no corresponding features in SMTLib.

### Z3str3 support for TestSymString
`TestSymString` currently not work with Z3str3, since it doesn't fully match the actual implementation of Z3str3 string support.

Our current solution is to create Z3str3 version of `TestSymString`.
For now only one test has been ported for Z3.
See [TestZ3SymString.java](../src/tests/gov/nasa/jpf/symbc/strings/TestZ3SymString.java) for an example.

It is more desirable if we can fix SPF and run TestSymString without modifying it.
To achieve this goal, it is necessary to copy solver solutions to the solution field of corresponding `StringSymbolic`.
The problem is that SPF doesn't maintain a list of existing `StringSymbolic` objects.
Only a list of object names are maintained, but we have no idea how to find and access the corresponding objects using their names.
As an ultimate solution, we can iterate the path condition and collect a list of `StringSymbolic` objects.


