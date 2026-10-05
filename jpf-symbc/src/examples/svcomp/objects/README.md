<!--
This file is part of the SV-Benchmarks collection of verification tasks:
https://github.com/sosy-lab/sv-benchmarks

SPDX-FileCopyrightText: 2011-2020 The SV-Benchmarks Community

SPDX-License-Identifier: Apache-2.0
-->

# Java nondeterministic Object Benchmarks

These benchmarks were added to provide some instances in which 
objects are created non-deterministically. These benchmarks
use the `nondetObject(..);` method of the Verifier class, which 
was added for these instances.

The idea is that (as for the other methods of the Verifier class), 
verifiers can replace the implementation, while the code also 
generates the full range of objects for which the analysis should
be performed. This is achieved through the newly added interface
`ObjectFacory`. Object factories have to provided alongside 
benchmarks.

The full signature of the `nondetObject` method is 

```Java
public static <T> T nondetObject(Class<T> type, ObjectFactory<T> factory)
```

This allows it to (a) use the return value of `nondetObject` as a `T`
without casting it and (b) to provide the factory that creates all 
possible instances of `T`.
