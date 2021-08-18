z3str3-integration.md

## z3str3 Support in SPF ##

The string solver z3str3 is integrated into the SMT solver z3. The source for z3 is available at:
https://github.com/Z3Prover/Z3  

### Building z3/z3str3 ###

The build process for z3 includes the option for creating a Java .jar file that exposes the functionality of z3/z3str3 for use in Java programs such as SPF. Check the instructions for building with CMAKE at:  
https://github.com/Z3Prover/z3/blob/master/README-CMake.md   

Once the build is complete, the .jar file and all corresponding library files must be placed in the bin directory in SPF:

Files: |  
------ |
com.microsoft.z3.jar  
libz3.dll  
libz3.dylib  
libz3.so  
libz3java.dll  
libz3java.dylib  
libz3java.so  

### Specifying z3str3 ###

z3str3 can be specified in the .jpf file. Example:  

    symbolic.string_dp=z3str3

### Setting z3str3 Options ###

There are options specific to z3str3 that can be set in the .jpf file:

__z3str3 String Option__ | Corresponding .jpf Property:  
------------------------ | ----------------------------
__str.aggressive_length_testing__ (bool) (default: false) | symbolic.z3str3_aggressive_length_testing  
__str.aggressive_unroll_testing__ (bool) (default: true) | symbolic.z3str3_aggressive_unroll_testing  
__str.aggressive_value_testing__ (bool) (default: false) | symbolic.z3str3_aggressive_value_testing
__str.fast_length_tester_cache__ (bool) (default: false) | symbolic.z3str3_fast_length_tester_cache
__str.fast_value_tester_cache__ (bool) (default: true) | symbolic.z3str3_fast_value_tester_cache  
__str.fixed_length_naive_cex__ (bool) (default: true) | symbolic.z3str3_fixed_length_naive_cex  
__str.fixed_length_refinement__ (bool) (default: false) | symbolic.z3str3_fixed_length_refinement  
__str.string_constant_cache__ (bool) (default: true) | symbolic.z3str3_string_constant_cache  
__str.strong_arrangements__ (bool) (default: true) | symbolic.z3str3_strong_arrangements  


For example, to set str.string_constant_cache to _false_, the following entry would be made in the .jpf file:  

    symbolic.z3str3_string_constant_cache=false  

Specific information about these options can be found through the z3 executable parameters option:

    z3 -p

### Limitations of z3str3 in SPF ###  

z3str3 is compliant with the SMT-LIB standard located at:  
http://smtlib.cs.uiowa.edu/

The input language of z3str3 is limited to SMT-LIB constructs, and does not directly implement Java string operations one-for-one. The input language specification can be found at:  
https://zyh1121.github.io/z3str3Docs/inputLanguage.html#input-language-summary  

### Supported String Operations ###

Due to the limits of the input language, z3str3 does not support all Java string operations. The following table presents those string operations available in z3str3.

Supported Operations: |
--------------------- |
concat(String str)    |
startsWith(String prefix) |
endsWith(String suffix) |
charAt(int index) |
length() |
replace(char oldChar, char newChar) |
replace(CharSequence target, CharSequence replacement) |
substring(int beginIndex, int endIndex) |
substring(int beginIndex) |
contains(CharSequence s) |
indexOf(String str) |
indexOf(String str, int fromIndex) |
equals(Object anObject) |
