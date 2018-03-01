Support for multiple decision procedures (based on work done by Saswat 
Anand for old symbolic framework);
set the "symbolic.dp" JPF configuration variable to one of the modes below.
I don't intend to keep the old file,pipe interface.
We will support: CVC3/CVCLite, STP, Yices, Omega.
 
For example from command line you can use "+symbolic.dp=omega.native", 
in which case JPF will use omega native interface.

Supported modes:
omega.native
omega.native.inc
yices.native
yices.native.inc
yices.native.incsolve
cvcl.native
cvcl.native.inc
cvcl.native.incsolve
stp.native

Description of Modes:
<name>.native - JNI Interface for decision procedure <name> 
	Path conditions are maintained inside JPF world.
	No problems with printing. Solving is done by POOC.	

<name>.native.inc - Path conditions are maintained in C side.
	Checking of constraint is done incrementally.
	Printing and solving does not work yet. Easy to fix.

<name>.native.incsolve - Constraints are checked incrementally
	using push/pop feature of decision procedures. Not 
	clear on how to print/solve path condition.


Notes:
1. Subsumption works only for omega.native correctly. (not sure if I'll keep 
this).
2. omega.inc and yice.native.incsolve are usually the fastest.
3. Reals: yices.native.* and cvcl.native.* handle real linear constraints.


	

