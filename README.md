# MonotoneSecurity
This is a security analyser written in F# for implicit and explicit information flow in a simple Guarded Command Language. It enables annotating the variables and arrays as unclassified and classified. Classified variables and arrays must additionally be associated with a security level in a user-defined lattice. The security level of unclassified variables and arrays can change throughout the program, and is derived in the analysis. The idea is that a security violation can never occur by information flowing into an unclassified variable, but may happen by information going from a classified variable through an unclassified variable and then into another classified variable.

The analysis happens in the following steps:
- The given AST is transformed to a program graph annotated with the implicit flows
- An analysis in the monotone framework derives the security levels of the unclassified variables and arrays in the different nodes
- The edges of the program graph are examined with the implicit flows and the derived security levels as context, and a set of security violations is returned

## Overview of the repository
- <code>MonotoneSecurity.fsproj</code> defines the order of compilation and imports packages
- <code>src/AST.fs</code> contains the types used for ASTs and program graphs
- <code>src/ProgramGraph.fs</code> contains the functions for deriving an annotated program graph from an AST
- <code>src/Algorithms.fs</code> defines the algorithms powering the monotone analysis (currently only a naive stack)
- <code>src/Monotone.fs</code> contains functions for generic monotone analyses
- <code>src/Classification.fs</code> contains a monotone analysis for deriving security levels of the unclassified variables and arrays
- <code>src/Security.fs</code> combines the other functions and defines functions for deriving security violations
- <code>src/Lattice.fs</code> contains an example security lattice
- <code>tst/ProgramGraphTest.fs</code> tests the functions of <code>src/ProgramGraph.fs</code>
- <code>tst/ClassificationTest.fs</code> tests the functions of <code>src/Classification.fs</code>
- <code>tst/SecurityTest.fs</code> tests the functions of <code>src/Security.fs</code>
- <code>src/Program.fs</code> performs the analysis of a hard-coded AST (UI to come)
