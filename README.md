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

## The Isabelle files
### Monotone.thy
This is the start of a quite detailed theorem which would cover both translation from AST to Program Graph, the main properties of the monotone framework, and the security analysis. I'm trying to make it so that when it's finished it would be possible to use code generation to get the translation from AST to Program Graph, the general monotone analysis functions, the monotone security analysis functions, and the functions for checking for security violations. I.e. a verified version of the F# project.

I currently only have the definition of an AST, interpreter of AST, translation from AST to Program Graph, and some manual proofs on programs written as ASTs.

### Security.thy
Security.thy contains just the parts that are novel to my analysis. I assume that a program graph has already been constructed and that the implicit flows are marked correctly. I define the monotone security analysis function, but not the rest of the monotone framework. In the main theorem I just assume that the constraints have been solved. I want to show that if the constraints have been solved and no violations are detected, then the program graph has the property of non-interference (if you run the program twice with different starting values for high-security variables but the same values for low-security variables, then you will end up with the same values for the low-security variables). Things like the extraction of implicit flows from ASTs and that the monotone framework solves the constraints if the analysis function is monotone has been proven by others before, so I'm not doing that in this file.

For Security.thy I have the entire skeleton of what I want to show. I'm missing a definition of non-interference and a definition of implicit flows being labeled correctly. I also have some very big sorryies, and will need quite a few helping lemmas.
