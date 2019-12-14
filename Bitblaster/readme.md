# Bitblaster

Implementation of bit blasting in Haskell. Bit blasting means transforming a given formula in bitvector logic into a Boolean Satisfiability Problem (SAT). This can be useful in the context of software verification, for example because numerical data types can be represented as bit vectors. Thus we can prove that a given program does (not) satisfy some property by encoding both the program and the property into a SAT problem. The algorithm was implemented as an exercise for the lecture "Decision Procedures" at KIT.

The program provides an interface for the following two commands:

- `Multiply x y` formalizes the multiplication of two integers as a SAT formula. The result of the operation will be assigned to specific variables corresponding to the result bit vector. The numbers of the variables are printed as a comment.
- `CheckPrime x` generates a SAT formula to check if the integer x is prime. If the formula is satisfiable, then x is prime.

Actually, the algorithm itself can encode arbitrary bit vector formulas, but since it wasn't needed for the exercise, there is no command line interface for the full functionality.

In the current form, the algorithm is rather inefficient (long runtime and generates large but easy to solve formulas). One reason for this is that the algorithm internally uses its own data structure to represent logical formulas (`LogicExpression`) because it was easier to implement this way. Later, this structure is simplified in a naive way, and then converted into CNF using the Tseitin Encoding. This leads to the introduction of many unnecessary variables in the encoding.

