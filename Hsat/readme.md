# Hsat - A simple SAT Solver written in Haskell

Very simple implementation of DPLL-like algorithm in Haskell. It features unit propagation and branching on variables. The code is explained in the comments, but it could be written a lot cleaner. This is one of my first algorithms written in Haskell.

Example of usage:
```
$ ghci sat.hs
*Hsat> solve [[1,2], [-1,-2,-3], [-1,2,-3], [-2,-3], [-1,3]] 3 []
(Just True,[(1,False),(2,True),(3,False)])
```

In this example we solved the formula:

(a ∨ b) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b ∨ ¬c) ∧ (¬b ∨ ¬c) ∧ (¬a ∨ c)

And got the solution:

Formula is SAT: a = false, b = true, c = false

