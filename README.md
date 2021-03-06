Terminating Expansion
===

A formalization of a strategy to compile general recursive functions into “equivalent” non-recursive ones.
It features a transformation algorithm and some interpreters.

## Desired Properties
1. The transformation is a total function, i.e., the function always halts with a value for every valid input. The proof is in the following file: https://github.com/lives-group/terminating-expansion/blob/52ede9f740436edbe1ca754668a87a79a319beef/src/Transform/Translation.agda#L113
2. The programs obtained with transformation always halt, even if with the out-of-fuel error. The proof is the definitional interpreter defined in: https://github.com/lives-group/terminating-expansion/blob/7de264e4bccf98ad94b92264c799b7220393bdfa/src/L/Semantics/Definitional.agda#L55
3. If a program M is transformed into M' and the execution of M' yields a value, then the execution of M yields the same value. No proof yet, but a property-based test is being made in https://github.com/mayconamaro/ringell-properties
4. If the execution of a program M halts with a value using at most f recursive calls and M is transformed into M' using f as the expansion factor, then the execution of M' yields the same value.

These properties, if proven, ensure the strategy transform any function into a non-recursive function with the same semantics, as long as the expanding factor is high enough. Non-terminating programs will always compile into "out-of-fuel" no matter how high the expanding factor is, but a transformed program answering the "out-of-fuel" doesn't mean the original won't terminate, it could just need a higher factor. This strategy does not solve the halting problem.
