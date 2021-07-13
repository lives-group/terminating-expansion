Type based expansion of finite recursion
========================================

Introduction
------------

In this draft, we outline the ideas of a core programming language featuring 
a type based termination criteria. The main novelty of the language design is 
its elaboration that unfolds a function call into a term that has a pattern 
matching ... FINISH THIS DESCRIPTION 


Syntax 
------

1. Type syntax: Our type syntax consist of named types, denoted by variable $C$,
which include basic types (int, bool, string, etc) and user defined types. Our type
language features the function space, tuples and a coproduct type.

$$
\begin{array}{lcll}
    \tau  & ::=  & C^\iota               &\text{Type name}\\
          & \mid & \tau \to \tau         &\text{Function name}\\
          & \mid & (\tau, ..., \tau)     &\text{Tuples}\\
          & \mid & \tau \oplus \tau      &\text{Coproduct}\\
    \iota &
\end{array}
$$

2. Top-level definitions: Our language supports 3 basic forms for top-level 
definitions. The first is type declarations which introduce a new type name
which can be understood as a synonym. The syntax for type definitions is as
follows:

$$
\text{type }C = \tau
$$

which introduces the new type name which is equivalent to type $\tau$. The 
type $\tau$ must not contain any negative occurrence the newly defined 
type $C$ in order to ensure termination properly.

Besides type definitions, our language features two classes of functions: 
total and unrestricted. 

Unrestricted functions does not limit recursion and does not need to be type 
checked by our approach. However, such functions need to be elaborated if they
call a total function.

Total functions need to be type-checked by our algorithm since they must be 
terminating.

$$
\begin{array}{ll}
  \text{def }f = e   & \text{Unrestricted function}\\
  \text{total }f = e & \text{Total function}\\
\end{array}
$$

3. Expression syntax: The syntax of expressions consists of the 
traditional constructions for the $\lambda$-calculus extended with
a case construct and primitives for tuples, coproducts and a special 
construct for calling a total function.

$$
\begin{array}{lcll}
  e & ::=  & x             & \text{Variables} \\
    & \mid & \lambda x. e  & \text{Abstraction}\\
    & \mid & e\:e          & \text{Application}\\
    & \mid & \text{case }e\text{ of }\{\overline{p \to e}\} & \text{Case construct}\\
    & \mid & v             & \text{Constants for primitive types}\\
    & \mid & \text{left }e & \text{Coproduct constructor}\\
    & \mid & \text{right }e & \text{Coproduct constructor}\\
    & \mid & (e,...,e) & \text{Tuple constructor}\\
    & \mid & f[n]      & \text{Total function call}\\
    &      & \\
  p & ::=  & x           & \text{Pattern variable}\\
    & \mid & (p, ..., p) & \text{Tuple pattern} \\
    & \mid & v           & \text{Constants} \\
    & \mid & \text{left }e & \text{Coproduct pattern}\\
    & \mid & \text{right }e & \text{Coproduct pattern}\\
\end{array}
$$


Some questions to be answered
=============================

1. Does it need to have two different classes for functions?
   - How can we call a total function inside a total function?
   - Can we call an unrestricted function inside a total one?
   
