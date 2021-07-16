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
      * Probably we can just expand them normally passing the current 
        recursion counter.
   - Can we call an unrestricted function inside a total one?
      * (maycon) if unrestricted functions only call total ones, they cannot call themselves, thus they cannot be recursive. But they would be trivially terminating, so  *a priori* it is no problem to call them inside total functions. If we allow unrestricted functions to call unrestricted ones, we would be allowing unlimited recursion, and would be turing complete (undesirable). So I think we should not have two classes for functions.
   
Maycon’s Draft
===
Trying to define some basic functions over lists. Our language does not contain polymorphism, so I cannot define `list a` for all `a`. Let’s work with an assumed `listC` instead, with constructors `nil` and `cons C listC`. Remember that `C` can be defined as synonym of any specific type, so our definition will work for arbitrary types without negative occurences, but it won’t be *general* in the polymorphism sense.

map
---
Without polymorphism, let’s work with total functions from `C` to `C`, our previously defined synonym.
$$
\text{total map} = \lambda f : C \rightarrow C.\lambda x 
: \text{listC}. \text{ case } x \text{ of } 
\{\text{nil} \rightarrow \text{nil}, \text{cons }
p \: s \rightarrow \text{cons } (f[p]) \: (\text{map } [f \: s])\} 
$$

Let’s expand the execution for a list of ints and successor function. Assume `+1` is written as $\lambda x : \text{int} . x+1$.

```
map (+1) (cons 1 (cons 2 (cons 3 (cons 4 nil))))
~
case of (cons 1 (cons 2 (cons 3 (cons 4 nil)))) {cons 1 (cons 2 (cons 3 (cons 4 nil))) -> cons (1+1) (map [(+1) (cons 2 (cons 3 (cons 4 nil)))])}
~
case (cons 1 (cons 2 (cons 3 (cons 4 nil)))) of {cons 1 (cons 2 (cons 3 (cons 4 nil))) -> cons (1+1) (case (cons 2 (cons 3 (cons 4 nil))) of 
{cons 2 (cons 3 (cons 4 nil)) -> map [(+1) (cons 3 (cons 4 nil))]})}
...
```

The expansion is tiring but possible, no major problems found. We would need the list size as the recursion counter. But what if the function was to find the number of prime divisors of a number? This function would need to be recursive (potentially total tho), and it would need to expand inside each expansion step above. The expansion tree can grow exponentially large when recursive functions are used inside our defined recursive functions and require for really large counters. If our argument function is the sum of the results of two recursive functions applied to the same argument, could they expand in parallel? Or will this exponential grow be this awful? [tomorrow I'll try more]