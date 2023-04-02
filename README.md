# Linear Logic Library

This repository contains a collection of formalizations of linear logic. We formalize propositional (PLL), first-order (FOLL), focused (FLL), and multimodal focused (MMLL) versions using the sequent calculi formalism. This repository corresponds to the implementation of an ongoing doctoral thesis work.

## Getting Started

The project was tested in Coq 8.16. No extra library is needed for compilation. 

### Building 

Typing "make" should suffice to compile the project:

```
coq_makefile -f _CoqProject -o Makefile
make
```

## Linear Logic

The directories PLL and FOLL correspond to the specification of Propositional and First-Order Linear Logic, respectively. If you are not familiar with Coq, we recommend starting with the PLL directory. For the First-Order version, we consider three systems of sequent rules in one-sided style (i.e. the antecedent of the sequents is empty): 

* **Monadic**: a single context of formulas represented as a multiset.
* **Dyadic**: two contexts of formulas, both represented as multisets.
* c**DyadicExc**: two contexts of formulas: the classical context, represented as a multiset, and the linear context, represented as a list. Due to this difference, there is an explicit rule for exchanging formulas in the linear context.

## Linear Logic as a Logical Framework 

We use the Hybrid library to support reasoning about object logics (OLs)
expressed using higher-order abstract syntax (HOAS). Hybrid is implemented as a two-level system and then, we have:

 - FLL and MMLL as specification logics (SL); and
 - Different OLs encoded as FLL and MMLL theories. 

For this reason, the project is divided in two main subdirectories, namely,  SL and OL plus an additional one (Misc) for some miscellaneous definitions and
results. 

> :construction: Under Construction :construction: