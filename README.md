# Type Theory Seminar

## Resources

### Book: Type Theory and Formal Proof
Tentatively we are using this book: [https://www.amazon.com/Type-Theory-Formal-Proof-Introduction/dp/110703650X](https://www.amazon.com/Type-Theory-Formal-Proof-Introduction/dp/110703650X). If anyone has issues due to the price of the book, please let us know ASAP.

### Notes

1. [Chapter 1 notes](https://github.com/donald-pinckney/type-theory-seminar/raw/master/notes/ch1/notes.pdf)
2. [Chapter 2 notes](https://github.com/donald-pinckney/type-theory-seminar/raw/master/notes/ch2/notes.pdf)

## **TENTATIVE** Schedule

Roughly we will plan to discuss primary content (i.e. readings from the book) on Tuesdays, and on Thurdays we can meet to discuss auxillary content such as alternate approaches to the material, more advanced material, etc. Later in the summer we plan to start a coding project, likely making a proof assistant.

Meeting times are yet to be determined.

| Meeting Dates | Readings Due, etc.  |
| ------------- |---------------|
| Tuesday, May 28      |  |
| Thursday, May 30      | Chapter 1 or [Chapter 1 notes](https://github.com/donald-pinckney/type-theory-seminar/raw/master/notes/ch1/notes.pdf)      |
| Tuesday, June 4      | Chapter 2 or [Chapter 2 notes](https://github.com/donald-pinckney/type-theory-seminar/raw/master/notes/ch2/notes.pdf)      |
| Thursday, June 6      |   **NO MEETING**   |
| Tuesday, June 11      | Chapter 3      |
| Thursday, June 13     |       |
| Tuesday, June 18      | Chapter 4      |
| Thursday, June 20     |   Implementation meeting    |
| Tuesday, June 25      | Chapter 5      |
| Future TBD | TBD |


## Status of Projects

### Idris (branch `idris-impl`, led by Donald)

Roughly, the goal for now is to loosely follow the book by implementing the discussed variants of lambda calculus. Since it is in Idris, we can also give proofs of some of the theorems in the book, with respect to our implementation. Roughly my attitude is to prove what I want / what is fun, but don't get too caught up on the proofs.

#### Features / Progress
- [x] All of chapter 1 (Parsing, beta reduction)
- [x] (mixed) De Bruijn indices. With this representation alpha-equivalent terms are equal terms (`=`) in Idris
- [x] Cool REPL for chapter 1
- [x] Chapter 2 parsing
- [x] Chapter 2 contexts, using dependent types to ensure all declarations are unique
- [x] Derivation rules specified as an inductive type in Idris
- [x] Fully verified type checker with respect to those rules. (i.e. it is impossible for the type checker to incorrectly accept / reject a program)
- [ ] Theorem: Type preservation under substitution
- [ ] Theorem: Beta reduction type preservation (done except for above theorem)
- [ ] Theorem: Progress under beta reduction (should be very easy)
- [ ] Term finder

#### How to help

People can work on theorem proving about stuff in say chapter 2, while concurrently other people work on stuff for future chapters. Just see what is most interesting to you to implement or prove. People can also go back and give proofs of things that were left unproved, such as Church Rosser theorem, etc.

### Haskell (branch `hs`, led by Ben / Aaron)
Currently two different implementations, the `Untyped` and `SimplyTyped` lambda
calculi. These are pretty much done and were mainly to get a feel for
Haskell/parser generators. Still, stuff like REPL support would be welcome as
this work will probably be largely reusable in future languages

### Haskell Inductive (branch `hs-inductive`, led by Ben / Aaron)
Working on a more robust type system with the ultimate goal of including
inductive types (such as Idris's `data Nat = Z | S Nat`). In addition, product
types and sum types as well as type constructors and records will be included
with the intention of doing some pattern matching.

This is a prototyping station for different features to be included in the proof
system we build later. Aaron will be hacking on a dependently typed system, and
we will either modify the inductive system with dependent types, modify
dependent types with some nice syntactic sugar from `hs-inductive`, or start a
new module entirely.

Right now I'm working on writing out a grammar for the type system and will try
to get a parser. In the mean time I'm reading some Pierce and Harper to learn
about the implementations of these systems.

Working grammar file can be found in the [lang.markdown](https://github.com/donald-pinckney/type-theory-seminar/blob/hs-inductive/toy-lambdas/src/Inductive/lang.markdown)
file on the [hs-inductive](https://github.com/donald-pinckney/type-theory-seminar/tree/hs-inductive) branch.
