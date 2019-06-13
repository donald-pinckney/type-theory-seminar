# Idris implementation of type theory stuff

## How to Run / Build

- Run: `make run`
- Build: `make`
- Typecheck and run unit tests: `make test`

## What's currently implemented

- Untyped Lambda Calculus parser
- Resolves bound variables with De Bruijn indices
- A term being in beta normal form is represenented as a type (proposition). There is a decision procedure for seeing if a term is in BNF.
- Single step of beta reduction: this either takes a single step, or returns a proof that the term is already in BNF
- Multi step: this continually takes single steps until the term is in BNF
- REPL: a REPL that lets you evaluate (multi step terms), single step terms, and test for BNF. Type `:h` at the REPL for documentation.
