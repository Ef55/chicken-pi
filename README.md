# Chicken-pi (provisional name)

A toy proof-assistant based on
[pi-forall](https://github.com/sweirich/pi-forall).

## Roadmap

This roadmap indicates the status of the project.
Note that these should not necessarily be done in order.

1. Removals from pi-forall:
   - [ ] Remove (syntax) for irrelevant arguments.
   - [ ] Prevent recursive functions.
2. "Dirt simple" (no parameters/indices) datatypes (see [oplss notes](https://github.com/sweirich/pi-forall/blob/2023/doc/oplss.pdf) chapter 9):
   - [X] Definition.
   - [X] Pattern matching (without `as`, `in` ~and `return`~).
   - [X] Exhaustivity check for pattern matching.
   - [ ] Relax ordering in patterns.
   - [X] Wildcard in patterns.
3. Universes:
   - [ ] Sorts: `Prop`, `Set`, and `Type i`.
   - [ ] Universe subtyping/cumulativity (see [subtyping rules](https://coq.inria.fr/doc/V8.19.0/refman/language/cic.html#subtyping-rules)).
   - [ ] Impredicative `Prop`.
   - [ ] Ensure proof erasability (see [`Prod-*` rules](https://coq.inria.fr/doc/V8.19.0/refman/language/cic.html#id6)).
   - [ ] Empty/singleton elimination (see [`Prop-extended`](https://coq.inria.fr/doc/V8.19.0/refman/language/core/inductive.html)).
4. [Coq-style](https://coq.inria.fr/doc/V8.19.0/refman/language/core/inductive.html)
   datatypes and pattern matching:
   - [ ] [(Strict) positivity](https://coq.inria.fr/doc/V8.19.0/refman/language/core/inductive.html) check.
   - [ ] "[Guardness](https://link.springer.com/chapter/10.1007/3-540-60579-7_3)" check.
   - [ ] [Dependent pattern matching](https://coq.inria.fr/doc/V8.19.0/refman/language/core/inductive.html#the-match-with-end-construction) (i.e. `as` and `return`).
   - [ ] Type parameters.
   - [ ] Type indices + pattern matching extension (`in`)
   - [ ] `if-then-else` as an alias for pattern matching
   - [ ] Support `data` equalities in `Contra`.

## Known differences with Coq

- The syntax might still be closer to pi-forall than Coq.
- `Type` have an explicit level annotation.