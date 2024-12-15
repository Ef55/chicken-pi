# Chicken-pi

> Pi-forall but with some ~chicken~ theorem-proving baked inside.

Chicken-pi is a toy proof assistant based on
[pi-forall](https://github.com/sweirich/pi-forall).
More precisely, it is based on pi-forall [version
2](https://github.com/sweirich/pi-forall/tree/2023/version2), extended with
Coq's
inductive types, pattern matching and universes.

## Building & running

All dependencies are defined in the cabal file, and stack should be able to
install them for you.

```shell
# Clone this repository
git clone https://github.com/Ef55/chicken-pi chicken-pi
# Move to the root of the repository
cd chicken-pi
# Build chicken-pi
stack build
# Run the tests
stack test
# Run a specific file (e.g. pi/Data/List.pi)
stack run chicken-pi pi/Data/List.pi
```

If you are using [nix](https://nixos.org/), you can use the provided flake to install all of the
dependencies (note however that the flake is not setup to build the project: it
just offers a devshell):
```shell
# From within this repository
nix develop
# And everything should be set up!
stack test
```

## Browsing the source

This project inherited pi-forall's codebase, and did not change much in term of
code organization:
- [`src/`](src) contains the source of the type-checker:
  - [`Syntax.hs`](src/Syntax.hs) defines the syntax of the language.
  - [`Environment.hs`](src/Environment.hs) defines the type-checking context, e.g. which definitions
    are in scope, and more generally the "type-checking monad" (`TcMonad`) which
    is used extensively in the two next files.
  - [`Equal.hs`](src/Equal.hs) defines a reduction from terms into their *weak head normal form*
    (`whnf`), which is used to determines whether two terms are equal, i.e. the
    `equate` function.
  - [`TypeCheck.hs`](src/TypeCheck.hs), which defines `checkType` and `inferType`, whose names are
    pretty self-explanatory.
- [`pi`](pi) contains the embryo of a standard library for chicken-pi
  (in [`pi/Data`](pi/Data) and [`pi/Logic`](pi/Logic)) as well as some
  extra examples (in [`pi/Examples`](pi/Examples)).
- [`test`](test) contains unit tests, as well a runner which type-checks all of
  these tests (and checks that the type-checking either succeeds or fails,
  depending on the test case) as well as the files in the [`pi`](pi) directory.
	Tests suffixed with `[✔]` are *positive* tests (i.e. files which should be
	accepted by the type-checker), and the ones suffixed with `[✘]` are *negative*
	tests (i.e. files which should be rejected by the type-checker).

## Comparison of chicken-pi with its inspirations (pi-forall, Coq, and some Lean)

The language is based on pi-forall (version 2, which doesn't include
(ir)relevance and datatypes) and its codebase.
The changes/additions can be
summarized as follows:
- Addition of (dependent) datatypes and (dependent) pattern matching;
- Addition of a hierarchy of universes;
- Restriction of recursive functions to prevent non-termination.
These changes should hopefully make chicken-pi (logically) sound.
Note that we did not change pi-forall's syntax to be closer to Coq.

We now detail theses points some more.

### Datatypes & pattern matching

Chicken-pi's datatypes should work exactly like the ones from Coq, except for
the absence of inference/heuristics and different keywords.
- Parameters and indices are supported.
- They are dependent; consider the following datatype:
  ```
	data D (t1: T1) ... (ti: Ti): I1 -> ... -> Ij -> S
	  C (p1: P1) ... (pk: Pk): S i1 ... ij
	```
	any `t_` is in the scope of any subsequent `T_`, as well as in the scope of
	all `I_` and `P_`. Any `p_` is also in the scope of any subsequent `p_`.
- Uniform type parameters are **not** supported.
- Dependent pattern matching is implemented using the `as`, `in`, and `return`
  keywords. Take a look at [`pi/Data/Vect.pi`](pi/Data/Vect.pi),
  [`pi/Data/HList.pi`](pi/Data/HList.pi), and
  [`pi/Data/Sigma.pi`](pi/Data/Sigma.pi) for examples.
- Pattern matching **must be** exhaustive, and all patterns must occur in the
  same order as the constructors were defined.
- Note that no type inference is attempted on pattern matching; the type must be
  known, i.e. using either the top-level signature, annotations or the `return`
  keyword.
	- The previous point makes it so that, if pattern matching occurs in a type
	(which includes propositions), it should most likely be annotated with
	`return` in order to for subsequent usages to type-check.

### Universes

In order to avoid paradoxes (e.g. [Hurken's
paradox](https://ionathan.ch/2021/11/24/inconsistencies.html)), `Type` cannot
have type `Type`.
Instead, types have a level, and `Type i` has type `Type (i + 1)`; these are
called *sorts*.
Following Coq, there are two special sorts, `Prop` and `Set`.
Sorts are related by a subtyping relation, noted `<`.
- For any `i`, `Type i < Type (i + 1)`.
- `Prop < Type 1` and `Set < Type 1`.
- The universes are cumulative, i.e. `t : S` and `S < S'` imply `t: S'`.
- An interesting difference between Coq the proof assistant and its
  documentation is the relation between `Prop` and `Set`: in the former, the two
  are unrelated; however, in the later, `Prop < Set`. Chicken-pi implemented the
  later. 
- Related to universes: chicken-pi implements proof irrelevance:
  - Terms of sort `Prop` could be "eliminated" from terms of sort `Set` without
		compromising their reduction.
	- This is implemented, following Coq, by preventing pattern matching on `Prop`
	  returning something in `Set`.
	- There is one exception: (sub-)singleton elimination, which is supported by
		chicken-pi (see [`pi/Logic/Eq.pi`](pi/Logic/Eq.pi) and
		[`pi/Examples/Contra.pi`](pi/Examples/Contra.pi)).
- Unlike Coq, `Type` have an explicit level, rather than all occurences of it
  being fresh variables with universe constrains which must later be solved.

### Fixpoints

General recursion is disallowed. Instead, a `fix` construct is available.
The syntax is as follows:
```
fix self p1 ... pk [r]. body
```
- `self` binds the function itself, the `p_`s are arbitrary parameters,
	`r` is the parameter on which the function will recurse.
- `self` must be fully applied (i.e. to `k + 1` arguments) every time it occurs
  in `body`.
- The last argument to the recursive calls in `body` must be "smaller" than `r`.
  A term `t` is smaller than `r` if:
	- It is a *recursive-component* of `r`. A recursive-component of `r` is any
	  variables introduced by pattern matching on: `r`; or another
	  recursive-component of `r`.
		- The variable must bind a recursive-component of
	    the constructor.
		- We say that a parameter `p: P` of a constructor for type `D` is a
		  recursive-component of the constructor if `D` occurs in `P`.
		- See
		  [`test/Fix/NonRecursiveComponent.pi`](test/Fix/NonRecursiveComponent.pi)
		  for an example of non-recursive-component.
	- It is of the form `l r` where `l` is itself smaller than `r`.
	- It is of the form `\x . b` where `b` is itself smaller than `r`.

## Possible changes / extensions

Also known as "acknowledgment of unsupported features".

### Simple

The following should require fairly minimal changes, or changes which are not
too involved:
- Change the syntax to be closer to Coq:
  - `case v of C -> ...` ↦ `match v with C => ...`
  - `someF : T -> U; someF = \t . ...` ↦ `Definition someF (t: T): U := ...`
  - etc.
- Support uniform type parameters;
- Support `if-then-else`;
- Relax the "smaller" relation;
- Remove the `=`, `Refl`, `subst`, and `contra` builtins.
  The language can already encode them (see [Eq.pi](pi/Logic/Eq.pi) and
  [Contra.pi](pi/Examples/Contra.pi));

### Advanced

Some more advanced feature of Coq which are not supported are:
- Support universe polymorphism;
- Better patterns (relax ordering, top-level wildcard/default case, nested
  patterns, etc.); this might require/justify moving to an elaboration approach;
- Add co-inductive types;
- Support implicit parameters;
- Add Typeclasses.