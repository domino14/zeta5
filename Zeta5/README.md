# Zeta5: a Lean 4 formalization of "ζ(5) is irrational"

A machine-checked verification of the paper *ζ(5) IS IRRATIONAL* (A. Fauzan, 17 Sep 2026), in
Lean 4 + Mathlib.

## The claim

`Claim.lean` states the result using only Mathlib's own definitions (`riemannZeta`, `Irrational`):

```lean
theorem zeta5_is_irrational : Irrational (riemannZeta 5).re
```

together with `(riemannZeta 5).im = 0`, and prints the axioms the proof depends on.

## Checking it

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager).

```sh
cd Zeta5
lake exe cache get      # download prebuilt Mathlib (otherwise Mathlib builds from source: hours)
lake build              # build the whole proof (~10 min; Lemma61Check alone takes ~4 min)
lake env lean Claim.lean
```

Expected output of the last command:

```
'zeta5_is_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. If any step of the proof were missing, `sorryAx` would
appear in the list.

## Layout

See `NOTES.md` for the blueprint, the file-by-file map, the dependency graph, and the findings
made while formalizing the paper, including statements that had to be corrected.

`Zeta5/PNTPort/` contains the prime number theorem, ported from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Apache-2.0;
see `Zeta5/PNTPort/LICENSE`).

Four `sorry`s remain in `Section3.lean` and `Section4.lean`. They are side statements of the
paper that the main theorem does not use, as the axiom check above confirms.
