# ζ(5) is irrational: a Lean 4 formalization

This repository is a machine-checked verification, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of the paper *ζ(5) IS IRRATIONAL*
by A. Fauzan (17 Sep 2026). The paper itself is not included.

## The claim

[`Zeta5/Claim.lean`](Zeta5/Claim.lean) states the result using only Mathlib's own definitions:

```lean
example : riemannZeta 5 = ∑' n : ℕ, 1 / (n : ℂ) ^ 5 := zeta_nat_eq_tsum_of_gt_one (by norm_num)

example : (riemannZeta 5).im = 0 := Zeta5.riemannZeta_five_im

theorem zeta5_is_irrational : Irrational (riemannZeta 5).re :=
  Zeta5.riemannZeta_five_irrational

#print axioms zeta5_is_irrational
```

`riemannZeta` is Mathlib's Riemann zeta function and `Irrational` is Mathlib's predicate. None of
this project's definitions appear in the statement. They are used only inside the proof, so a
mistranscribed definition would make the proof fail; it could not make a false claim check.

## Checking it yourself

1. Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager. It reads
   `Zeta5/lean-toolchain` and fetches the right Lean version automatically.

   ```sh
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   source ~/.elan/env          # or open a new terminal
   ```

2. Build and check:

   ```sh
   git clone https://github.com/domino14/zeta5.git
   cd zeta5/Zeta5
   lake exe cache get          # prebuilt Mathlib; without it Mathlib compiles from source for hours
   lake build                  # the proof itself, ~10 minutes
   lake env lean Claim.lean
   ```

3. The last command should print:

   ```
   'zeta5_is_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   These are Lean's three standard axioms: propositional extensionality, the axiom of choice and
   quotient soundness. Any gap left in the proof (a `sorry`) would add `sorryAx` to this list. CI
   runs the same check on every push.

### Independent kernel replay

`#print axioms` trusts the compiled files. A stronger check re-runs every proof through Lean's
kernel from scratch:

```sh
for m in $(find Zeta5 -name "*.lean" | sed 's/\.lean$//; s|/|.|g'); do lake env leanchecker $m || echo "FAIL $m"; done
```

This prints nothing on success and takes about 7 minutes. Don't run it on the root module
`Zeta5`: that file contains only `import` lines, and checking it uses more than 30 GB of RAM.

If you get `lake: command not found`, `~/.elan/bin` is not on your `PATH`. Run
`source ~/.elan/env`.

## What's in here

| Path | Contents |
|---|---|
| `Zeta5/Claim.lean` | The statement above, and the axiom check |
| `Zeta5/Zeta5/Defs.lean` | All definitions transcribed from the paper |
| `Zeta5/Zeta5/Section2.lean` … `Section7.lean`, `AppendixA/B.lean` | The paper's statements, section by section |
| `Zeta5/Zeta5/*.lean` (others) | The proofs, one file per lemma or proposition |
| `Zeta5/Zeta5/Main.lean` | Theorem 1.1 (`zeta5_irrational`) |
| `Zeta5/Zeta5/PNTPort/` | The prime number theorem, ported from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Apache-2.0, see its `LICENSE`) |
| `Zeta5/NOTES.md` | Blueprint, dependency graph, and findings made during the formalization |
| `checks/` | Python numerical checks of the paper's constants and claims (mpmath, python-flint, sympy) |
| `gen/` | Scripts that generate the long, mechanical Lean files (piecewise integrals, interval checks, the PNT port) |

## Findings

The paper's argument holds up. A few statements needed care; details are in
[`Zeta5/NOTES.md`](Zeta5/NOTES.md):

- **Corrected edge cases.** Several statements as first transcribed were false in edge cases:
  κ-integrality at p = 2, Legendre's formula (5.3) at K = 0, and Lemma 6.2 with point masses.
  The paper's use of each is unaffected.
- **Tight margins.** The Appendix A bound (6.4) holds with only about 6.5·10⁻⁸ to spare, and
  (5.16) is also tight. Both are proved with rigorous interval bounds.
- **Remaining `sorry`s.** Four remain, in `Section3.lean` and `Section4.lean`. They are side
  statements of the paper that the main theorem does not use, as the axiom check confirms.
