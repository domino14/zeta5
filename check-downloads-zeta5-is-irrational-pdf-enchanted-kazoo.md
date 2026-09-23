# Plan: Checking "ζ(5) is irrational" (Fauzan, 17 Sep 2026) with computation and Lean 4

## Context
The paper (32 pp.) builds integer polynomials Q_n = Q_{40n,200} of degree 37n with
0 < Q_n(ζ(5)) < exp(−139n²/5), which forces irrationality. The proof has these parts:

| Part | Content | Kind of math | Risk of a hidden error |
|---|---|---|---|
| §1, §7 | Thm 2.1 ⇒ Thm 1.1 (bⁿQ(a/b) is a positive integer tending to 0) | elementary | very low |
| §2 | Functional μ_X via Bernoulli numbers; Hankel matrix G_K; leading coefficient (2.9); positivity via the weight w(y) (Prop 2.2) | Hermite/Hurwitz-zeta integrals, Euler's formula | low–medium |
| §3 | p-adic functional τ, Tate-algebra extension (Lemma 3.1), distribution formula (Lemma 3.2), small-prime bound (3.12) | p-adic analysis, Bernoulli/von Staudt | **medium–high** |
| §4 | Inner-range basis and weights (Prop 4.1); outer range with a rank correction (Lemma 4.2, Prop 4.3) | intricate valuation bookkeeping | **high** (dense proofs, many "one checks") |
| §5 | Normalization m_{K,M}; limit functions Γ, N, R, R₀; the PNT turns sums into integrals; tail bounds | analytic number theory + piecewise-affine calculus | **medium–high** (uniformity claims in (5.7)) |
| §6 | Andréief identity; zero-mass log-energy (Lemma 6.2); 16-arcsine comparison measure | potential theory + real analysis | medium |
| App. A/B | Exact rationals (Tables 1–4, margins in (7.2)), interval enclosures for log/arctan | pure computation | low but easy to check mechanically |
| App. C | Irrationality exponent ≤ 260 | not needed for Thm 1.1 | skip at first |

The margin is small. −1600(A₂₀₀+U) − 139/5 ≈ 0.052, which is about 0.2% of 27.8. A small constant error in §4 or §5 could erase it, so those sections deserve the most scrutiny.

**What Lean can and can't do here:**
- A full Lean proof would settle correctness, but only relative to the Lean statement, so the statement has to be written faithfully: `Irrational (riemannZeta 5).re` (or the equivalent over ℝ).
- Lean won't point to an error on its own. An error shows up as a lemma that can't be proved, or as a counterexample found while formalizing.
- A full formalization of this paper is a multi-month expert project. Mathlib is missing: an asymptotic PNT (it exists in the external *PrimeNumberTheoremAnd* project), Hermite's formula for Hurwitz ζ, Andréief's identity, logarithmic potential theory and the arcsine-measure potentials. It has riemannZeta, Bernoulli numbers, ℚ_p/ℤ_p, determinants, Vandermonde and measure theory.
- The fastest way to find errors is **computation first, then Lean from the top down**, spending effort where the risk is highest.

## Phase 0: What you need to install
1. `brew install poppler`: PDF tools, so the paper can be read and re-read reliably.
2. Python tooling for exact and multiprecision checks: `python3 -m venv ~/zeta5/.venv && ~/zeta5/.venv/bin/pip install sympy mpmath python-flint`. SageMath or PARI/GP is optional but helpful for p-adic work (`brew install pari`).
3. Lean 4 plus Mathlib:
   - `curl https://elan.lean-lang.org/elan-init.sh -sSf | sh` (installs the toolchain manager elan, plus `lean` and `lake`)
   - `cd ~/zeta5 && lake new Zeta5 math && cd Zeta5 && lake exe cache get` (downloads prebuilt Mathlib, a few GB)
   - VS Code with the "Lean 4" extension to work on it interactively.
4. Optional: `pip install leanblueprint` for a dependency-graph "blueprint" of the paper's lemmas.

## Phase 1: Computational checks (days; most likely to catch an error)
Scripts go in `~/zeta5/checks/`, using exact rationals everywhere possible.
1. **Appendix B and constants.** Recompute (5.18) from R(x) over the 143 intervals, then I_out = 127751/96000, A*, A₂₀₀, A₁₀₀₀₀₀, U and the exact margins in (7.2). Also check the cancellation identity 2λ−12λα+2(H²−H−λ²)−18α²+6α = 0, Σc_j = 37/40 and λM₀ = −49173/8000.
2. **Appendix A.** Check (A.2) for I(ρ), C* in (6.3), and the bound (A.9), B(l,r) < −6.645002, on every Table 2 interval. Use interval arithmetic with mpmath `iv` or python-flint `arb`. Also do a dense independent scan of 2U_ρ(t) − V(t) ≤ −1329/200 on [0, ∞).
3. **§2 identities at small K (for example N=3, K=40, h=37, and several smaller analogues).**
   - Build G_K(X) exactly in ℚ[X].
   - Check the leading coefficient (2.9).
   - Check Prop 2.2 numerically: μ_{ζ(5)}(tᵉ) and μ_{ζ(5)}(1/(t+j²)) against ∫R(y²)w(y)dy with mpmath at 50 digits.
   - Check that G_K(ζ(5)) is positive definite.
4. **§3 identities.** Check the pullback identity (3.1), the reflection and difference identities (3.2) and (3.3), and the distribution formula (3.7) for small p, using p-adic truncations.
5. **Valuation bounds at feasible sizes.**
   - Test (3.12) for every prime and small K, using the exact F_K.
   - Test the ingredients of Props 4.1 and 4.3. The stated hypotheses (K ≥ 200M², M ≥ 40) are far too large to compute directly. Instead, check the per-entry bounds (4.2), (4.3) and (4.12) on individual matrix entries in the new bases at moderate p and K. Also check Lemma 4.2 on random matrices.
   - This is evidence, not proof, but a violated entry bound would be decisive.
6. **(5.7) uniformity.** For moderately large K (10⁴–10⁶), compute γ_p^in and v_p(S_K) straight from the definitions (4.4)–(4.8) and (5.3). No determinant is needed; this is pure combinatorics. Compare them with pΓ(K/p) and pN(K/p), and look for a drifting error.

## Phase 2: Lean skeleton (about a week)
In `~/zeta5/Zeta5/`:
1. `Zeta5/Main.lean`: state `theorem zeta5_irrational : Irrational (riemannZeta 5).re` (and check the imaginary part is 0). Prove it **completely** from a `sorry`'d `Theorem 2.1` (a sequence Q_n ∈ ℤ[X], deg ≤ 37n, with 0 < Q_n(ζ5) < exp(−139n²/5) eventually). This is short and checks the top-level logic.
2. `Zeta5/Defs.lean`: formal definitions of μ_X, G_K, Δ_K, S_K, F_K and m_{K,M}. This step alone forces every definition in the paper to be unambiguous, and is often where hidden issues surface.
3. One file per section, with every numbered lemma or proposition stated and left as `sorry`, plus a blueprint graph of the dependencies.

## Phase 3: Formalize by risk and cost
1. **Cheap and certain:** Appendix B rationals (`norm_num` / `decide`), the §7 combination, and Lemma 4.2 (pure linear algebra over a valuation).
2. **Highest risk:** §4 (Props 4.1 and 4.3) and Lemmas 3.1–3.3. These are finite algebra over ℤ_p and need no analysis.
3. **§5 prime sum:** import PrimeNumberTheoremAnd for the asymptotic PNT; the piecewise-affine integrals are mechanical.
4. **Analysis:** Prop 2.2 (needs Hermite's formula, a sizable side project), Andréief, Lemma 6.2 and Appendix A enclosures (interval arithmetic in Lean is laborious; a trusted external checker is an acceptable interim step).

## Verification / milestones
- Phase 1 passes means every numeric claim and every small-scale identity reproduces. Any mismatch goes to the author as a concrete counterexample.
- `lake build` with no `sorry` in `Main.lean` other than Thm 2.1 means the top-level deduction is formally verified.
- `#print axioms zeta5_irrational` listing only `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`) means the full proof is verified.

## Status (2026-09-23)
- **Phase 1: done, all passing.** Scripts: `check_constants.py` (1.1), `check_appendixA.py` (1.2), `check_prop22.py` + `check_determinant.py 40 80` (1.3), `check_section3.py` (1.4), `check_local.py` + `check_determinant.py` (1.5), `check_uniformity.py` (1.6). Caveats: the (A.9) margin is only 6.9e-7, and the inner entry bounds are tested only below K ≥ 200M². Details in `Zeta5/NOTES.md`.
- **Phase 2: done.** `lake build` succeeds. `Main.lean` proves Thm 1.1 from Thm 2.1 with no `sorry`. Thm 2.1, (7.1) and (2.7) are *assembled* from the section lemmas in `Section7.lean`. The Appendix B rationals and margins are proved by `norm_num`. All other numbered results are stated with a `sorry` proof. See `Zeta5/NOTES.md` for the dependency graph and the ambiguities found (notably the zero-class rows of the outer basis).
- **Phase 3: started.** Lemma 4.2 is fully proved (via row-multilinear expansion, not complementary minors), along with the Gauss-valuation toolkit (`Valuation.lean`) and the bookkeeping lemmas (4.4), `γ_in ∈ ℤ`, the (4.1)/(4.9) consequences, `m_{K,M} > 0`, and `G_K` affine in X. 59 `sorry`s remain (from 66).
- **Phase 3 (continued):** the whole small-prime chain is proved: (3.1) pullback → Lemma 3.3 (with (3.8), (3.9)) → (3.11) → (3.12), plus `G_eq_cancelled`. 52 `sorry`s remain. Next highest-risk targets: Props 4.1 and 4.3 (§4), Lemmas 3.1 and 3.2.
- **Phase 3 (continued):** **Prop 4.3 is proved.** That includes (4.10), (4.11), (4.12), (4.14) and the κ/µ von Staudt–Clausen bounds. 44 `sorry`s remain. Next: the inner range (Prop 4.1 and Lemmas 3.1, 3.2), and Prop 4.3 for p > K.
- **Phase 3 (continued):** **Prop 4.1 is proved** (inner range), together with Lemma 3.1 (far-pole form), Lemma 3.2, `C_p ∈ p⁵ℤ_p` and Prop 4.3 for p > K. Sections 3 and 4 are now complete apart from three identities not used by the main line. 36 `sorry`s remain, in §2 (Prop 2.2, (2.9)), §5 (PNT, integrals), §6 (analysis) and Appendix A. Next: Prop 5.1 (integrality), which now follows from (3.12) and Props 4.1 and 4.3.
- 2026-09-23: Phase 3 main line complete. `zeta5_irrational` depends only on propext, Classical.choice, Quot.sound (PNT ported from PrimeNumberTheoremAnd). 4 off-path sorries remain (§3 ×3, §4 ×1).
