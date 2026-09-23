import Zeta5

/-!
# The claim

`riemannZeta` is Mathlib's Riemann zeta function `ℂ → ℂ`, and `Irrational` is Mathlib's
predicate on `ℝ`. Nothing from this project appears in the statements below: every project
definition is internal to the proof.

Check with (from this directory):

    lake env lean Claim.lean
-/

/-- Mathlib's `riemannZeta 5` is the familiar series `∑_{n ≥ 1} 1/n⁵`. (The `n = 0` term is
`1/0 = 0` in Lean.) -/
example : riemannZeta 5 = ∑' n : ℕ, 1 / (n : ℂ) ^ 5 :=
  zeta_nat_eq_tsum_of_gt_one (by norm_num)

/-- ζ(5) is real. -/
example : (riemannZeta 5).im = 0 := Zeta5.riemannZeta_five_im

/-- ζ(5) is irrational. -/
theorem zeta5_is_irrational : Irrational (riemannZeta 5).re :=
  Zeta5.riemannZeta_five_irrational

-- Should print only `[propext, Classical.choice, Quot.sound]`; a `sorryAx` here would mean
-- the proof is incomplete.
#print axioms zeta5_is_irrational
