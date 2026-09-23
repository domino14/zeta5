import Zeta5.Prop22

/-!
# §6 The real determinant

Lemma 6.1 (the comparison measure; proved in Appendix A), Lemma 6.2 (zero-mass logarithmic
energy), the configuration bound (6.9), Andréief's identity (6.10) and Proposition 6.3.
-/

open Polynomial Finset MeasureTheory

noncomputable section

namespace Zeta5


/-- Mutual logarithmic energy `∬ log|z - w| dμ(z) dν(w)` on `ℂ`. -/
def logEnergyC (μ ν : Measure ℂ) : ℝ := ∫ z, ∫ w, Real.log ‖z - w‖ ∂ν ∂μ

-- Lemma 6.2 (`lemma_6_2'`, with the diagonal-null hypothesis) is in `Energy6.lean`.


-- Lemma 6.1 is in `Lemma61Final.lean`.
-- (6.9) (`config_bound_6_9`) is in `Config69.lean`.


-- (6.11) (`weight_le'`) is in `Energy6.lean`; (6.10), (6.14), (6.15) and Proposition 6.3 are in
-- `Section6b.lean`.





end Zeta5
