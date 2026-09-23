import Zeta5.Lemma61Check

/-!
# Lemma 6.1 and Appendix A (A.1), (A.2), (A.9), (A.10), under their original names
-/

open Finset MeasureTheory

noncomputable section

namespace Zeta5

/-- (A.1): the potential of the unit arcsine measure. -/
theorem arcsine_potential (a b t : ℝ) (hab : a < b) :
    logPot (arcsine a b) t =
      if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
      else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2) := by
  exact arcsine_potential' a b t hab

/-- (A.2): `I(ρ) = ∑_j (S_j² - S_{j-1}²) log((b_j - a_j)/4)`. -/
theorem energy_A2 :
    logEnergy rho = ∑ j ∈ range 16,
      (Spart (j + 1) ^ 2 - Spart j ^ 2) *
        Real.log ((((table1.getD j (0, 0, 0)).2.1 : ℝ) - (table1.getD j (0, 0, 0)).1)
          / 10 ^ 12 / 4) := by
  exact energy_A2'

/-- (A.9), with (6.8) for `t ≥ 2`: `2U^ρ(t) - V(t) < -6645002/10⁶ < M₀` for `t ≥ 0`. -/
theorem potential_A9 (t : ℝ) (ht : 0 ≤ t) : 2 * logPot rho t - V t < -6645002 / 10 ^ 6 := by
  exact potential_A9' t ht

/-- (A.10): the enclosures of `I(ρ)` and `C*`. -/
theorem enclosures_A10 :
    -2126593445148 / 10 ^ 12 < logEnergy rho ∧ logEnergy rho < -2126593445147 / 10 ^ 12 ∧
      2653035990340 / 10 ^ 12 < Cstar ∧ Cstar < 2653035990341 / 10 ^ 12 := by
  exact enclosures_A10'

/-- Lemma 6.1: `ρ` has mass `λ`, is supported in `(0, 2)`, and satisfies
`2U^ρ(t) - V(t) ≤ M₀` for `t ≥ 0` (6.2) and `λM₀ - I(ρ) + C* ≤ U` (6.4). -/
theorem lemma_6_1 :
    rho Set.univ = ENNReal.ofReal (Lim.lam) ∧ rho (Set.Ioo 0 2)ᶜ = 0 ∧
      (∀ t : ℝ, 0 ≤ t → 2 * logPot rho t - V t ≤ M0) ∧
      (Lim.lam * M0 - logEnergy rho + Cstar ≤ U) := by
  exact lemma_6_1'

end Zeta5
