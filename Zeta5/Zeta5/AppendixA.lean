import Zeta5.Section6

/-!
# Appendix A: the measure and its elementary bounds

Statements of the nesting/length properties of Table 1, the arcsine potential (A.1), the
energy formula (A.2), the half-line bound (A.9) and the enclosures (A.10).

The rational facts about Table 1 are proved here by computation. The analytic statements are
`sorry`. Phase 1.2 of the plan (an interval-arithmetic check of (A.2), (A.9) and (A.10)) has
not been done yet.
-/

open Finset MeasureTheory

noncomputable section

namespace Zeta5

/-- `∑ c_j = 37/40 · 10¹²`: the mass of `ρ` is `λ`. -/
theorem table1_sum_c : (table1.map fun e => e.2.2).sum = 37 * 10 ^ 12 / 40 := by
  decide

/-- Nesting `0 < a₁₆ < ⋯ < a₁ < b₁ < ⋯ < b₁₆ < 2` and `b_j - a_j > 1/225` (scaled by `10¹²`). -/
theorem table1_nested :
    (table1.map fun e => e.1).reverse.Pairwise (· < ·) ∧
      (table1.map fun e => e.2.1).Pairwise (· < ·) ∧
      (∀ e ∈ table1, 0 < e.1 ∧ e.1 < e.2.1 ∧ e.2.1 < 2 * 10 ^ 12 ∧
        225 * (e.2.1 - e.1) > 10 ^ 12) := by
  decide


/-- The partial masses `S_j = ∑_{i ≤ j} c_i` (as reals). -/
def Spart (j : ℕ) : ℝ := ((table1.take j).map fun e => ((e.2.2 : ℝ) / 10 ^ 12)).sum




/-- The rational step after (A.10). The endpoints combine to exactly `-1366995564511/10¹²`, so the
paper's strict inequality `λM₀ - I(ρ) + C* < -1366995564511/10¹²` comes from the strict
enclosures. -/
theorem A10_combination :
    lam * M0 + 2126593445148 / 10 ^ 12 + 2653035990341 / 10 ^ 12 = -1366995564511 / 10 ^ 12 ∧
      (-1366995564511 / 10 ^ 12 : ℚ) < U := by
  norm_num [lam, M0, U]

-- (A.1), (A.2), (A.9), (A.10) are proved in `Lemma61*.lean`; see `Lemma61Final.lean`.

end Zeta5
