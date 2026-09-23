import Zeta5.Functionals

/-!
# §2 The determinant construction

Statements of (2.9) (degree and leading coefficient) and Proposition 2.2 (positive integral
representation), plus the well-definedness facts about `muX` that the paper uses silently.
-/

open Polynomial Finset MeasureTheory

noncomputable section

namespace Zeta5

-- Well-definedness of `µ_X` (`muX_mul_cancel`, `muX_mul_cancel_set`) is in `Functionals.lean`.

/-- `G_K` may equivalently be computed with the cancelled denominator `D_K / D_N` and numerator
`D_N⁵`. This is how `checks/check_determinant.py` builds it. -/
theorem G_eq_cancelled (K : ℕ) (i j : Fin (hof K)) :
    G K i j = muX (Icc (Nof K + 1) K) (D (Nof K) ^ 5 * X ^ ((i : ℕ) + j)) := by
  have hU : Icc 1 K = Icc 1 (Nof K) ∪ Icc (Nof K + 1) K := by
    ext x; simp only [mem_Icc, mem_union]; unfold Nof; omega
  have hd : Disjoint (Icc 1 (Nof K)) (Icc (Nof K + 1) K) := by
    rw [Finset.disjoint_left]; intro x hx hx'; simp only [mem_Icc] at hx hx'; omega
  simp only [G, Matrix.of_apply]
  rw [hU, ← muX_mul_cancel_set _ _ hd]
  congr 1
  simp only [D, sqPoleProd]
  ring

/-- `G_K(X)` has entries affine in `X`. -/
theorem muX_natDegree_le (S : Finset ℕ) (P : ℚ[X]) : (muX S P).natDegree ≤ 1 := by
  unfold muX
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans ?_
  unfold muPole
  compute_degree!

theorem G_entry_natDegree_le (K : ℕ) (i j : Fin (hof K)) : (G K i j).natDegree ≤ 1 :=
  muX_natDegree_le _ _

-- (2.9) `Delta_natDegree_leadingCoeff` is in `Degree29.lean`.






-- Proposition 2.2, `weight_pos` and the positivity statements are in `Prop22.lean`.

end Zeta5
