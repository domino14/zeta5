import Zeta5.Section2
import Zeta5.Functionals

/-!
# (2.9): degree and leading coefficient of `Δ_K`
-/

open Polynomial Finset Matrix

noncomputable section

namespace Zeta5

/-- The constant and `X`-coefficients of `G_K`. -/
def GA (K : ℕ) : Matrix (Fin (hof K)) (Fin (hof K)) ℚ := Matrix.of fun i l => (G K i l).coeff 0
def GB (K : ℕ) : Matrix (Fin (hof K)) (Fin (hof K)) ℚ := Matrix.of fun i l => (G K i l).coeff 1

theorem Delta_eq_det_affine (K : ℕ) :
    Delta K = det ((X : ℚ[X]) • (GB K).map C + (GA K).map C) := by
  unfold Delta
  congr 1
  ext i l : 1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, GA, GB, Matrix.of_apply,
    smul_eq_mul]
  rw [eq_X_add_C_of_natDegree_le_one (G_entry_natDegree_le K i l)]
  simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C_zero, coeff_X_zero, coeff_C, mul_one,
    mul_zero, zero_add, one_ne_zero, if_false, add_zero, if_true]
  ring

theorem muPole_coeff_one (j : ℕ) : (muPole j).coeff 1 = (j : ℚ) ^ 4 := by
  unfold muPole
  rw [coeff_add, coeff_sub, coeff_C_mul, coeff_sub, coeff_X_one, coeff_C, coeff_C, coeff_C]
  simp

/-- The residue weight at the pole `j`. -/
def wt (K j : ℕ) : ℚ :=
  (j : ℚ) ^ 4 * ((D (Nof K)).eval (-(j : ℚ) ^ 2)) ^ 5 /
    ∏ k ∈ (Icc (Nof K + 1) K).erase j, ((k : ℚ) ^ 2 - (j : ℚ) ^ 2)

theorem GB_apply (K : ℕ) (i l : Fin (hof K)) :
    GB K i l = ∑ j ∈ Icc (Nof K + 1) K, (-(j : ℚ) ^ 2) ^ (i : ℕ) * (-(j : ℚ) ^ 2) ^ (l : ℕ) * wt K j := by
  simp only [GB, Matrix.of_apply]
  rw [G_eq_cancelled, muX, coeff_add, coeff_C, if_neg one_ne_zero, zero_add, finsetSum_coeff]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, muPole_coeff_one, sqResidue, wt]
  simp only [eval_mul, eval_pow, eval_X]
  ring

/-! ## A Vandermonde sign identity -/

theorem sum_card_Ioi (n : ℕ) : ∑ t : Fin n, (Ioi t).card = n * (n - 1) / 2 := by
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun t => n - 1 - t) n, ← sum_range_id]
  exact sum_range_reflect (fun t => t) n

theorem prod_erase_sub (n : ℕ) (v : Fin n → ℚ) :
    ∏ t, ∏ s ∈ univ.erase t, (v t - v s) = (-1) ^ (n * (n - 1) / 2) * det (vandermonde v) ^ 2 := by
  rw [det_vandermonde]
  have hsplit : ∀ t : Fin n, univ.erase t = Iio t ∪ Ioi t := by
    intro t; ext s; simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : ∀ t : Fin n, Disjoint (Iio t) (Ioi t) := by
    intro t; rw [Finset.disjoint_left]; intro s h1 h2; simp only [mem_Iio, mem_Ioi] at h1 h2; omega
  have e1 : ∏ t, ∏ s ∈ univ.erase t, (v t - v s) =
      (∏ t, ∏ s ∈ Iio t, (v t - v s)) * ∏ t, ∏ s ∈ Ioi t, (v t - v s) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun t _ => by rw [hsplit, prod_union (hdisj t)]
  have e2 : ∏ t, ∏ s ∈ Iio t, (v t - v s) = ∏ i, ∏ j ∈ Ioi i, (v j - v i) := by
    refine prod_comm' fun t s => ?_
    simp only [mem_univ, true_and, and_true, mem_Iio, mem_Ioi]
  have e3 : ∏ t, ∏ s ∈ Ioi t, (v t - v s) =
      (-1) ^ (n * (n - 1) / 2) * ∏ i, ∏ j ∈ Ioi i, (v j - v i) := by
    rw [← sum_card_Ioi, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun t _ => ?_
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun s _ => by ring
  rw [e1, e2, e3]; ring

/-! ## The determinant of the `X`-coefficient matrix -/

section Main

variable {K : ℕ} (hK : 40 ∣ K)
include hK

theorem hof_eq : hof K = K - Nof K := by unfold hof Nof; omega

/-- The poles `x_t = N + 1 + t`. -/
def xpole (K : ℕ) (t : Fin (hof K)) : ℕ := Nof K + 1 + (t : ℕ)

omit hK in
theorem xpole_inj : Function.Injective (xpole K) := fun a b h => by
  unfold xpole at h; exact Fin.ext (by omega)

theorem Icc_eq_image : Icc (Nof K + 1) K = (univ : Finset (Fin (hof K))).image (xpole K) := by
  have hh := hof_eq hK
  ext j
  simp only [mem_Icc, mem_image, mem_univ, true_and, xpole]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨j - (Nof K + 1), by omega⟩, by simp; omega⟩
  · rintro ⟨t, rfl⟩; have := t.2; omega

omit hK in
theorem D_eval_ne_zero {j : ℕ} (hj : Nof K < j) : (D (Nof K)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [D, eval_prod]
  refine prod_ne_zero_iff.mpr fun i hi => ?_
  rw [mem_Icc] at hi
  simp only [eval_add, eval_X, eval_C]
  intro h0
  have : (i : ℚ) ^ 2 = (j : ℚ) ^ 2 := by linarith
  have := (pow_left_inj₀ (Nat.cast_nonneg i) (Nat.cast_nonneg j) two_ne_zero).mp this
  have : i = j := by exact_mod_cast this
  omega

theorem det_GB :
    det (GB K) = (-1) ^ (hof K * (hof K - 1) / 2) *
      ∏ j ∈ Icc (Nof K + 1) K, (j : ℚ) ^ 4 * ((D (Nof K)).eval (-(j : ℚ) ^ 2)) ^ 5 := by
  set v : Fin (hof K) → ℚ := fun t => -((xpole K t : ℚ)) ^ 2 with hv
  have hvinj : Function.Injective v := by
    intro a b hab
    simp only [hv, neg_inj] at hab
    have := (pow_left_inj₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) two_ne_zero).mp hab
    exact xpole_inj (by exact_mod_cast this)
  have hGB : GB K = (vandermonde v).transpose * diagonal (fun t => wt K (xpole K t)) *
      vandermonde v := by
    ext i l
    rw [GB_apply, Icc_eq_image hK, sum_image fun a _ b _ h => xpole_inj h, Matrix.mul_apply]
    refine sum_congr rfl fun t _ => ?_
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, vandermonde_apply, hv]
    ring
  have hV : det (vandermonde v) ≠ 0 := by
    rw [Ne, det_vandermonde_eq_zero_iff]
    rintro ⟨i, j, h1, h2⟩; exact h2 (hvinj h1)
  have hden : ∀ t : Fin (hof K), ∏ k ∈ (Icc (Nof K + 1) K).erase (xpole K t),
      ((k : ℚ) ^ 2 - (xpole K t : ℚ) ^ 2) = ∏ s ∈ univ.erase t, (v t - v s) := by
    intro t
    rw [Icc_eq_image hK, ← image_erase xpole_inj, prod_image fun a _ b _ h => xpole_inj h]
    exact prod_congr rfl fun s _ => by simp only [hv]; ring
  have hnum : ∏ t : Fin (hof K), (xpole K t : ℚ) ^ 4 * ((D (Nof K)).eval (-(xpole K t : ℚ) ^ 2)) ^ 5
      = ∏ j ∈ Icc (Nof K + 1) K, (j : ℚ) ^ 4 * ((D (Nof K)).eval (-(j : ℚ) ^ 2)) ^ 5 := by
    rw [Icc_eq_image hK, prod_image fun a _ b _ h => xpole_inj h]
  have hwt : ∏ t : Fin (hof K), wt K (xpole K t) =
      (∏ t : Fin (hof K), (xpole K t : ℚ) ^ 4 * ((D (Nof K)).eval (-(xpole K t : ℚ) ^ 2)) ^ 5) /
        ((-1) ^ (hof K * (hof K - 1) / 2) * det (vandermonde v) ^ 2) := by
    unfold wt
    rw [prod_div_distrib, ← prod_erase_sub]
    congr 1
    exact prod_congr rfl fun t _ => hden t
  rw [hGB, det_mul, det_mul, det_transpose, det_diagonal, hwt, hnum]
  have hs : ((-1 : ℚ) ^ (hof K * (hof K - 1) / 2)) * ((-1 : ℚ) ^ (hof K * (hof K - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  set P := ∏ j ∈ Icc (Nof K + 1) K, (j : ℚ) ^ 4 * ((D (Nof K)).eval (-(j : ℚ) ^ 2)) ^ 5
  set sg := ((-1 : ℚ) ^ (hof K * (hof K - 1) / 2))
  have hs0 : sg ≠ 0 := by simp [sg]
  calc det (vandermonde v) * (P / (sg * det (vandermonde v) ^ 2)) * det (vandermonde v)
      = P / sg := by field_simp
    _ = sg * P := by rw [div_eq_iff hs0]; linear_combination (-P) * hs

end Main

/-- **(2.9)**: `Δ_K` has degree `h` and leading coefficient
`(-1)^{h(h-1)/2} ∏_{j=N+1}^K j⁴ D_N(-j²)⁵`. -/
theorem Delta_natDegree_leadingCoeff' (K : ℕ) (hK : 40 ∣ K) :
    (Delta K).natDegree = hof K ∧
      (Delta K).leadingCoeff =
        (-1) ^ (hof K * (hof K - 1) / 2) *
          ∏ j ∈ Icc (Nof K + 1) K, (j : ℚ) ^ 4 * ((D (Nof K)).eval (-(j : ℚ) ^ 2)) ^ 5 := by
  have hdet := det_GB hK
  have hne : det (GB K) ≠ 0 := by
    rw [hdet]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_ne_zero_iff.mpr fun j hj => ?_)
    rw [mem_Icc] at hj
    refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (show j ≠ 0 by omega)))
      (pow_ne_zero _ (D_eval_ne_zero (by omega)))
  have hle := natDegree_det_X_add_C_le (GB K) (GA K)
  have hc := coeff_det_X_add_C_card (GB K) (GA K)
  rw [Fintype.card_fin] at hle hc
  rw [Delta_eq_det_affine]
  have hdeg : (det ((X : ℚ[X]) • (GB K).map C + (GA K).map C)).natDegree = hof K :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact hne))
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg, hc, hdet]

/-- **(2.9)**: `Δ_K` has degree `h` and leading coefficient
`(-1)^{h(h-1)/2} ∏_{j=N+1}^K j⁴ D_N(-j²)⁵`. -/
theorem Delta_natDegree_leadingCoeff (K : ℕ) (hK : 40 ∣ K) :
    (Delta K).natDegree = hof K ∧
      (Delta K).leadingCoeff =
        (-1) ^ (hof K * (hof K - 1) / 2) *
          ∏ j ∈ Icc (Nof K + 1) K, (j : ℚ) ^ 4 * ((D (Nof K)).eval (-(j : ℚ) ^ 2)) ^ 5 :=
  Delta_natDegree_leadingCoeff' K hK

end Zeta5
