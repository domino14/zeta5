import Zeta5.OuterEntries
import Zeta5.OuterCount
import Zeta5.CRTBasis
import Zeta5.SmallPrimes
import Zeta5.Lemma42

/-!
# Proposition 4.3, assembled

Change to the outer basis (unimodular by `outerBasis_unimodular'`), split `G = A + p⁻¹L` by
(4.10), bound the entries by (4.12), apply Lemma 4.2, and identify the bound with `γ_p^out`
(`gammaOut_eq_sum'`).
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Linearity of `µ⁰_X` -/

theorem muModPoly_add (P Q : ℚ[X]) : muModPoly p (P + Q) = muModPoly p P + muModPoly p Q := by
  unfold muModPoly
  exact sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

theorem muModPoly_C_mul (c : ℚ) (P : ℚ[X]) : muModPoly p (C c * P) = c * muModPoly p P := by
  unfold muModPoly
  rw [← smul_eq_C_mul, sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum, Polynomial.sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem muXmod_add (S : Finset ℕ) (P Q : ℚ[X]) :
    muXmod p S (P + Q) = muXmod p S P + muXmod p S Q := by
  rw [muXmod_def, muXmod_def, muXmod_def, add_divByMonic, muModPoly_add, C_add]
  unfold sqResidue
  simp only [eval_add, add_div, C_add, add_mul, sum_add_distrib]
  ring

theorem muXmod_C_mul (S : Finset ℕ) (c : ℚ) (P : ℚ[X]) :
    muXmod p S (C c * P) = C c * muXmod p S P := by
  rw [muXmod_def, muXmod_def, ← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul, muModPoly_C_mul,
    C_mul, mul_add, Finset.mul_sum]
  unfold sqResidue
  simp only [eval_smul, smul_eq_mul, C_mul, mul_div_assoc]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem muXmod_sum (S : Finset ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    muXmod p S (∑ i ∈ s, f i) = ∑ i ∈ s, muXmod p S (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := muXmod_C_mul (p := p) S 0 0
    simpa using this
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, muXmod_add, ih]

/-! ## The outer basis as a coefficient matrix -/

theorem card_tailPoles {K : ℕ} (hK : 40 ∣ K) : (tailPoles K).card = hof K := by
  unfold tailPoles; rw [Nat.card_Icc]; unfold hof Nof; omega

theorem outerBasis_natDegree_lt {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) (x : OuterIdx K p) :
    (outerBasis K p x).natDegree < hof K := by
  have hodd := OuterHyp.odd hK h
  have hpodd : p % 2 = 1 := by omega
  set Ca := outerClassPoles K p x.1
  have hsub : Ca ⊆ tailPoles K := class_subset_tail K p _
  have hcnt : Ca.card ≤ hof K := (card_le_card hsub).trans (card_tailPoles hK).le
  have hxi : (x.2 : ℕ) < Ca.card := x.2.2
  have hoq : (oq K p x).natDegree ≤ x.2 := by
    unfold oq
    split_ifs with h0 h1
    · refine natDegree_pow_le.trans ?_
      rw [natDegree_X_add_C, mul_one]
    · refine natDegree_pow_le.trans ?_
      rw [natDegree_X_add_C, mul_one]
    · have hE := card_E_add_two hpodd h (Nat.one_le_iff_ne_zero.mpr h0) (Nat.lt_succ_iff.mp x.1.2)
      refine natDegree_mul_le.trans ?_
      rw [sqPoleProd_natDegree]
      refine (Nat.add_le_add (le_refl _) natDegree_pow_le).trans ?_
      simp only [natDegree_X_add_C, mul_one]
      omega
  rw [outerBasis_eq]
  refine lt_of_le_of_lt (natDegree_mul_le.trans (Nat.add_le_add (le_refl _) hoq)) ?_
  rw [sqPoleProd_natDegree, card_sdiff_of_subset hsub, card_tailPoles hK]
  omega

theorem outerBasis_expand {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) (x : OuterIdx K p) :
    outerBasis K p x = ∑ d : Fin (hof K), C ((outerBasis K p x).coeff d) * X ^ (d : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun d => C ((outerBasis K p x).coeff d) * X ^ d)]
  conv_lhs => rw [as_sum_range' _ _ (outerBasis_natDegree_lt hK h x)]
  simp only [C_mul_X_pow_eq_monomial]

theorem outerBasis_vge (K : ℕ) (x : OuterIdx K p) : vpGge p (outerBasis K p x) 0 := by
  rw [outerBasis_eq]; exact vpGge_mul0 (vpGge_sqPoleProd _) (oq_vge K p x)

/-- The Gram matrix of `µ⁰_X` in the outer basis is `B A Bᵀ`. -/
theorem outerGram_eq_sum {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) (x y : OuterIdx K p) :
    outerGram K p x y = ∑ k : Fin (hof K), ∑ l : Fin (hof K),
      C ((outerBasis K p x).coeff k * (outerBasis K p y).coeff l) * Aout K p k l := by
  rw [outerGram_apply]
  conv_lhs => rw [outerBasis_expand hK h x, outerBasis_expand hK h y]
  rw [mul_assoc, sum_mul_sum, mul_sum, muXmod_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, muXmod_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [show D (Nof K) ^ 6 * (C ((outerBasis K p x).coeff k) * X ^ (k : ℕ) *
      (C ((outerBasis K p y).coeff l) * X ^ (l : ℕ))) =
      C ((outerBasis K p x).coeff k * (outerBasis K p y).coeff l) *
        (D (Nof K) ^ 6 * X ^ ((k : ℕ) + l)) by rw [C_mul, pow_add]; ring, muXmod_C_mul]
  rfl

/-! ## Assembly -/

theorem halfInt_min0 {t : ℚ} (ht : ∃ k : ℤ, 2 * t = k) : ∃ k : ℤ, 2 * min 0 t = k := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨min 0 k, ?_⟩
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 2), mul_zero, hk]
  push_cast; rfl

theorem wOut_halfInt (K p : ℕ) (x : OuterIdx K p) : ∃ k : ℤ, 2 * wOut K p x = k := by
  simp only [wOut]
  by_cases h0 : (x.1 : ℕ) = 0
  · rw [if_pos h0]
    by_cases h1 : outerCount K p 0 = 1
    · rw [if_pos h1]; exact ⟨-1, by norm_num⟩
    · rw [if_neg h1]
      by_cases h2 : (x.2 : ℕ) = 0
      · rw [if_pos h2]; exact ⟨-4, by norm_num⟩
      · rw [if_neg h2]; exact ⟨0, by norm_num⟩
  · rw [if_neg h0]
    by_cases h3 : (x.2 : ℕ) < ell p K x.1 - 2
    · rw [if_pos h3]
      refine halfInt_min0 ?_
      by_cases h4 : (x.1 : ℕ) ≤ Nof K
      · rw [if_pos h4]; exact ⟨2 * (x.2 : ℕ) + 6 - ell p K x.1 - 4, by push_cast; ring⟩
      · rw [if_neg h4]; exact ⟨2 * (x.2 : ℕ) - ell p K x.1 - 4, by push_cast; ring⟩
    · rw [if_neg h3]; exact ⟨0, by norm_num⟩

/-- Multiplying by a `p`-adic unit does not change Gauss-valuation bounds. -/
theorem vpGge_of_unit_mul {u : ℚ} (hu : u ≠ 0) (hv : padicValRat p u = 0) {P : ℚ[X]} {b : ℚ}
    (h : vpGge p (C u * P) b) : vpGge p P b := by
  intro n hn
  have := h n (by rw [coeff_C_mul]; exact mul_ne_zero hu hn)
  rwa [coeff_C_mul, padicValRat.mul hu hn, hv, zero_add] at this

/-- **Proposition 4.3**: under (4.9), `v_p^G(Δ_K) ≥ γ_p^out`. -/
theorem prop_4_3' {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) :
    vpGge p (Delta K) (gammaOut K p) := by
  obtain ⟨L, hGL, hLint, hLrank⟩ := decomp_4_10' hK h
  obtain ⟨e, hdetv, hdet0⟩ := outerBasis_unimodular' hK h
  set Bm : Matrix (Fin (hof K)) (Fin (hof K)) ℚ :=
    Matrix.of fun x d => (outerBasis K p (e.symm x)).coeff d with hBm
  set OG : Matrix (Fin (hof K)) (Fin (hof K)) ℚ[X] :=
    Matrix.of fun x y => outerGram K p (e.symm x) (e.symm y) with hOG
  set L2 := Bm * L * Bm.transpose with hL2
  have hA : Bm.map C * Aout K p * (Bm.map C).transpose = OG := by
    refine Matrix.ext fun x y => ?_
    rw [hOG, Matrix.of_apply, outerGram_eq_sum hK h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hBm, Matrix.of_apply,
      sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [C_mul]; ring
  have hLm : Bm.map C * L.map (fun c => C ((p : ℚ)⁻¹ * c)) * (Bm.map C).transpose =
      L2.map (fun c => C ((p : ℚ)⁻¹ * c)) := by
    have e1 : L.map (fun c => C ((p : ℚ)⁻¹ * c)) = ((p : ℚ)⁻¹ • L).map C := by
      refine Matrix.ext fun i j => ?_; simp
    have e2 : L2.map (fun c => C ((p : ℚ)⁻¹ * c)) = ((p : ℚ)⁻¹ • L2).map C := by
      refine Matrix.ext fun i j => ?_; simp
    rw [e1, e2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hL2,
      Matrix.mul_smul, Matrix.smul_mul]
  have hkey : Bm.map C * G K * (Bm.map C).transpose = OG + L2.map (fun c => C ((p : ℚ)⁻¹ * c)) := by
    rw [hGL, Matrix.mul_add, Matrix.add_mul, hA, hLm]
  have hdetrel : (OG + L2.map (fun c => C ((p : ℚ)⁻¹ * c))).det = C (Bm.det ^ 2) * Delta K := by
    rw [← hkey, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_C_det, Delta]
    simp only [map_pow]; ring
  -- Lemma 4.2
  have hBint : ∀ x d, vge p (Bm x d) 0 := fun x d => outerBasis_vge K (e.symm x) d
  have hLint' : ∀ i j, vge p (L i j) 0 := fun i j hij => by exact_mod_cast hLint i j hij
  have hL2int : ∀ i j, L2 i j ≠ 0 → 0 ≤ padicValRat p (L2 i j) := by
    intro i j hij
    have : vge p (L2 i j) 0 := by
      simp only [hL2, Matrix.mul_apply, Matrix.transpose_apply]
      refine vge_sum _ _ fun l _ => ?_
      have hs : vge p (∑ k, Bm i k * L k l) 0 :=
        vge_sum _ _ fun k _ => by simpa using vge_mul (hBint i k) (hLint' k l)
      simpa using vge_mul hs (hBint j l)
    exact_mod_cast this hij
  have hrank : L2.rank ≤ rOut K p :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hLrank
  have h42 := lemma_4_2 p OG L2 (fun x => wOut K p (e.symm x)) (fun x => wOut_nonpos K p _)
    (fun x => wOut_halfInt K p _) (fun x y => outerGram_entry_bound' hK h _ _) hL2int
    (rOut K p) hrank
  rw [hdetrel] at h42
  have hu : Bm.det ^ 2 ≠ 0 := pow_ne_zero 2 hdet0
  have huv : padicValRat p (Bm.det ^ 2) = 0 := by rw [padicValRat.pow, hdetv, mul_zero]
  have hΔ := vpGge_of_unit_mul hu huv h42
  refine vpGge_mono hΔ (le_of_eq ?_)
  rw [gammaOut_eq_sum' hK h]
  have hsum : ∑ x, wOut K p (e.symm x) = ∑ y, wOut K p y := Equiv.sum_comp e.symm _
  have hcard : (univ.filter fun x => wOut K p (e.symm x) = 0).card =
      (univ.filter fun y => wOut K p y = 0).card := by
    refine card_bij (fun x _ => e.symm x) (by simp) (fun a _ b _ hab => e.symm.injective hab)
      (fun y hy => ⟨e y, by simpa using hy, by simp⟩)
  rw [hsum, hcard]

end Zeta5