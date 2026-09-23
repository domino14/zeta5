import Zeta5.Prop43
import Zeta5.CRTBasis
import Zeta5.MuMod

/-!
# Proposition 4.3, second part: `v_p^G(Δ_K) ≥ 0` for `p > K`

For `p > K` every pole is below `p`, each class has at most the two poles `a, p - a`, there is
no polynomial correction (`G = A`), and every entry of the outer Gram matrix is integral.
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

theorem cls_of_lt {j : ℕ} (hj : j < p) : cls p j = min j (p - j) := by
  unfold cls; rw [Nat.mod_eq_of_lt hj]

theorem muX_eq_muXmod_of_lt (S : Finset ℕ) (P : ℚ[X])
    (hdeg : (P /ₘ sqPoleProd S).natDegree < 2 * p - 3) : muX S P = muXmod p S P := by
  rw [muX_eq_muXmod_add (p := p)]
  have : ((P /ₘ sqPoleProd S).sum fun e c => c * cCorr p e) = 0 := by
    rw [Polynomial.sum_def]
    refine sum_eq_zero fun e he => ?_
    rw [cCorr_of_lt (lt_of_le_of_lt (le_natDegree_of_mem_supp e he) hdeg), mul_zero]
  rw [this]; simp

section Large

variable {K : ℕ} (hK : 40 ∣ K) (hK0 : 0 < K) (hpK : K < p)
include hK hK0 hpK

theorem large_K40 : 40 ≤ K := by obtain ⟨n, rfl⟩ := hK; omega

theorem large_odd : p % 2 = 1 := by
  have := large_K40 hK hK0 hpK
  rcases hp.out.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

theorem large_p7 : 7 ≤ p := by have := large_K40 hK hK0 hpK; omega

/-- For `p > K`, class `a ≥ 1` poles are among `a, p - a`. -/
theorem large_class_mem {a j : ℕ} (ha : a ≤ mHalf p) (hj : j ∈ outerClassPoles K p a) :
    (j = a ∨ j = p - a) ∧ Nof K + 1 ≤ j ∧ j ≤ K := by
  have hodd := large_odd hK hK0 hpK
  rw [mem_outerClassPoles_iff hodd ha, mem_Icc] at hj
  obtain ⟨⟨h1, h2⟩, h3⟩ := hj
  rw [cls_of_lt (by omega)] at h3
  refine ⟨?_, h1, h2⟩
  rcases le_total j (p - j) with h' | h' <;> simp only [min_eq_left h', min_eq_right h'] at h3 <;>
    omega

theorem large_ell_le_two {a : ℕ} (ha : a ≤ mHalf p) : ell p K a ≤ 2 := by
  have hodd := large_odd hK hK0 hpK
  unfold ell
  calc _ ≤ ({a, p - a} : Finset ℕ).card := by
        refine card_le_card fun j hj => ?_
        rw [mem_filter, classCond_iff hodd ha, mem_Icc] at hj
        rw [cls_of_lt (by omega)] at hj
        simp only [mem_insert, mem_singleton]
        rcases le_total j (p - j) with h' | h' <;>
          simp only [min_eq_left h', min_eq_right h'] at hj <;> omega
    _ ≤ 2 := card_le_two

theorem large_filter_empty (a : ℕ) : (outerClassPoles K p a).filter (fun j => p < j) = ∅ := by
  rw [filter_eq_empty_iff]
  intro j hj
  have := (mem_filter.mp hj).1
  rw [mem_Icc] at this; omega

theorem large_count_zero : outerCount K p 0 = 0 := by
  unfold outerCount
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro j hj
  rw [outerClassPoles, mem_filter, mem_Icc] at hj
  have hd : p ∣ j := by
    rcases hj.2 with h1 | h1
    · exact Nat.dvd_of_mod_eq_zero (by simpa using h1)
    · exact Nat.dvd_of_mod_eq_zero (by simpa using h1)
  have := Nat.le_of_dvd (by omega) hd; omega

theorem large_ne_zero (x : OuterIdx K p) : (x.1 : ℕ) ≠ 0 := by
  intro h0
  have hc : outerCount K p x.1 = 0 := by rw [h0]; exact large_count_zero hK hK0 hpK
  have := x.2.2; omega

theorem large_oq (x : OuterIdx K p) :
    oq K p x = (X + C (((x.1 : ℕ) : ℚ) ^ 2)) ^ (x.2 : ℕ) := by
  have h0 := large_ne_zero hK hK0 hpK x
  have hl := large_ell_le_two hK hK0 hpK (Nat.lt_succ_iff.mp x.1.2)
  unfold oq
  rw [if_neg h0]
  split_ifs with hi
  · rfl
  · rw [large_filter_empty hK hK0 hpK, sqPoleProd, prod_empty, one_mul,
      show ell p K x.1 - 2 = 0 by omega, Nat.sub_zero]

/-! ## Unimodularity -/

theorem outerBasisZ_mod_large (x : OuterIdx K p) :
    (outerBasisZ K p x).map (Int.castRingHom (ZMod p)) =
      crtFam (rr p) (fun c => outerCount K p c) x := by
  have hodd := large_odd hK hK0 hpK
  obtain ⟨a, i⟩ := x
  unfold outerBasisZ crtFam
  simp only
  split_ifs with h0 hi
  · have ha0 : a = 0 := Fin.ext h0
    subst ha0
    rw [Polynomial.map_mul, Pa_mod hodd, Polynomial.map_pow]
    simp [rr]
  · rw [Polynomial.map_mul, Pa_mod hodd, Polynomial.map_pow, map_X_add_sq]
  · have hl := large_ell_le_two hK hK0 hpK (Nat.lt_succ_iff.mp a.2)
    rw [Polynomial.map_mul, Polynomial.map_mul, Pa_mod hodd, Polynomial.map_pow, sqPoleProdZ_map,
      large_filter_empty hK hK0 hpK, prod_empty, mul_one, map_X_add_sq,
      show ell p K a - 2 = 0 by omega, Nat.sub_zero]

theorem outerBasis_unimodular_large :
    ∃ e : OuterIdx K p ≃ Fin (hof K),
      padicValRat p (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (outerBasis K p (e.symm x)).coeff d).det = 0 ∧
      (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (outerBasis K p (e.symm x)).coeff d).det ≠ 0 := by
  have hp := large_odd hK hK0 hpK
  set e : OuterIdx K p ≃ Fin (hof K) := Fintype.equivFinOfCardEq (card_outerIdx hK hp)
  refine ⟨e, ?_⟩
  set MZ : Matrix (Fin (hof K)) (Fin (hof K)) ℤ :=
    Matrix.of fun x d => (outerBasisZ K p (e.symm x)).coeff d with hMZ
  have hM : (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
      (outerBasis K p (e.symm x)).coeff d) = (Int.castRingHom ℚ).mapMatrix MZ := by
    ext x d; simp [hMZ, outerBasis_eq_map, coeff_map]
  have hdet : (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
      (outerBasis K p (e.symm x)).coeff d).det = ((MZ.det : ℤ) : ℚ) := by
    rw [hM, ← RingHom.map_det]; rfl
  set v := crtFam (rr p) (fun c : Fin (mHalf p + 1) => outerCount K p c) with hv
  set Mp := (Int.castRingHom (ZMod p)).mapMatrix MZ with hMp_def
  have hMp : ∀ x d, Mp x d = (v (e.symm x)).coeff d := by
    intro x d
    rw [hv, ← outerBasisZ_mod_large hK hK0 hpK, coeff_map]; rfl
  have hdetp : Mp.det ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hg0
    have hQ : ∑ x, g x • v (e.symm x) = 0 := by
      ext d
      rw [finsetSum_coeff, coeff_zero]
      by_cases hd : d < hof K
      · have := congrFun hg ⟨d, hd⟩
        simp only [Matrix.vecMul, dotProduct, hMp, Pi.zero_apply] at this
        simpa [coeff_smul] using this
      · refine sum_eq_zero fun x _ => ?_
        have hdeg := crtFam_natDegree_lt (rr p) (fun c : Fin (mHalf p + 1) => outerCount K p c)
          (e.symm x)
        have hsum : ∑ c : Fin (mHalf p + 1), outerCount K p c = hof K := by
          rw [← card_outerIdx hK hp, Fintype.card_sigma]; simp
        rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by rw [hv]; omega), smul_zero]
    have hli := crtFam_linearIndependent (rr p) (rr_injective hp)
      (fun c : Fin (mHalf p + 1) => outerCount K p c)
    rw [Fintype.linearIndependent_iff] at hli
    have h1 : ∑ z, g (e z) • v z = 0 := by
      rw [← hQ, ← Equiv.sum_comp e (fun x => g x • v (e.symm x))]
      simp
    funext y
    have := hli (fun z => g (e z)) h1 (e.symm y)
    simpa using this
  have hmod : ((MZ.det : ℤ) : ZMod p) ≠ 0 := by
    have h1 : ((MZ.det : ℤ) : ZMod p) = Mp.det := by rw [hMp_def, ← RingHom.map_det]; rfl
    rw [h1]; exact hdetp
  have hndvd : ¬ (p : ℤ) ∣ MZ.det := fun hd => hmod ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd)
  refine ⟨?_, ?_⟩
  · rw [hdet, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hndvd]; rfl
  · rw [hdet]
    intro h0
    apply hmod
    have : MZ.det = 0 := by exact_mod_cast h0
    rw [this]; simp

/-! ## No polynomial correction: `G = A` -/

theorem G_eq_Aout_large : G K = Aout K p := by
  have hp7 := large_p7 hK hK0 hpK
  obtain ⟨n, rfl⟩ := hK
  refine Matrix.ext fun i j => ?_
  simp only [G, Aout, Matrix.of_apply]
  apply muX_eq_muXmod_of_lt
  have hi := i.2
  have hj := j.2
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  rw [natDegree_divByMonic _ (sqPoleProd_monic _), sqPoleProd_natDegree, Nat.card_Icc]
  have hdeg : (D (Nof (40 * n)) ^ 6 * X ^ ((i : ℕ) + j)).natDegree ≤ 6 * Nof (40 * n) + (i + j) := by
    refine natDegree_mul_le.trans (add_le_add (natDegree_pow_le.trans ?_) (natDegree_X_pow_le _))
    rw [D_natDeg]
  omega

/-! ## The Gram identity -/

theorem outerBasis_natDegree_lt_large (x : OuterIdx K p) :
    (outerBasis K p x).natDegree < hof K := by
  have hsub : outerClassPoles K p x.1 ⊆ tailPoles K := class_subset_tail K p _
  have hcnt : (outerClassPoles K p x.1).card ≤ hof K :=
    (card_le_card hsub).trans (card_tailPoles hK).le
  have hxi : (x.2 : ℕ) < (outerClassPoles K p x.1).card := x.2.2
  rw [outerBasis_eq, large_oq hK hK0 hpK]
  refine lt_of_le_of_lt (natDegree_mul_le.trans (Nat.add_le_add (le_refl _) natDegree_pow_le)) ?_
  rw [sqPoleProd_natDegree, card_sdiff_of_subset hsub, card_tailPoles hK, natDegree_X_add_C,
    mul_one]
  omega

theorem outerBasis_expand_large (x : OuterIdx K p) :
    outerBasis K p x = ∑ d : Fin (hof K), C ((outerBasis K p x).coeff d) * X ^ (d : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun d => C ((outerBasis K p x).coeff d) * X ^ d)]
  conv_lhs => rw [as_sum_range' _ _ (outerBasis_natDegree_lt_large hK hK0 hpK x)]
  simp only [C_mul_X_pow_eq_monomial]

theorem outerGram_eq_sum_large (x y : OuterIdx K p) :
    outerGram K p x y = ∑ k : Fin (hof K), ∑ l : Fin (hof K),
      C ((outerBasis K p x).coeff k * (outerBasis K p y).coeff l) * Aout K p k l := by
  rw [outerGram_apply]
  conv_lhs => rw [outerBasis_expand_large hK hK0 hpK x, outerBasis_expand_large hK hK0 hpK y]
  rw [mul_assoc, sum_mul_sum, mul_sum, muXmod_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, muXmod_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [show D (Nof K) ^ 6 * (C ((outerBasis K p x).coeff k) * X ^ (k : ℕ) *
      (C ((outerBasis K p y).coeff l) * X ^ (l : ℕ))) =
      C ((outerBasis K p x).coeff k * (outerBasis K p y).coeff l) *
        (D (Nof K) ^ 6 * X ^ ((k : ℕ) + l)) by rw [C_mul, pow_add]; ring, muXmod_C_mul]
  rfl

/-! ## Every entry is integral -/

theorem large_class_entry {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) {R : ℚ[X]} (hR : vpGge p R 0) :
    vpGge p (muXmod p (outerClassPoles K p a) R) 0 := by
  have hp7 := large_p7 hK hK0 hpK
  have hodd := large_odd hK hK0 hpK
  have ha2 : 2 * a < p := by unfold mHalf at ha; omega
  by_cases hboth : a ∈ outerClassPoles K p a ∧ p - a ∈ outerClassPoles K p a
  · have hC : outerClassPoles K p a = {a, p - a} := by
      ext j
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hj; exact (large_class_mem hK hK0 hpK ha hj).1
      · rintro (rfl | rfl)
        · exact hboth.1
        · exact hboth.2
    rw [hC]
    exact two_pole_vge hp7 ha1 ha2 hR
  · refine muXmod_vge_of_residues hp7 _ hR le_rfl fun j hj => ?_
    have hj' := large_class_mem hK hK0 hpK ha hj
    have herase : (outerClassPoles K p a).erase j = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro k hk
      have hk' := large_class_mem hK hK0 hpK ha (mem_of_mem_erase hk)
      have hkj := ne_of_mem_erase hk
      apply hboth
      rcases hj'.1 with rfl | rfl <;> rcases hk'.1 with rfl | rfl
      · exact absurd rfl hkj
      · exact ⟨hj, mem_of_mem_erase hk⟩
      · exact ⟨mem_of_mem_erase hk, hj⟩
      · exact absurd rfl hkj
    have hres : sqResidue (outerClassPoles K p a) R j = R.eval (-(j : ℚ) ^ 2) := by
      rw [sqResidue, herase, prod_empty, div_one]
    rw [hres]
    exact vpGge_mul0 (vpGge_C (eval_vge0 hR (vge_neg_sq j)))
      (muPole_vge_small (by omega) (by omega) (by omega))

theorem outerGram_int_large (x y : OuterIdx K p) : vpGge p (outerGram K p x y) 0 := by
  have hp7 := large_p7 hK hK0 hpK
  have hodd := large_odd hK hK0 hpK
  rw [outerGram_apply, outerBasis_eq, outerBasis_eq]
  by_cases hac : x.1 = y.1
  swap
  · have hdisj : Disjoint (outerClassPoles K p x.1) (outerClassPoles K p y.1) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      rw [mem_outerClassPoles_iff hodd (Nat.lt_succ_iff.mp x.1.2)] at h1
      rw [mem_outerClassPoles_iff hodd (Nat.lt_succ_iff.mp y.1.2)] at h2
      exact hac (Fin.ext (h1.2.symm.trans h2.2))
    rw [cross_class_cancel (p := p) K _ _ hdisj]
    exact vpGge_C (muModPoly_vge hp7 (vpGge_mul0 (vpGge_mul0 (vpGge_mul0
      (vpGge_pow0 (vpGge_sqPoleProd _) _) (vpGge_sqPoleProd _)) (oq_vge K p x)) (oq_vge K p y)))
  · have hyx : (y.1 : ℕ) = x.1 := congrArg Fin.val hac.symm
    rw [hyx, same_class_cancel (p := p) K _ (class_subset_tail K p _)]
    exact large_class_entry hK hK0 hpK (Nat.one_le_iff_ne_zero.mpr (large_ne_zero hK hK0 hpK x))
      (Nat.lt_succ_iff.mp x.1.2) (vpGge_mul0 (vpGge_mul0 (vpGge_mul0
        (vpGge_pow0 (vpGge_sqPoleProd _) _) (vpGge_sqPoleProd _)) (oq_vge K p x)) (oq_vge K p y))

end Large

/-- **Proposition 4.3, second part**: `v_p^G(Δ_K) ≥ 0` for `p > K`. -/
theorem prop_4_3_large' {K : ℕ} (hK : 40 ∣ K) (hp : K < p) : vpGge p (Delta K) 0 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK0
  · have : IsEmpty (Fin (hof 0)) := by
      rw [show hof 0 = 0 by rfl]; infer_instance
    unfold Delta
    rw [Matrix.det_isEmpty]
    exact vpGge_one
  obtain ⟨e, hdetv, hdet0⟩ := outerBasis_unimodular_large hK hK0 hp
  set Bm : Matrix (Fin (hof K)) (Fin (hof K)) ℚ :=
    Matrix.of fun x d => (outerBasis K p (e.symm x)).coeff d with hBm
  set OG : Matrix (Fin (hof K)) (Fin (hof K)) ℚ[X] :=
    Matrix.of fun x y => outerGram K p (e.symm x) (e.symm y) with hOG
  have hA : Bm.map C * Aout K p * (Bm.map C).transpose = OG := by
    refine Matrix.ext fun x y => ?_
    rw [hOG, Matrix.of_apply, outerGram_eq_sum_large hK hK0 hp]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hBm, Matrix.of_apply,
      sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [C_mul]; ring
  have hdetrel : OG.det = C (Bm.det ^ 2) * Delta K := by
    rw [← hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_C_det, Delta,
      G_eq_Aout_large hK hK0 hp]
    simp only [map_pow]; ring
  have hOGv : vpGge p OG.det 0 := by
    apply vpGge_det_of_terms
    intro σ
    have := vpGge_prod univ (fun i => OG (σ i) i) (fun _ => (0 : ℚ))
      fun i _ => outerGram_int_large hK hK0 hp _ _
    simpa using this
  rw [hdetrel] at hOGv
  have hu : Bm.det ^ 2 ≠ 0 := pow_ne_zero 2 hdet0
  have huv : padicValRat p (Bm.det ^ 2) = 0 := by rw [padicValRat.pow, hdetv, mul_zero]
  exact vpGge_of_unit_mul hu huv hOGv

end Zeta5
