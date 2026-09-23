import Zeta5.Functionals
import Zeta5.Valuation

/-!
# CRT bases and the unimodularity of the outer basis (4.11)
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

section CRT

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The CRT family `∏_{c ≠ a} (X - r_c)^{n_c} · (X - r_a)^i`, `i < n_a`. -/
def crtFam (r : ι → F) (n : ι → ℕ) (x : Σ a : ι, Fin (n a)) : F[X] :=
  (∏ c ∈ univ.erase x.1, (X - C (r c)) ^ n c) * (X - C (r x.1)) ^ (x.2 : ℕ)

theorem crtFam_natDegree (r : ι → F) (n : ι → ℕ) (x : Σ a : ι, Fin (n a)) :
    (crtFam r n x).natDegree = (∑ c ∈ univ.erase x.1, n c) + x.2 := by
  unfold crtFam
  rw [natDegree_mul (monic_prod_of_monic _ _ fun c _ => (monic_X_sub_C _).pow _).ne_zero
      ((monic_X_sub_C _).pow _).ne_zero,
    natDegree_prod_of_monic _ _ fun c _ => (monic_X_sub_C _).pow _]
  simp [natDegree_pow]

theorem crtFam_natDegree_lt (r : ι → F) (n : ι → ℕ) (x : Σ a : ι, Fin (n a)) :
    (crtFam r n x).natDegree < ∑ c, n c := by
  rw [crtFam_natDegree, ← add_sum_erase _ _ (mem_univ x.1)]
  have := x.2.2
  omega

/-- **CRT basis lemma.** For distinct `r_c`, the polynomials
`∏_{c ≠ a} (X - r_c)^{n_c} (X - r_a)^i`, `i < n_a`, are linearly independent. -/
theorem crtFam_linearIndependent (r : ι → F) (hr : Function.Injective r) (n : ι → ℕ) :
    LinearIndependent F (crtFam r n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg x
  obtain ⟨a, i⟩ := x
  set Pa := ∏ c ∈ univ.erase a, (X - C (r c)) ^ n c with hPa
  set S : F[X] := ∑ k : Fin (n a), g ⟨a, k⟩ • (X - C (r a)) ^ (k : ℕ) with hS
  have hsum : ∑ x, g x • crtFam r n x =
      ∑ b, ∑ k : Fin (n b), g ⟨b, k⟩ • crtFam r n ⟨b, k⟩ := Fintype.sum_sigma _
  rw [hsum, ← add_sum_erase _ _ (mem_univ a)] at hg
  have hblock : ∑ k : Fin (n a), g ⟨a, k⟩ • crtFam r n ⟨a, k⟩ = Pa * S := by
    rw [hS, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [crtFam, hPa, smul_eq_C_mul]
    ring
  have hdvd : (X - C (r a)) ^ n a ∣ Pa * S := by
    rw [← hblock, eq_neg_of_add_eq_zero_left hg]
    refine (dvd_neg).mpr (dvd_sum fun b hb => dvd_sum fun k _ => ?_)
    rw [smul_eq_C_mul]
    refine dvd_mul_of_dvd_right ?_ _
    exact dvd_mul_of_dvd_left (dvd_prod_of_mem _ (mem_erase.mpr ⟨(ne_of_mem_erase hb).symm,
      mem_univ _⟩)) _
  have hcop : IsCoprime ((X - C (r a)) ^ n a) Pa :=
    IsCoprime.prod_right fun c hc =>
      (isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr fun h => (ne_of_mem_erase hc) (hr h).symm).isUnit).pow
  have hSd : (X - C (r a)) ^ n a ∣ S := hcop.dvd_of_dvd_mul_left hdvd
  have hSdeg : S.natDegree < ((X - C (r a)) ^ n a).natDegree := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have hpos : 0 < n a := lt_of_le_of_lt (Nat.zero_le _) i.2
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := n a - 1) fun k _ => ?_) (by omega)
    refine (natDegree_smul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have := k.2; omega
  have hS0 : S = 0 := eq_zero_of_dvd_of_natDegree_lt hSd hSdeg
  have hcomp := congrArg (fun P : F[X] => (P.comp (X + C (r a))).coeff i) hS0
  simp only [hS, coeff_zero, zero_comp] at hcomp
  rw [← hcomp]
  simp only [Polynomial.sum_comp, smul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right,
    finsetSum_coeff, coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_eq_single i (fun b _ hb => ite_eq_right_iff.mpr fun h => absurd (Fin.ext h.symm) hb) (by simp)]
  simp

end CRT

/-! ## Square classes mod `p` -/

/-- The square class of `j` mod `p`: `min(j mod p, p - j mod p)`. -/
def cls (p j : ℕ) : ℕ := min (j % p) (p - j % p)

theorem mod_lt_two_mul {x p : ℕ} (hx : x < 2 * p) : x % p = if x < p then x else x - p := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- For odd `p` and `a ≤ (p-1)/2`, `j ≡ ±a (mod p)` iff `cls p j = a`. -/
theorem classCond_aux (p r a : ℕ) (hp : p % 2 = 1) (hr : r < p) (ha : a ≤ (p - 1) / 2) :
    (r = a ∨ (if r + a < p then r + a else r + a - p) = 0) ↔ min r (p - r) = a := by
  split_ifs with h <;> rcases le_total r (p - r) with h' | h' <;>
    simp only [min_eq_left h', min_eq_right h'] <;> omega

theorem classCond_iff {p j a : ℕ} (hp : p % 2 = 1) (ha : a ≤ mHalf p) :
    (j % p = a % p ∨ (j + a) % p = 0) ↔ cls p j = a := by
  have hp0 : 0 < p := by omega
  have ha' : a ≤ (p - 1) / 2 := ha
  have hap : a < p := by omega
  have h1 : (j + a) % p = (j % p + a) % p := by rw [Nat.add_mod, Nat.mod_eq_of_lt hap]
  have hr : j % p < p := Nat.mod_lt _ hp0
  rw [h1, mod_lt_two_mul (x := j % p + a) (by omega), Nat.mod_eq_of_lt hap]
  exact classCond_aux p (j % p) a hp hr ha'

theorem cls_le {p j : ℕ} (hp : p % 2 = 1) : cls p j ≤ mHalf p := by
  have hr : j % p < p := Nat.mod_lt _ (by omega)
  show min (j % p) (p - j % p) ≤ (p - 1) / 2
  rcases le_total (j % p) (p - j % p) with h' | h' <;>
    simp only [min_eq_left h', min_eq_right h'] <;> omega

theorem cast_sq_cls (p j : ℕ) [Fact p.Prime] :
    ((j : ZMod p)) ^ 2 = ((cls p j : ℕ) : ZMod p) ^ 2 := by
  have hr : j % p ≤ p := (Nat.mod_lt _ (Fact.out : p.Prime).pos).le
  have hj : (j : ZMod p) = ((j % p : ℕ) : ZMod p) := (ZMod.natCast_mod j p).symm
  unfold cls
  rcases le_total (j % p) (p - j % p) with h | h
  · rw [min_eq_left h, hj]
  · rw [min_eq_right h, Nat.cast_sub hr, ZMod.natCast_self, hj]; ring

/-- The class as an element of `Fin (m+1)` (the `min` makes this total; it is `cls` for odd `p`). -/
def clsF (p j : ℕ) : Fin (mHalf p + 1) := ⟨min (cls p j) (mHalf p), by omega⟩

theorem clsF_val {p j : ℕ} (hp : p % 2 = 1) : (clsF p j : ℕ) = cls p j := by
  simp [clsF, min_eq_left (cls_le hp)]

theorem mem_outerClassPoles_iff {K p a j : ℕ} (hp : p % 2 = 1) (ha : a ≤ mHalf p) :
    j ∈ outerClassPoles K p a ↔ j ∈ Icc (Nof K + 1) K ∧ cls p j = a := by
  unfold outerClassPoles
  rw [mem_filter, classCond_iff hp ha]

/-! ## The integer basis -/

def sqPoleProdZ (S : Finset ℕ) : ℤ[X] := ∏ j ∈ S, (X + C ((j : ℤ) ^ 2))

def outerBasisZ (K p : ℕ) (x : OuterIdx K p) : ℤ[X] :=
  let a : ℕ := x.1
  let i : ℕ := x.2
  let Pa := sqPoleProdZ (Icc (Nof K + 1) K \ outerClassPoles K p a)
  if a = 0 then Pa * (X + C ((p : ℤ) ^ 2)) ^ i
  else
    let l := ell p K a
    if i < l - 2 then Pa * (X + C ((a : ℤ) ^ 2)) ^ i
    else Pa * sqPoleProdZ ((outerClassPoles K p a).filter fun j => p < j) *
      (X + C ((a : ℤ) ^ 2)) ^ (i - (l - 2))

theorem sqPoleProdZ_map {R : Type*} [CommRing R] (S : Finset ℕ) :
    (sqPoleProdZ S).map (Int.castRingHom R) = ∏ j ∈ S, (X + C ((j : R) ^ 2)) := by
  simp [sqPoleProdZ, Polynomial.map_prod]

theorem outerBasis_eq_map (K p : ℕ) (x : OuterIdx K p) :
    outerBasis K p x = (outerBasisZ K p x).map (Int.castRingHom ℚ) := by
  unfold outerBasis outerBasisZ
  simp only
  split_ifs <;> simp [Polynomial.map_mul, Polynomial.map_pow, sqPoleProdZ_map, sqPoleProd]

/-! ## Reduction mod `p` -/

/-- The roots `-c²` mod `p` of the class factors `t + c²`. -/
def rr (p : ℕ) (c : Fin (mHalf p + 1)) : ZMod p := -(((c : ℕ) : ZMod p) ^ 2)

theorem rr_injective {p : ℕ} [Fact p.Prime] (hp : p % 2 = 1) : Function.Injective (rr p) := by
  intro c c' h
  have hc : (c : ℕ) ≤ (p - 1) / 2 := Nat.lt_succ_iff.mp c.2
  have hc' : (c' : ℕ) ≤ (p - 1) / 2 := Nat.lt_succ_iff.mp c'.2
  have h2 : (((c : ℕ) : ZMod p) - (c' : ℕ)) * (((c : ℕ) : ZMod p) + (c' : ℕ)) = 0 := by
    simp only [rr, neg_inj] at h; linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp h3)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext this
  · have h4 : ((((c : ℕ) + c' : ℕ)) : ZMod p) = 0 := by push_cast; exact h3
    have := (ZMod.natCast_eq_zero_iff _ _).mp h4
    have h5 : (c : ℕ) + c' = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    exact Fin.ext (by omega)

theorem X_sub_rr (p : ℕ) (c : Fin (mHalf p + 1)) :
    (X - C (rr p c) : (ZMod p)[X]) = X + C (((c : ℕ) : ZMod p) ^ 2) := by
  simp [rr]

/-- Grouping a product of pole factors by square classes. -/
theorem prod_by_class {p : ℕ} [Fact p.Prime] (hp : p % 2 = 1) (T : Finset ℕ) :
    ∏ j ∈ T, (X + C ((j : ZMod p) ^ 2)) =
      ∏ c : Fin (mHalf p + 1), (X - C (rr p c)) ^ (T.filter fun j => clsF p j = c).card := by
  rw [← prod_fiberwise T (clsF p)]
  refine prod_congr rfl fun c _ => ?_
  rw [← prod_const]
  refine prod_congr rfl fun j hj => ?_
  have hjc := (mem_filter.mp hj).2
  rw [X_sub_rr, cast_sq_cls, ← clsF_val hp, hjc]

theorem filter_clsF_eq {K p : ℕ} (hp : p % 2 = 1) (c : Fin (mHalf p + 1)) :
    (Icc (Nof K + 1) K).filter (fun j => clsF p j = c) = outerClassPoles K p c := by
  ext j
  rw [mem_filter, mem_outerClassPoles_iff hp (Nat.lt_succ_iff.mp c.2), Fin.ext_iff, clsF_val hp]

theorem card_filter_Pa {K p : ℕ} (hp : p % 2 = 1) (a c : Fin (mHalf p + 1)) :
    ((Icc (Nof K + 1) K \ outerClassPoles K p a).filter (fun j => clsF p j = c)).card =
      if c = a then 0 else outerCount K p c := by
  split_ifs with hca
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro j hj hjc
    rw [mem_sdiff, mem_outerClassPoles_iff hp (Nat.lt_succ_iff.mp a.2)] at hj
    exact hj.2 ⟨hj.1, by rw [← clsF_val hp, hjc, hca]⟩
  · unfold outerCount
    rw [← filter_clsF_eq hp c]
    congr 1
    ext j
    simp only [mem_filter, mem_sdiff, mem_outerClassPoles_iff hp (Nat.lt_succ_iff.mp a.2)]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun h3 => hca ?_⟩, h2⟩
      rw [← h2]; exact Fin.ext (by rw [clsF_val hp]; exact h3.2)

/-- `#E = ℓ - 2`: the class of `a ≥ 1` has exactly two poles `a, p - a` below `p`. -/
theorem card_E_add_two {K p a : ℕ} (hp : p % 2 = 1) (h : OuterHyp K p) (ha1 : 1 ≤ a)
    (ha : a ≤ mHalf p) :
    ((outerClassPoles K p a).filter (fun j => p < j)).card + 2 = ell p K a := by
  obtain ⟨h7, hpK, hK3, h2K, h2N, h5N⟩ := h
  have ha' : a ≤ (p - 1) / 2 := ha
  have key : ∀ j, j ≤ p → (cls p j = a ↔ j = a ∨ j = p - a) := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj | hj
    · have : cls p j = min j (p - j) := by unfold cls; rw [Nat.mod_eq_of_lt hj]
      rw [this]
      rcases le_total j (p - j) with h' | h' <;>
        simp only [min_eq_left h', min_eq_right h'] <;> omega
    · have : cls p j = 0 := by unfold cls; rw [hj]; simp
      rw [this]; omega
  have hset : (Icc 1 K).filter (fun j => j % p = a % p ∨ (j + a) % p = 0) =
      insert a (insert (p - a) ((outerClassPoles K p a).filter (fun j => p < j))) := by
    ext j
    simp only [mem_filter, mem_insert, mem_Icc, classCond_iff hp ha,
      mem_outerClassPoles_iff hp ha]
    by_cases hjp : j ≤ p
    · rw [key j hjp]; omega
    · constructor
      · rintro ⟨h1, h2⟩; exact Or.inr (Or.inr ⟨⟨⟨by omega, h1.2⟩, h2⟩, by omega⟩)
      · rintro (h1 | h1 | ⟨⟨⟨h1, h2⟩, h3⟩, _⟩)
        · omega
        · omega
        · exact ⟨⟨by omega, h2⟩, h3⟩
  unfold ell
  rw [hset, card_insert_of_notMem, card_insert_of_notMem]
  · simp only [mem_filter, not_and, not_lt]; intro _; omega
  · simp only [mem_insert, mem_filter, not_or, not_and, not_lt]
    exact ⟨by omega, fun _ => by omega⟩

theorem Pa_mod {K p : ℕ} [Fact p.Prime] (hp : p % 2 = 1) (a : Fin (mHalf p + 1)) :
    (sqPoleProdZ (Icc (Nof K + 1) K \ outerClassPoles K p a)).map (Int.castRingHom (ZMod p)) =
      ∏ c ∈ univ.erase a, (X - C (rr p c)) ^ outerCount K p c := by
  rw [sqPoleProdZ_map, prod_by_class hp]
  simp_rw [card_filter_Pa hp a]
  rw [← mul_prod_erase univ _ (mem_univ a)]
  simp only [ite_true, pow_zero, one_mul]
  exact prod_congr rfl fun c hc => by simp [ne_of_mem_erase hc]

theorem map_X_add_sq {p : ℕ} (a : Fin (mHalf p + 1)) :
    (X + C (((a : ℕ) : ℤ) ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p)) = X - C (rr p a) := by
  rw [X_sub_rr]; simp

/-- Mod `p`, the outer basis is the CRT family. -/
theorem outerBasisZ_mod {K p : ℕ} [Fact p.Prime] (hp : p % 2 = 1) (h : OuterHyp K p)
    (x : OuterIdx K p) :
    (outerBasisZ K p x).map (Int.castRingHom (ZMod p)) =
      crtFam (rr p) (fun c => outerCount K p c) x := by
  obtain ⟨a, i⟩ := x
  unfold outerBasisZ crtFam
  simp only
  split_ifs with h0 hi
  · have ha0 : a = 0 := Fin.ext h0
    subst ha0
    rw [Polynomial.map_mul, Pa_mod hp, Polynomial.map_pow]
    simp [rr]
  · rw [Polynomial.map_mul, Pa_mod hp, Polynomial.map_pow, map_X_add_sq]
  · have ha1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr h0
    have hE := card_E_add_two (K := K) hp h ha1 (Nat.lt_succ_iff.mp a.2)
    rw [Polynomial.map_mul, Polynomial.map_mul, Pa_mod hp, Polynomial.map_pow, sqPoleProdZ_map]
    have hEprod : ∏ j ∈ (outerClassPoles K p a).filter (fun j => p < j),
        (X + C ((j : ZMod p) ^ 2)) = (X - C (rr p a)) ^ (ell p K a - 2) := by
      rw [← hE, Nat.add_sub_cancel, ← prod_const]
      refine prod_congr rfl fun j hj => ?_
      have hj' := (mem_outerClassPoles_iff hp (Nat.lt_succ_iff.mp a.2)).mp (mem_filter.mp hj).1
      rw [X_sub_rr, cast_sq_cls, hj'.2]
    rw [hEprod]
    rw [map_X_add_sq, mul_assoc, ← pow_add]
    congr 2
    omega

theorem card_outerIdx {K p : ℕ} (hK : 40 ∣ K) (hp : p % 2 = 1) :
    Fintype.card (OuterIdx K p) = hof K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h1 := card_eq_sum_card_fiberwise (s := Icc (Nof K + 1) K) (t := univ) (f := clsF p)
    (fun _ _ => mem_coe.mpr (mem_univ _))
  simp_rw [filter_clsF_eq hp] at h1
  unfold outerCount
  rw [← h1, Nat.card_Icc]
  obtain ⟨n, rfl⟩ := hK
  unfold Nof hof; omega

/-- **(4.11)**: the outer basis is `ℤ_p`-unimodular. -/
theorem outerBasis_unimodular' {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    ∃ e : OuterIdx K p ≃ Fin (hof K),
      padicValRat p (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (outerBasis K p (e.symm x)).coeff d).det = 0 ∧
      (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (outerBasis K p (e.symm x)).coeff d).det ≠ 0 := by
  have hp : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | h2
    · have := h.1; omega
    · exact h2
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
    rw [hv, ← outerBasisZ_mod hp h, coeff_map]; rfl
  have hsum : ∑ c : Fin (mHalf p + 1), outerCount K p c = hof K := by
    rw [← card_outerIdx hK hp, Fintype.card_sigma]; simp
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

end Zeta5