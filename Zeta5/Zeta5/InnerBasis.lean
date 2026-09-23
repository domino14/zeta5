import Zeta5.Section4
import Zeta5.CRTBasis
import Zeta5.Prop43

/-!
# §4.1 The inner basis: dimensions, unimodularity, and Prop 4.1 from the entry bounds
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

/-! ## Counting residues -/

/-- At most `(A + p - r)/p` integers in `[1, A]` are `≡ r (mod p)`. -/
theorem card_filter_mod_mul_le (A p r : ℕ) (hr : r < p) :
    ((Icc 1 A).filter fun j => j % p = r).card * p ≤ A + p - r := by
  have hp : 0 < p := by omega
  have hc : ((Icc 1 A).filter fun j => j % p = r).card ≤ (A + p - r) / p := by
    have : ((Icc 1 A).filter fun j => j % p = r).card ≤ (range ((A + p - r) / p)).card := by
      refine card_le_card_of_injOn (fun j => j / p) ?_ ?_
      · intro j hj
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj
        simp only [coe_range, Set.mem_Iio]
        apply Nat.lt_of_succ_le
        rw [Nat.le_div_iff_mul_le hp]
        have e := Nat.div_add_mod j p
        rw [hj.2] at e
        apply Nat.le_sub_of_add_le
        nlinarith [e, hj.1.2]
      · intro j1 hj1 j2 hj2 heq
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj1 hj2
        have e1 := Nat.div_add_mod j1 p
        have e2 := Nat.div_add_mod j2 p
        simp only at heq
        rw [heq, hj1.2] at e1
        rw [hj2.2] at e2
        omega
    simpa using this
  calc _ ≤ (A + p - r) / p * p := Nat.mul_le_mul_right p hc
    _ ≤ A + p - r := Nat.div_mul_le_self _ _

/-- `ℓ_A(a) ≤ 2A/p + 1` for `1 ≤ a < p`. -/
theorem ell_mul_le {p A a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) : ell p A a * p ≤ 2 * A + p := by
  have hsub : (Icc 1 A).filter (fun j => j % p = a % p ∨ (j + a) % p = 0) ⊆
      (Icc 1 A).filter (fun j => j % p = a) ∪ (Icc 1 A).filter (fun j => j % p = p - a) := by
    intro j hj
    simp only [mem_filter, mem_union] at hj ⊢
    rw [Nat.mod_eq_of_lt hap] at hj
    rcases hj.2 with h1 | h1
    · exact Or.inl ⟨hj.1, h1⟩
    · right
      refine ⟨hj.1, ?_⟩
      have hr : j % p < p := Nat.mod_lt _ (by omega)
      rw [Nat.add_mod, Nat.mod_eq_of_lt hap, mod_add_small hr hap] at h1
      omega
  have h1 := card_filter_mod_mul_le A p a hap
  have h2 := card_filter_mod_mul_le A p (p - a) (by omega)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  unfold ell
  calc _ ≤ (((Icc 1 A).filter fun j => j % p = a).card +
        ((Icc 1 A).filter fun j => j % p = p - a).card) * p := Nat.mul_le_mul_right p hc
    _ ≤ 2 * A + p := by rw [add_mul]; omega

theorem InnerHyp.odd {K M p : ℕ} [hp : Fact p.Prime] (h : InnerHyp K M p) :
    2 * mHalf p + 1 = p := by
  have := (innerHyp_bounds h).1
  have h40 := h.1
  obtain ⟨k, hk⟩ := (hp.out.eq_two_or_odd').resolve_left (by omega)
  unfold mHalf; omega

theorem epsIn_nonneg (K M p : ℕ) (pos : ℕ → ℕ) (a : ℕ) : 0 ≤ epsIn K M p pos a := by
  unfold epsIn; split_ifs <;> norm_num

theorem epsIn_le_one (K M p : ℕ) (pos : ℕ → ℕ) (a : ℕ) : epsIn K M p pos a ≤ 1 := by
  unfold epsIn; split_ifs <;> norm_num

/-- §4.1: the dimensions `L_a` are nonnegative. -/
theorem Lin_nonneg' {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) (a : ℕ) (ha : a ≤ mHalf p) :
    0 ≤ Lin K M p a := by
  unfold Lin
  split_ifs with ha0
  · positivity
  · have hodd := InnerHyp.odd h
    obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
    have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
    have hh : hof (40 * n) = 37 * n := by unfold hof; omega
    have hell := ell_mul_le (p := p) (A := Nof (40 * n)) (Nat.one_le_iff_ne_zero.mpr ha0) (by omega)
    rw [hN] at hell
    have hq : 3 * n / p ≤ 3 * n := Nat.div_le_self _ _
    have hm : (0 : ℤ) < mHalf p := by exact_mod_cast (show 0 < mHalf p by omega)
    have hT : bIn (40 * n) p a ≤ Tin (40 * n) M p := by
      unfold Tin bIn
      apply Int.le_ediv_of_mul_le hm
      unfold rhs44 L0
      rw [hN, hh]
      have e1 : ((ell p (3 * n) a : ℕ) : ℤ) * p ≤ 2 * (3 * n) + p := by exact_mod_cast hell
      have e2 : (p : ℤ) = 2 * mHalf p + 1 := by exact_mod_cast hodd.symm
      have e3 : (3 : ℤ) * p ≤ 40 * n := by exact_mod_cast h3p
      have e4 : ((3 * n / p : ℕ) : ℤ) ≤ 3 * n := by exact_mod_cast hq
      have e5 : (200 : ℤ) * M ^ 2 ≤ 40 * n := by exact_mod_cast hKM
      have e6 : (40 : ℤ) ≤ M := by exact_mod_cast hM
      have e7 : (0 : ℤ) ≤ ell p (3 * n) a := by positivity
      push_cast
      nlinarith
    have := epsIn_nonneg (40 * n) M p (defaultPos (40 * n) p) a
    linarith

/-! ## `∑ L_a = h` -/

theorem sum_ell_eq {p A : ℕ} (hp : p % 2 = 1) :
    ∑ a ∈ range (mHalf p + 1), ell p A a = A := by
  have h1 := card_eq_sum_card_fiberwise (s := Icc 1 A) (t := range (mHalf p + 1)) (f := cls p)
    (fun j _ => by simp only [coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le (cls_le hp))
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  conv_rhs => rw [h1]
  refine sum_congr rfl fun a ha => ?_
  unfold ell
  congr 1
  ext j
  simp only [mem_filter]
  rw [classCond_iff hp (Nat.lt_succ_iff.mp (mem_range.mp ha))]

theorem ell_zero_eq (p A : ℕ) : ell p A 0 = A / p := by
  unfold ell
  rw [← Nat.Ioc_filter_dvd_card_eq_div A p]
  congr 1
  ext j
  simp only [mem_filter, mem_Icc, mem_Ioc, Nat.zero_mod, add_zero, or_self]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, Nat.dvd_of_mod_eq_zero h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, Nat.mod_eq_zero_of_dvd h3⟩

section Order

variable (K p : ℕ)

/-- The strict order "`c` comes before `a`" of `defaultPos`. -/
def before (c a : ℕ) : Prop := ell p K a < ell p K c ∨ (ell p K c = ell p K a ∧ c < a)

instance : DecidableRel (before K p) := fun _ _ => by unfold before; infer_instance

theorem before_trans {a b c : ℕ} (h1 : before K p a b) (h2 : before K p b c) : before K p a c := by
  unfold before at *; omega

theorem before_irrefl (a : ℕ) : ¬ before K p a a := by unfold before; omega

theorem before_total {a c : ℕ} (h : a ≠ c) : before K p a c ∨ before K p c a := by
  unfold before; omega

theorem defaultPos_eq (a : ℕ) :
    defaultPos K p a = ((Icc 1 (mHalf p)).filter fun c => before K p c a).card := rfl

theorem pos_lt_iff {a c : ℕ} (hc : c ∈ Icc 1 (mHalf p)) :
    defaultPos K p c < defaultPos K p a ↔ before K p c a := by
  rw [defaultPos_eq, defaultPos_eq]
  constructor
  · intro hlt
    by_contra hn
    rcases eq_or_ne c a with rfl | hca
    · exact lt_irrefl _ hlt
    · have hac := (before_total K p hca).resolve_left hn
      have : ((Icc 1 (mHalf p)).filter fun d => before K p d a) ⊆
          ((Icc 1 (mHalf p)).filter fun d => before K p d c) := by
        intro d hd; simp only [mem_filter] at hd ⊢
        exact ⟨hd.1, before_trans K p hd.2 hac⟩
      exact absurd (card_le_card this) (not_le.mpr hlt)
  · intro hca
    refine card_lt_card ⟨fun d hd => ?_, fun hsub => ?_⟩
    · simp only [mem_filter] at hd ⊢; exact ⟨hd.1, before_trans K p hd.2 hca⟩
    · have := hsub (mem_filter.mpr ⟨hc, hca⟩)
      exact before_irrefl K p c (mem_filter.mp this).2

theorem pos_injOn : Set.InjOn (defaultPos K p) (Icc 1 (mHalf p) : Finset ℕ) := by
  intro a ha c hc hac
  by_contra hne
  rcases before_total K p hne with h1 | h1
  · have := (pos_lt_iff K p (mem_coe.mp ha)).mpr h1; omega
  · have := (pos_lt_iff K p (mem_coe.mp hc)).mpr h1; omega

theorem pos_lt_m {a : ℕ} (ha : a ∈ Icc 1 (mHalf p)) : defaultPos K p a < mHalf p := by
  rw [defaultPos_eq]
  have hsub : ((Icc 1 (mHalf p)).filter fun c => before K p c a) ⊆ (Icc 1 (mHalf p)).erase a := by
    intro c hc
    simp only [mem_filter] at hc
    exact mem_erase.mpr ⟨fun e => before_irrefl K p a (e ▸ hc.2), hc.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem ha, Nat.card_Icc] at this
  have : 0 < mHalf p := by simp only [mem_Icc] at ha; omega
  omega

theorem image_pos : (Icc 1 (mHalf p)).image (defaultPos K p) = range (mHalf p) := by
  apply eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (pos_lt_m K p ha)
  · rw [card_image_of_injOn (pos_injOn K p), card_range, Nat.card_Icc]; omega

theorem card_pos_lt (E : ℕ) (hE : E ≤ mHalf p) :
    ((Icc 1 (mHalf p)).filter fun a => defaultPos K p a < E).card = E := by
  have h1 : ((Icc 1 (mHalf p)).filter fun a => defaultPos K p a < E).image (defaultPos K p) =
      range E := by
    ext k
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨a, ⟨_, h⟩, rfl⟩; exact h
    · intro hk
      have : k ∈ (Icc 1 (mHalf p)).image (defaultPos K p) := by
        rw [image_pos]; exact mem_range.mpr (by omega)
      obtain ⟨a, ha, rfl⟩ := mem_image.mp this
      exact ⟨a, ⟨ha, hk⟩, rfl⟩
  have hinj : Set.InjOn (defaultPos K p)
      (((Icc 1 (mHalf p)).filter fun a => defaultPos K p a < E : Finset ℕ) : Set ℕ) :=
    (pos_injOn K p).mono fun a ha => mem_coe.mpr (mem_filter.mp (mem_coe.mp ha)).1
  have := card_image_of_injOn hinj
  rw [h1, card_range] at this
  exact this.symm

theorem card_before_eq {a : ℕ} :
    ((Icc 1 (mHalf p)).filter fun c => defaultPos K p c < defaultPos K p a).card =
      defaultPos K p a := by
  rw [defaultPos_eq K p a]
  congr 1
  exact filter_congr fun c hc => pos_lt_iff K p hc

end Order

theorem sum_epsIn {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    ∑ a ∈ Icc 1 (mHalf p), epsIn K M p (defaultPos K p) a = Ein K M p := by
  obtain ⟨hE0, hEm, -⟩ := TE_spec h
  have e : ∀ a ∈ Icc 1 (mHalf p), epsIn K M p (defaultPos K p) a =
      if defaultPos K p a < (Ein K M p).toNat then 1 else 0 := by
    intro a _
    unfold epsIn
    rw [card_before_eq]
    congr 1
    apply propext; omega
  rw [sum_congr rfl e, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one,
    card_pos_lt K p _ (by omega)]
  omega

theorem range_succ_eq_insert (m : ℕ) : range (m + 1) = insert 0 (Icc 1 m) := by
  ext a; simp only [mem_range, mem_insert, mem_Icc]; omega

/-- §4.1: `L₀ + ∑_{a ≥ 1} L_a = h`. -/
theorem sum_Lin' {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    ∑ a ∈ range (mHalf p + 1), Lin K M p a = hof K := by
  have hodd := InnerHyp.odd h
  have hp2 : p % 2 = 1 := by omega
  obtain ⟨-, -, hTE⟩ := TE_spec h
  have h0 : (0 : ℕ) ∉ Icc 1 (mHalf p) := by simp
  have hell := sum_ell_eq (A := Nof K) hp2
  rw [range_succ_eq_insert, sum_insert h0, ell_zero_eq] at hell
  rw [range_succ_eq_insert, sum_insert h0]
  have hL : ∀ a ∈ Icc 1 (mHalf p), Lin K M p a =
      Tin K M p - 3 * (ell p (Nof K) a : ℤ) + epsIn K M p (defaultPos K p) a := by
    intro a ha
    have : a ≠ 0 := by simp only [mem_Icc] at ha; omega
    simp [Lin, this, bIn]
  rw [sum_congr rfl hL, sum_add_distrib, sum_sub_distrib, sum_epsIn h, sum_const, Nat.card_Icc,
    ← Finset.mul_sum]
  simp only [Lin, ite_true, nsmul_eq_mul]
  have hs : (∑ a ∈ Icc 1 (mHalf p), (ell p (Nof K) a : ℤ)) = Nof K - (Nof K / p : ℕ) := by
    have : ((Nof K / p + ∑ a ∈ Icc 1 (mHalf p), ell p (Nof K) a : ℕ) : ℤ) = Nof K := by
      rw [hell]
    rw [Nat.cast_add, Nat.cast_sum] at this
    linarith
  rw [hs]
  unfold rhs44 at hTE
  push_cast at hTE ⊢
  linarith

/-! ## The inner basis is a CRT family -/

theorem card_innerIdx {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    Fintype.card (InnerIdx K M p) = hof K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun a => (Lin K M p a).toNat)]
  have : ((∑ a ∈ range (mHalf p + 1), (Lin K M p a).toNat : ℕ) : ℤ) = hof K := by
    rw [Nat.cast_sum, ← sum_Lin' h]
    exact sum_congr rfl fun a ha => Int.toNat_of_nonneg (Lin_nonneg' h a
      (Nat.lt_succ_iff.mp (mem_range.mp ha)))
  exact_mod_cast this

theorem prod_range_erase_eq {R : Type*} [CommMonoid R] {m : ℕ} (a : Fin (m + 1)) (f : ℕ → R) :
    ∏ c ∈ (range (m + 1)).erase (a : ℕ), f c = ∏ c ∈ univ.erase a, f c := by
  symm
  refine prod_nbij' (fun c => (c : ℕ)) (fun c => (⟨min c m, by omega⟩ : Fin (m + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_erase] at hc
    rw [mem_erase, mem_range]
    exact ⟨fun h => hc.1 (Fin.ext h), c.2⟩
  · intro c hc
    rw [mem_erase, mem_range] at hc
    rw [mem_erase]
    refine ⟨fun h => hc.1 ?_, mem_univ _⟩
    rw [← h]; simp; omega
  · intro c _; ext; simp; omega
  · intro c hc
    rw [mem_erase, mem_range] at hc
    simp; omega
  · intro c _; rfl

/-- The inner basis over `ℤ`. -/
def innerBasisZ (K M p : ℕ) (x : InnerIdx K M p) : ℤ[X] :=
  (∏ c ∈ univ.erase x.1, (X + C (((c : ℕ) : ℤ) ^ 2)) ^ (Lin K M p c).toNat) *
    (X + C (((x.1 : ℕ) : ℤ) ^ 2)) ^ (x.2 : ℕ)

theorem innerBasis_eq_map (K M p : ℕ) (x : InnerIdx K M p) :
    innerBasis K M p x = (innerBasisZ K M p x).map (Int.castRingHom ℚ) := by
  unfold innerBasis innerBasisZ
  rw [prod_range_erase_eq x.1 (fun c => (X + C ((c : ℚ) ^ 2)) ^ (Lin K M p c).toNat)]
  simp [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow]

theorem innerBasisZ_mod {K M p : ℕ} [Fact p.Prime] (x : InnerIdx K M p) :
    (innerBasisZ K M p x).map (Int.castRingHom (ZMod p)) =
      crtFam (rr p) (fun c => (Lin K M p c).toNat) x := by
  unfold innerBasisZ crtFam
  rw [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow, map_X_add_sq]
  congr 1
  exact prod_congr rfl fun c _ => by rw [Polynomial.map_pow, map_X_add_sq]

/-- The inner basis over `ℚ` is a CRT family with roots `-c²`. -/
theorem innerBasis_eq_crt (K M p : ℕ) (x : InnerIdx K M p) :
    innerBasis K M p x =
      crtFam (fun c : Fin (mHalf p + 1) => -((c : ℕ) : ℚ) ^ 2) (fun c => (Lin K M p c).toNat) x := by
  unfold innerBasis crtFam
  rw [prod_range_erase_eq x.1 (fun c => (X + C ((c : ℚ) ^ 2)) ^ (Lin K M p c).toNat)]
  simp [sub_eq_add_neg]

theorem innerBasis_natDegree_lt {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p)
    (x : InnerIdx K M p) : (innerBasis K M p x).natDegree < hof K := by
  rw [innerBasis_eq_crt]
  refine lt_of_lt_of_eq (crtFam_natDegree_lt _ _ x) ?_
  rw [← card_innerIdx h, Fintype.card_sigma]; simp

/-- **(4.5)**: the inner basis is `ℤ_p`-unimodular. -/
theorem innerBasis_unimodular' {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    ∃ e : InnerIdx K M p ≃ Fin (hof K),
      padicValRat p (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (innerBasis K M p (e.symm x)).coeff d).det = 0 ∧
      (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (innerBasis K M p (e.symm x)).coeff d).det ≠ 0 := by
  have hp : p % 2 = 1 := by have := InnerHyp.odd h; omega
  set e : InnerIdx K M p ≃ Fin (hof K) := Fintype.equivFinOfCardEq (card_innerIdx h)
  refine ⟨e, ?_⟩
  set MZ : Matrix (Fin (hof K)) (Fin (hof K)) ℤ :=
    Matrix.of fun x d => (innerBasisZ K M p (e.symm x)).coeff d with hMZ
  have hM : (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
      (innerBasis K M p (e.symm x)).coeff d) = (Int.castRingHom ℚ).mapMatrix MZ := by
    ext x d; simp [hMZ, innerBasis_eq_map, coeff_map]
  have hdet : (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
      (innerBasis K M p (e.symm x)).coeff d).det = ((MZ.det : ℤ) : ℚ) := by
    rw [hM, ← RingHom.map_det]; rfl
  set v := crtFam (rr p) (fun c : Fin (mHalf p + 1) => (Lin K M p c).toNat) with hv
  set Mp := (Int.castRingHom (ZMod p)).mapMatrix MZ with hMp_def
  have hMp : ∀ x d, Mp x d = (v (e.symm x)).coeff d := by
    intro x d
    rw [hv, ← innerBasisZ_mod, coeff_map]; rfl
  have hsum : ∑ c : Fin (mHalf p + 1), (Lin K M p c).toNat = hof K := by
    rw [← card_innerIdx h, Fintype.card_sigma]; simp
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
        have hdeg := crtFam_natDegree_lt (rr p)
          (fun c : Fin (mHalf p + 1) => (Lin K M p c).toNat) (e.symm x)
        rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by rw [hv]; omega), smul_zero]
    have hli := crtFam_linearIndependent (rr p) (rr_injective hp)
      (fun c : Fin (mHalf p + 1) => (Lin K M p c).toNat)
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

/-! ## Proposition 4.1 from the entry bounds -/

theorem innerBasis_expand {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) (x : InnerIdx K M p) :
    innerBasis K M p x = ∑ d : Fin (hof K), C ((innerBasis K M p x).coeff d) * X ^ (d : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun d => C ((innerBasis K M p x).coeff d) * X ^ d)]
  conv_lhs => rw [as_sum_range' _ _ (innerBasis_natDegree_lt h x)]
  simp only [C_mul_X_pow_eq_monomial]

theorem innerGram_eq_sum {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) (x y : InnerIdx K M p) :
    innerGram K M p x y = ∑ k : Fin (hof K), ∑ l : Fin (hof K),
      C ((innerBasis K M p x).coeff k * (innerBasis K M p y).coeff l) * G K k l := by
  rw [innerGram, Matrix.of_apply]
  conv_lhs => rw [innerBasis_expand h x, innerBasis_expand h y]
  rw [mul_assoc, sum_mul_sum, mul_sum, muX_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, muX_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [show D (Nof K) ^ 6 * (C ((innerBasis K M p x).coeff k) * X ^ (k : ℕ) *
      (C ((innerBasis K M p y).coeff l) * X ^ (l : ℕ))) =
      C ((innerBasis K M p x).coeff k * (innerBasis K M p y).coeff l) *
        (D (Nof K) ^ 6 * X ^ ((k : ℕ) + l)) by rw [C_mul, pow_add]; ring, muX_C_mul]
  rfl

theorem gammaIn_eq_sum_idx (K M p : ℕ) :
    gammaIn K M p = 2 * ∑ y : InnerIdx K M p, wInIdx K M p y := by
  unfold gammaIn wInIdx
  rw [Fintype.sum_sigma]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ i ∈ range (Lin K M p a).toNat, wIn K M p a i)]
  refine sum_congr rfl fun a _ => ?_
  exact (Fin.sum_univ_eq_sum_range (fun i => wIn K M p a i) _).symm

/-- **Proposition 4.1** from the entry bounds `v_p^G(⟨E_x, E_y⟩) ≥ w_x + w_y`. -/
theorem prop_4_1_of_entries {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p)
    (hent : ∀ x y, vpGge p (innerGram K M p x y) (wInIdx K M p x + wInIdx K M p y)) :
    vpGge p (Delta K) (gammaIn K M p) := by
  obtain ⟨e, hdetv, hdet0⟩ := innerBasis_unimodular' h
  set Bm : Matrix (Fin (hof K)) (Fin (hof K)) ℚ :=
    Matrix.of fun x d => (innerBasis K M p (e.symm x)).coeff d with hBm
  set OG : Matrix (Fin (hof K)) (Fin (hof K)) ℚ[X] :=
    Matrix.of fun x y => innerGram K M p (e.symm x) (e.symm y) with hOG
  have hA : Bm.map C * G K * (Bm.map C).transpose = OG := by
    refine Matrix.ext fun x y => ?_
    rw [hOG, Matrix.of_apply, innerGram_eq_sum h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hBm, Matrix.of_apply,
      sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [C_mul]; ring
  have hdetrel : OG.det = C (Bm.det ^ 2) * Delta K := by
    rw [← hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_C_det, Delta]
    simp only [map_pow]; ring
  set w : Fin (hof K) → ℚ := fun x => wInIdx K M p (e.symm x)
  have hOGb : vpGge p OG.det (2 * ∑ x, w x) := by
    apply vpGge_det_of_terms
    intro σ
    refine vpGge_mono (vpGge_prod _ _ (fun i => w (σ i) + w i)
      fun i _ => hent (e.symm (σ i)) (e.symm i)) (le_of_eq ?_)
    rw [sum_add_distrib, Equiv.sum_comp σ w]; ring
  rw [hdetrel] at hOGb
  have hu : Bm.det ^ 2 ≠ 0 := pow_ne_zero 2 hdet0
  have huv : padicValRat p (Bm.det ^ 2) = 0 := by rw [padicValRat.pow, hdetv, mul_zero]
  refine vpGge_mono (vpGge_of_unit_mul hu huv hOGb) (le_of_eq ?_)
  rw [gammaIn_eq_sum_idx]
  congr 1
  exact (Equiv.sum_comp e.symm (wInIdx K M p)).symm

end Zeta5