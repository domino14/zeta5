import Zeta5.InnerEntries
import Zeta5.InnerBasis

/-!
# §4.1 The inner entry bounds (4.2)/(4.3) and Proposition 4.1
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

/-- Exponent of `t + j²` in the inner row `E_x`. -/
def nu (K M p : ℕ) (x : InnerIdx K M p) (j : ℕ) : ℕ :=
  if j ≤ mHalf p then (if j = (x.1 : ℕ) then (x.2 : ℕ) else (Lin K M p j).toNat) else 0

/-- The index set of the numerator `D_N⁶ E_x E_y`. -/
def Jset (K p : ℕ) : Finset ℕ := Icc 1 (Nof K) ∪ range (mHalf p + 1)

/-- The exponents of the numerator `D_N⁶ E_x E_y`. -/
def kexp (K M p : ℕ) (x y : InnerIdx K M p) (j : ℕ) : ℕ :=
  6 * (if j ∈ Icc 1 (Nof K) then 1 else 0) + nu K M p x j + nu K M p y j

theorem prod_subset_pow {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℚ[X]) (e : ℕ → ℕ)
    (he : ∀ j ∈ t, j ∉ s → e j = 0) : ∏ j ∈ s, f j ^ e j = ∏ j ∈ t, f j ^ e j :=
  prod_subset hst fun j hj hjs => by rw [he j hj hjs, pow_zero]

theorem innerBasis_eq_prod (K M p : ℕ) (x : InnerIdx K M p) :
    innerBasis K M p x = ∏ j ∈ range (mHalf p + 1), (X + C ((j : ℚ) ^ 2)) ^ nu K M p x j := by
  have hx : (x.1 : ℕ) ∈ range (mHalf p + 1) := mem_range.mpr x.1.2
  rw [innerBasis, ← mul_prod_erase (range (mHalf p + 1))
    (fun j => (X + C ((j : ℚ) ^ 2)) ^ nu K M p x j) hx]
  conv_rhs => rw [mul_comm]
  congr 1
  · refine prod_congr rfl fun c hc => ?_
    rw [mem_erase, mem_range] at hc
    have h1 : c ≤ mHalf p := by omega
    simp only [nu, h1, hc.1, ite_true, ite_false]
  · have h1 : (x.1 : ℕ) ≤ mHalf p := Nat.lt_succ_iff.mp x.1.2
    simp only [nu, h1, ite_true]

theorem numerator_eq (K M p : ℕ) (x y : InnerIdx K M p) :
    D (Nof K) ^ 6 * innerBasis K M p x * innerBasis K M p y =
      ∏ j ∈ Jset K p, (X + C ((j : ℚ) ^ 2)) ^ kexp K M p x y j := by
  have hR : range (mHalf p + 1) ⊆ Jset K p := subset_union_right
  have hI : Icc 1 (Nof K) ⊆ Jset K p := subset_union_left
  simp only [kexp, pow_add, prod_mul_distrib]
  rw [innerBasis_eq_prod, innerBasis_eq_prod,
    prod_subset_pow hR _ (nu K M p x) (fun j _ hj => by
      simp only [nu]; rw [mem_range] at hj; simp [show ¬ j ≤ mHalf p by omega]),
    prod_subset_pow hR _ (nu K M p y) (fun j _ hj => by
      simp only [nu]; rw [mem_range] at hj; simp [show ¬ j ≤ mHalf p by omega])]
  congr 2
  rw [D, ← prod_pow, ← prod_subset_pow hI _ (fun j => 6 * if j ∈ Icc 1 (Nof K) then 1 else 0)
    (fun j _ hj => by simp [hj])]
  refine prod_congr rfl fun j hj => ?_
  simp [hj]

/-! ## Counting `p`'s by class -/

/-- Multiplicity: `2` for the zero class, `1` otherwise. -/
def mult (c : ℕ) : ℕ := if c = 0 then 2 else 1

theorem omg_eq {p c : ℕ} (hp2 : p % 2 = 1) (hc : c < p) (j : ℕ) :
    omg p c j = if cls p j = cls p c then mult c else 0 := by
  have hp0 : 0 < p := by omega
  have hr : j % p < p := Nat.mod_lt _ hp0
  have e1 : (p : ℤ) ∣ (j : ℤ) - c ↔ j % p = c := by
    rw [← Nat.modEq_iff_dvd]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hc]; exact eq_comm
  have e2 : (p : ℤ) ∣ (j : ℤ) + c ↔ (j % p + c = 0 ∨ j % p + c = p) := by
    rw [show (j : ℤ) + c = ((j + c : ℕ) : ℤ) by push_cast; ring, Int.natCast_dvd_natCast,
      Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_eq_of_lt hc, mod_add_small hr hc]
  have e3 : cls p c = min c (p - c) := by unfold cls; rw [Nat.mod_eq_of_lt hc]
  unfold omg mult
  rw [e3]
  unfold cls
  simp only [e1, e2]
  split_ifs <;> omega

theorem sum_omg {p c : ℕ} (hp2 : p % 2 = 1) (hc : c < p) (A : ℕ) :
    ∑ j ∈ Icc 1 A, omg p c j = mult c * ell p A (cls p c) := by
  rw [sum_congr rfl fun j _ => omg_eq hp2 hc j, ← sum_filter, sum_const, smul_eq_mul, mul_comm]
  congr 1
  unfold ell
  congr 1
  exact filter_congr fun j _ => (classCond_iff hp2 (cls_le hp2)).symm

theorem nearCount_eq {p : ℕ} [Fact p.Prime] (K c : ℕ) :
    nearCount p K c = ∑ j ∈ Icc 1 K, omg p c j := by
  unfold nearCount signedPoles omg
  have hd : Disjoint ((Icc 1 K).image fun j : ℕ => (j : ℤ)) ((Icc 1 K).image fun j : ℕ => -(j : ℤ)) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [mem_image, mem_Icc] at h1 h2
    obtain ⟨a, ha, rfl⟩ := h1; obtain ⟨b, hb, e⟩ := h2; omega
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hd), filter_image, filter_image,
    card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    card_image_of_injective _ (fun a b h => by simpa using h), sum_add_distrib, card_filter,
    card_filter]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  congr 1
  apply propext
  rw [show -(j : ℤ) - c = -((j : ℤ) + c) by ring, dvd_neg]

theorem cls_small {p j : ℕ} (hp2 : p % 2 = 1) (hj : j ≤ mHalf p) : cls p j = j := by
  unfold cls mHalf at *
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `eNum` for the inner numerator. -/
theorem eNum_eq {K M p : ℕ} (hp2 : p % 2 = 1) (x y : InnerIdx K M p) {c : ℕ} (hc : c < p) :
    eNum p c (Jset K p) (kexp K M p x y) = 5 * (if c = 0 then 1 else 0) +
      mult c * (6 * ell p (Nof K) (cls p c) + nu K M p x (cls p c) + nu K M p y (cls p c)) := by
  have hcd : ((p : ℤ) ∣ (c : ℤ)) ↔ c = 0 := by
    rw [Int.natCast_dvd_natCast]
    constructor
    · intro hd; by_contra h0; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    · rintro rfl; exact dvd_zero _
  unfold eNum
  simp only [hcd]
  congr 1
  have hR : range (mHalf p + 1) ⊆ Jset K p := subset_union_right
  have hI : Icc 1 (Nof K) ⊆ Jset K p := subset_union_left
  have hsm : ∀ z : InnerIdx K M p, ∑ j ∈ Jset K p, nu K M p z j * omg p c j =
      mult c * nu K M p z (cls p c) := by
    intro z
    rw [← sum_subset hR (fun j _ hj => by
      simp only [nu]; rw [mem_range] at hj; simp [show ¬ j ≤ mHalf p by omega])]
    rw [sum_congr rfl fun j hj => by
      rw [omg_eq hp2 hc j, cls_small hp2 (Nat.lt_succ_iff.mp (mem_range.mp hj))]]
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq' (range (mHalf p + 1)) (cls p c) (fun j => nu K M p z j * mult c),
      if_pos (mem_range.mpr (Nat.lt_succ_of_le (cls_le hp2)))]
    ring
  have h6 : ∑ j ∈ Jset K p, 6 * (if j ∈ Icc 1 (Nof K) then 1 else 0) * omg p c j =
      6 * (mult c * ell p (Nof K) (cls p c)) := by
    rw [← sum_omg hp2 hc, Finset.mul_sum, ← sum_subset hI (fun j _ hj => by simp [hj])]
    exact sum_congr rfl fun j hj => by simp [hj]
  simp only [kexp, add_mul, sum_add_distrib, hsm, h6]
  ring

/-! ## Bounds on the dimensions and on `ℓ_K` -/

theorem count_mod_ge (A p r : ℕ) (hp : 0 < p) (hr1 : 1 ≤ r) (hr : r < p) :
    A / p ≤ ((Icc 1 A).filter fun j => j % p = r).card := by
  have : (range (A / p)).card ≤ ((Icc 1 A).filter fun j => j % p = r).card := by
    refine card_le_card_of_injOn (fun t => t * p + r) ?_ ?_
    · intro t ht
      simp only [coe_range, Set.mem_Iio] at ht
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
      have h1 : t * p + p ≤ A / p * p := by nlinarith
      have h2 := Nat.div_mul_le_self A p
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
    · intro a _ b _ hab
      simp only at hab
      have : a * p = b * p := by omega
      exact Nat.eq_of_mul_eq_mul_right hp this
  simpa using this

theorem count_mod_le (A p r : ℕ) (hp : 0 < p) (hr1 : 1 ≤ r) (hr : r < p) :
    ((Icc 1 A).filter fun j => j % p = r).card ≤ A / p + 1 := by
  have h := card_filter_mod_mul_le A p r hr
  have h2 : A < (A / p + 1) * p := by
    have := Nat.lt_div_mul_add (a := A) hp; rw [add_mul, one_mul]; omega
  by_contra hc
  push Not at hc
  have h3 : (A / p + 2) * p ≤ ((Icc 1 A).filter fun j => j % p = r).card * p :=
    Nat.mul_le_mul_right p hc
  have e : (A / p + 2) * p = (A / p + 1) * p + p := by ring
  set Xv := (A / p + 1) * p
  set Yv := ((Icc 1 A).filter fun j => j % p = r).card * p
  omega

theorem ell_bounds {p : ℕ} (hp2 : p % 2 = 1) (A a : ℕ) (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    2 * (A / p) ≤ ell p A a ∧ ell p A a ≤ 2 * (A / p) + 2 := by
  have hp0 : 0 < p := by omega
  have hap : a < p := by unfold mHalf at ha; omega
  have hsplit : (Icc 1 A).filter (fun j => j % p = a % p ∨ (j + a) % p = 0) =
      (Icc 1 A).filter (fun j => j % p = a) ∪ (Icc 1 A).filter (fun j => j % p = p - a) := by
    rw [← filter_or]
    refine filter_congr fun j _ => ?_
    have hr : j % p < p := Nat.mod_lt _ hp0
    rw [Nat.mod_eq_of_lt hap, Nat.add_mod, Nat.mod_eq_of_lt hap, mod_add_small hr hap]
    omega
  have hd : Disjoint ((Icc 1 A).filter fun j => j % p = a) ((Icc 1 A).filter fun j => j % p = p - a) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_filter] at h1 h2
    unfold mHalf at ha; omega
  unfold ell
  rw [hsplit, card_union_of_disjoint hd]
  have := count_mod_ge A p a hp0 ha1 hap
  have := count_mod_ge A p (p - a) hp0 (by omega) (by omega)
  have := count_mod_le A p a hp0 ha1 hap
  have := count_mod_le A p (p - a) hp0 (by omega) (by omega)
  omega

section Hyp

variable {K M p : ℕ} [hp : Fact p.Prime] (h : InnerHyp K M p)
include h

theorem hyp_facts : 7 ≤ p ∧ p % 2 = 1 ∧ 2 * mHalf p + 1 = p ∧ K / p < M ∧ Nof K / p < M := by
  have hodd := InnerHyp.odd h
  have hb := innerHyp_bounds h
  obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
  have hp0 : 0 < p := by omega
  refine ⟨by omega, by omega, hodd, (Nat.div_lt_iff_lt_mul hp0).mpr (by nlinarith),
    ?_⟩
  unfold Nof
  rw [show 3 * (40 * n) / 40 = 3 * n by omega]
  exact (Nat.div_lt_iff_lt_mul hp0).mpr (by nlinarith)

theorem Tin_le : Tin K M p ≤ 4 * M := by
  have hodd := InnerHyp.odd h
  have hb := (innerHyp_bounds h).1
  obtain ⟨hE0, -, hTE⟩ := TE_spec h
  obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  unfold rhs44 L0 at hTE
  rw [hN, hh] at hTE
  have hm1 : (1 : ℤ) ≤ mHalf p := by exact_mod_cast (show 1 ≤ mHalf p by omega)
  have hpM' : (40 * n : ℤ) < (2 * mHalf p + 1) * M := by exact_mod_cast (hodd ▸ hpM)
  have hq : (0 : ℤ) ≤ ((3 * n / p : ℕ) : ℤ) := by positivity
  have hM0 : (0 : ℤ) ≤ M := by positivity
  by_contra hc
  push Not at hc
  set m : ℤ := (mHalf p : ℤ)
  set T := Tin (40 * n) M p
  have h1 : m * (4 * M + 1) ≤ m * T := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (M : ℤ) ≤ m * M := by nlinarith
  push_cast at hTE
  have hq' : (0 : ℤ) ≤ 3 * (n : ℤ) / (p : ℤ) := Int.ediv_nonneg (by positivity) (by positivity)
  have hmT : m * T ≤ 46 * n := by linarith
  have e1 : m * (4 * M + 1) = 4 * (m * M) + m := by ring
  have h1' : 4 * (m * M) + m ≤ m * T := by linarith [h1, e1]
  have e2 : (2 * m + 1) * M = 2 * (m * M) + M := by ring
  have h3 : (40 : ℤ) * n < 3 * (m * M) := by linarith [hpM', e2]
  linarith

theorem Lin_le (a : ℕ) (ha : a ≤ mHalf p) : Lin K M p a ≤ 4 * M + 10 := by
  have hT := Tin_le h
  unfold Lin
  split_ifs with ha0
  · unfold L0; push_cast; linarith
  · have := epsIn_le_one K M p (defaultPos K p) a
    have : (0 : ℤ) ≤ bIn K p a := by unfold bIn; positivity
    linarith

theorem nu_le (x : InnerIdx K M p) (j : ℕ) : nu K M p x j ≤ 4 * M + 10 := by
  unfold nu
  split_ifs with h1 h2
  · have hx := x.2.2
    have := Lin_le h x.1 (Nat.lt_succ_iff.mp x.1.2)
    omega
  · have := Lin_le h j h1; omega
  · omega

theorem ellN_le (a : ℕ) (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) : ell p (Nof K) a ≤ M := by
  have hodd := InnerHyp.odd h
  have hell := ell_mul_le (p := p) (A := Nof K) ha1 (by omega)
  obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  rw [hN] at hell
  have : ell p (3 * n) a * p < (M + 1) * p := by nlinarith
  rw [hN]
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right this)

theorem eps_char (a : ℕ) :
    epsIn K M p (defaultPos K p) a = if (defaultPos K p a : ℤ) < Ein K M p then 1 else 0 := by
  unfold epsIn; rw [card_before_eq]

theorem eps_key {a b : ℕ} (ha : a ∈ Icc 1 (mHalf p)) (hb : b ∈ Icc 1 (mHalf p)) :
    2 * (epsIn K M p (defaultPos K p) a - epsIn K M p (defaultPos K p) b) ≤
      2 + (ell p K a : ℤ) - ell p K b := by
  have hp2 := (hyp_facts h).2.1
  obtain ⟨la1, la2⟩ := ell_bounds hp2 K a (mem_Icc.mp ha).1 (mem_Icc.mp ha).2
  obtain ⟨lb1, lb2⟩ := ell_bounds hp2 K b (mem_Icc.mp hb).1 (mem_Icc.mp hb).2
  rw [eps_char h, eps_char h]
  split_ifs with h1 h2 h2
  · omega
  · have hlt : defaultPos K p a < defaultPos K p b := by omega
    have := (pos_lt_iff K p ha).mp hlt
    unfold before at this
    omega
  · omega
  · omega

/-- Half-weight at an ordinary source `b`. -/
theorem half_ord (x : InnerIdx K M p) (b : ℕ) (hb1 : 1 ≤ b) (hb : b ≤ mHalf p) :
    wInIdx K M p x ≤ (nu K M p x b : ℚ) + 3 * (ell p (Nof K) b : ℚ) - ((ell p K b : ℚ) + 4) / 2 := by
  have hLb := Lin_nonneg' h b hb
  have hbne : b ≠ 0 := by omega
  have hLbq : ((Lin K M p b).toNat : ℚ) = (Tin K M p : ℚ) - 3 * (ell p (Nof K) b : ℚ) +
      (epsIn K M p (defaultPos K p) b : ℚ) := by
    have : ((Lin K M p b).toNat : ℤ) = Lin K M p b := Int.toNat_of_nonneg hLb
    have e2 : ((Lin K M p b).toNat : ℚ) = ((Lin K M p b : ℤ) : ℚ) := by exact_mod_cast this
    rw [e2]; unfold Lin bIn; rw [if_neg hbne]; push_cast; ring
  obtain ⟨a, i⟩ := x
  simp only [wInIdx, wIn, nu, if_pos hb]
  by_cases ha0 : (a : ℕ) = 0
  · rw [if_pos ha0, if_neg (by omega), hLbq]
    rw [Finset.fold_min_le]
    right
    refine ⟨b, mem_Icc.mpr ⟨hb1, hb⟩, le_of_eq ?_⟩
    unfold Zin; push_cast; ring
  · rw [if_neg ha0]
    by_cases hba : b = (a : ℕ)
    · rw [if_pos hba]; subst hba; unfold bIn; push_cast; ring_nf; rfl
    · rw [if_neg hba, hLbq]
      have hLa := Lin_nonneg' h a (Nat.lt_succ_iff.mp a.2)
      have hi : ((i : ℕ) : ℤ) + 1 ≤ Lin K M p a := by
        have := i.2; have : ((Lin K M p a).toNat : ℤ) = Lin K M p a := Int.toNat_of_nonneg hLa
        omega
      have hLdef : Lin K M p a = Tin K M p - bIn K p a + epsIn K M p (defaultPos K p) a := by
        unfold Lin; rw [if_neg ha0]
      have key := eps_key h (a := a) (b := b) (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr ha0,
        Nat.lt_succ_iff.mp a.2⟩) (mem_Icc.mpr ⟨hb1, hb⟩)
      have hi' : ((i : ℕ) : ℚ) + (bIn K p a : ℚ) + 1 ≤ (Tin K M p : ℚ) +
          (epsIn K M p (defaultPos K p) a : ℚ) := by exact_mod_cast (by linarith : _)
      have key' : 2 * ((epsIn K M p (defaultPos K p) a : ℚ) - epsIn K M p (defaultPos K p) b) ≤
          2 + (ell p K a : ℚ) - ell p K b := by exact_mod_cast key
      linarith

/-- Half-weight at the zero source. -/
theorem half_zero (x : InnerIdx K M p) :
    wInIdx K M p x ≤ 2 * (nu K M p x 0 : ℚ) + 6 * ((Nof K / p : ℕ) : ℚ) - ((K / p : ℕ) : ℚ) + 1 / 2 := by
  obtain ⟨a, i⟩ := x
  simp only [wInIdx, wIn, nu, if_pos (Nat.zero_le _)]
  by_cases ha0 : (a : ℕ) = 0
  · rw [if_pos ha0, if_pos ha0.symm, Finset.fold_min_le]
    left; rfl
  · rw [if_neg ha0, if_neg (Ne.symm ha0)]
    have hT := Tin_le h
    have hKp := (hyp_facts h).2.2.2.1
    have hLa := Lin_nonneg' h a (Nat.lt_succ_iff.mp a.2)
    have hi : ((i : ℕ) : ℤ) + 1 ≤ Lin K M p a := by
      have := i.2; have : ((Lin K M p a).toNat : ℤ) = Lin K M p a := Int.toNat_of_nonneg hLa
      omega
    have hLdef : Lin K M p a = Tin K M p - bIn K p a + epsIn K M p (defaultPos K p) a := by
      unfold Lin; rw [if_neg ha0]
    have he := epsIn_le_one K M p (defaultPos K p) a
    have hL0 : (Lin K M p 0).toNat = 4 * M + 10 := by simp [Lin, L0]; omega
    rw [hL0]
    have h1 : ((i : ℕ) : ℚ) + (bIn K p a : ℚ) ≤ 4 * M := by
      have : ((i : ℕ) : ℤ) + bIn K p a ≤ 4 * M := by linarith
      exact_mod_cast this
    have h2 : ((K / p : ℕ) : ℚ) ≤ M := by exact_mod_cast hKp.le
    have h3 : (0 : ℚ) ≤ (ell p K a : ℚ) := by positivity
    have h4 : (0 : ℚ) ≤ ((Nof K / p : ℕ) : ℚ) := by positivity
    push_cast
    linarith

end Hyp

/-! ## The entry bound and Proposition 4.1 -/

theorem cls_zero (p : ℕ) : cls p 0 = 0 := by simp [cls]

theorem cls_pos {p c : ℕ} (hc0 : c ≠ 0) (hc : c < p) : 1 ≤ cls p c := by
  unfold cls; rw [Nat.mod_eq_of_lt hc]; omega

/-- **(4.2)/(4.3)**: every entry of the Gram matrix in the inner basis has Gauss valuation at least
the sum of its two row weights. -/
theorem innerGram_entry_bound' {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p)
    (x y : InnerIdx K M p) :
    vpGge p (innerGram K M p x y) (wInIdx K M p x + wInIdx K M p y) := by
  obtain ⟨hp7, hp2, hodd, hKp, hNp⟩ := hyp_facts h
  have hb := innerHyp_bounds h
  have hM := h.1
  have hK1 : 2 * K < p ^ 2 := by omega
  have hK2 : K + p < p ^ 2 := by nlinarith
  rw [innerGram, Matrix.of_apply, numerator_eq]
  apply entry_generic hp7 K hK1 hK2
  · intro c hc
    rw [eNum_eq hp2 x y hc, nearCount_eq, sum_omg hp2 hc]
    by_cases hc0 : c = 0
    · subst hc0
      have hx := half_zero h x
      have hy := half_zero h y
      simp only [cls_zero, mult, ite_true, ell_zero_eq]
      push_cast
      linarith
    · have hcl1 := cls_pos hc0 hc
      have hcl2 := cls_le (j := c) hp2
      have hx := half_ord h x (cls p c) hcl1 hcl2
      have hy := half_ord h y (cls p c) hcl1 hcl2
      simp only [mult, hc0, ite_false]
      push_cast
      linarith
  · intro c hc
    rw [eNum_eq hp2 x y hc]
    by_cases hc0 : c = 0
    · subst hc0
      have := nu_le h x 0
      have := nu_le h y 0
      simp only [cls_zero, mult, ite_true, ell_zero_eq]
      omega
    · have hcl1 := cls_pos hc0 hc
      have hcl2 := cls_le (j := c) hp2
      have := nu_le h x (cls p c)
      have := nu_le h y (cls p c)
      have := ellN_le h (cls p c) hcl1 hcl2
      simp only [mult, hc0, ite_false]
      omega

/-- **Proposition 4.1**: under (4.1), `v_p^G(Δ_K) ≥ γ_p^in`. -/
theorem prop_4_1' {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    vpGge p (Delta K) (gammaIn K M p) := prop_4_1_of_entries h (innerGram_entry_bound' h)

/-- **Proposition 4.1**: under (4.1), `v_p^G(Δ_K) ≥ γ_p^in`. -/
theorem prop_4_1 {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    vpGge p (Delta K) (gammaIn K M p) := prop_4_1' h

theorem innerGram_entry_bound {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p)
    (x y : InnerIdx K M p) :
    vpGge p (innerGram K M p x y) (wInIdx K M p x + wInIdx K M p y) := innerGram_entry_bound' h x y

end Zeta5
