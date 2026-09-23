import Zeta5.IntValued

/-!
# Lemma 3.3

`v_p^G(τ_X((K!)² A(x) / ∏_{0<|r|≤K} (x - r))) ≥ -6⌊log_p max(2K, d+1)⌋ - v_p(24)` for an
integer-valued `A` of degree `≤ d`.
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

/-! ## Counting multiples in an interval -/

/-- At most `2⌊K/q⌋ + 2` elements of `[-K, K]` lie in one residue class mod `q`, and at most one
if `q > 2K`. -/
theorem card_filter_dvd_Icc_le (K q : ℕ) (hq : 0 < q) (x : ℤ) :
    #{s ∈ Icc (-(K : ℤ)) K | (q : ℤ) ∣ x - s} ≤ (2 * K) / q + 1 := by
  set S := {s ∈ Icc (-(K : ℤ)) K | (q : ℤ) ∣ x - s}
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hinj : Set.InjOn (fun s : ℤ => (s + K) / (q : ℤ)) S := by
    intro s1 hs1 s2 hs2 heq
    simp only [S, coe_filter, Set.mem_ofPred_eq, mem_Icc] at hs1 hs2
    have hd : (q : ℤ) ∣ s1 - s2 := by
      have := dvd_sub hs2.2 hs1.2
      rw [show x - s2 - (x - s1) = s1 - s2 by ring] at this; exact this
    have hm : (s1 + K) % q = (s2 + K) % q := by
      have : (s1 + K) ≡ (s2 + K) [ZMOD q] := Int.modEq_iff_dvd.mpr (by
        rw [show (s2 + K) - (s1 + K) = -(s1 - s2) by ring]; exact dvd_neg.mpr hd)
      exact this
    have e1 := Int.mul_ediv_add_emod (s1 + K) q
    have e2 := Int.mul_ediv_add_emod (s2 + K) q
    simp only at heq
    rw [heq, hm] at e1
    linarith
  have hmaps : Set.MapsTo (fun s : ℤ => (s + K) / (q : ℤ)) S (Icc 0 ((2 * K : ℕ) / (q : ℤ))) := by
    intro s hs
    simp only [S, coe_filter, Set.mem_ofPred_eq, mem_Icc] at hs
    simp only [coe_Icc, Set.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by linarith) hq'.le
    · exact Int.ediv_le_ediv hq' (by push_cast; linarith)
  have := card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at this
  rw [← Int.natCast_ediv] at this
  generalize 2 * K / q = m at this ⊢
  omega

theorem two_mul_div_le (K q : ℕ) (hq : 0 < q) : 2 * K / q ≤ 2 * (K / q) + 1 := by
  have h := Nat.div_add_mod K q
  have hr := Nat.mod_lt K hq
  have : 2 * K < q * (2 * (K / q) + 2) := by nlinarith
  have := (Nat.div_lt_iff_lt_mul hq).mpr (by linarith [this] : 2 * K < (2 * (K / q) + 2) * q)
  omega

/-! ## Valuations as counts -/

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValInt_eq_card (z : ℤ) (hz : z ≠ 0) (B : ℕ) (hB : padicValInt p z < B) :
    padicValInt p z = #{j ∈ Ico 1 B | (p : ℤ) ^ j ∣ z} := by
  have : {j ∈ Ico 1 B | (p : ℤ) ^ j ∣ z} = Ico 1 (padicValInt p z + 1) := by
    ext j
    simp only [mem_filter, mem_Ico, padicValInt_dvd_iff, hz, false_or]
    omega
  rw [this, Nat.card_Ico]; omega

theorem sum_padicValInt_le (x : ℤ) (T : Finset ℤ) (hx : ∀ s ∈ T, x - s ≠ 0) (B : ℕ)
    (hB : ∀ s ∈ T, padicValInt p (x - s) < B) (c : ℕ → ℕ)
    (hc : ∀ j ∈ Ico 1 B, #{s ∈ T | (p : ℤ) ^ j ∣ x - s} ≤ c j) :
    ∑ s ∈ T, padicValInt p (x - s) ≤ ∑ j ∈ Ico 1 B, c j := by
  classical
  calc ∑ s ∈ T, padicValInt p (x - s)
      = ∑ s ∈ T, ∑ j ∈ Ico 1 B, if (p : ℤ) ^ j ∣ x - s then 1 else 0 := by
        refine sum_congr rfl fun s hs => ?_
        rw [padicValInt_eq_card _ (hx s hs) B (hB s hs), card_filter]
    _ = ∑ j ∈ Ico 1 B, #{s ∈ T | (p : ℤ) ^ j ∣ x - s} := by
        rw [sum_comm]; exact sum_congr rfl fun j _ => (card_filter _ _).symm
    _ ≤ _ := sum_le_sum hc

theorem padicValRat_prod {ι : Type*} (T : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ T, f i ≠ 0) :
    padicValRat p (∏ i ∈ T, f i) = ∑ i ∈ T, padicValRat p (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a T))
      (prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- The factorial ratio `(K!)² / ∏_{s ∈ T} (x - s)`, from per-level counts: if at each level `j`
at most `2⌊K/p^j⌋ + e·[j ≤ L₀]` of the `x - s` are divisible by `p^j`, the ratio has
`v_p ≥ -e L₀`, where `L₀ = ⌊log_p 2K⌋`. -/
theorem vge_factorial_sq_div_prod (K : ℕ) (x : ℤ) (T : Finset ℤ) (hx : ∀ s ∈ T, x - s ≠ 0)
    (e : ℕ) (hc : ∀ j, 1 ≤ j → #{s ∈ T | (p : ℤ) ^ j ∣ x - s} ≤
      2 * (K / p ^ j) + (if j ≤ Nat.log p (2 * K) then e else 0)) :
    vge p ((K.factorial : ℚ) ^ 2 / ∏ s ∈ T, ((x : ℚ) - s)) (-(e * Nat.log p (2 * K) : ℚ)) := by
  classical
  set L0 := Nat.log p (2 * K)
  set B := ∑ s ∈ T, padicValInt p (x - s) + L0 + Nat.log p K + 1
  have hB : ∀ s ∈ T, padicValInt p (x - s) < B := fun s hs => by
    have := single_le_sum (f := fun s => padicValInt p (x - s)) (fun _ _ => Nat.zero_le _) hs
    omega
  have hsum := sum_padicValInt_le x T hx B hB _ fun j hj => hc j (mem_Ico.mp hj).1
  rw [sum_add_distrib, ← mul_sum, ← padicValNat_factorial (by omega : Nat.log p K < B),
    ← sum_filter, sum_const, smul_eq_mul] at hsum
  have hcard : #{j ∈ Ico 1 B | j ≤ L0} = L0 := by
    have : {j ∈ Ico 1 B | j ≤ L0} = Ico 1 (L0 + 1) := by
      ext j; simp only [mem_filter, mem_Ico]; omega
    rw [this, Nat.card_Ico]; omega
  rw [hcard] at hsum
  have hprod : ∏ s ∈ T, ((x : ℚ) - s) ≠ 0 :=
    prod_ne_zero_iff.mpr fun s hs => by exact_mod_cast hx s hs
  intro _
  rw [padicValRat.div (by positivity) hprod, padicValRat.pow,
    padicValRat_prod T _ fun s hs => by exact_mod_cast hx s hs]
  have hs : ∑ s ∈ T, padicValRat p ((x : ℚ) - s) = ((∑ s ∈ T, padicValInt p (x - s) : ℕ) : ℤ) := by
    push_cast
    exact sum_congr rfl fun s _ => by rw [← padicValRat.of_int]; push_cast; rfl
  rw [hs]
  push_cast
  have : (∑ s ∈ T, padicValInt p (x - s) : ℚ) ≤ 2 * padicValNat p K.factorial + L0 * e := by
    exact_mod_cast hsum
  have hf : ((padicValRat p (K.factorial : ℚ) : ℤ) : ℚ) = (padicValNat p K.factorial : ℚ) := by
    rw [padicValRat.of_nat]; rfl
  linarith

/-! ## The three counting estimates -/

omit hp in
theorem card_filter_dvd_le (K q : ℕ) (hq : 0 < q) (x : ℤ) (T : Finset ℤ)
    (hT : T ⊆ Icc (-(K : ℤ)) K) : #{s ∈ T | (q : ℤ) ∣ x - s} ≤ 2 * K / q + 1 :=
  (card_le_card (filter_subset_filter _ hT)).trans (card_filter_dvd_Icc_le K q hq x)

omit hp in
/-- If `x₀ ∈ [-K, K] \ T` is in the residue class, the count drops by one. -/
theorem card_filter_dvd_le_excl (K q : ℕ) (hq : 0 < q) (x x0 : ℤ) (T : Finset ℤ)
    (hT : T ⊆ Icc (-(K : ℤ)) K) (hx0 : x0 ∈ Icc (-(K : ℤ)) K) (hx0T : x0 ∉ T)
    (hd : (q : ℤ) ∣ x - x0) : #{s ∈ T | (q : ℤ) ∣ x - s} ≤ 2 * K / q := by
  have hsub : insert x0 {s ∈ T | (q : ℤ) ∣ x - s} ⊆ {s ∈ Icc (-(K : ℤ)) K | (q : ℤ) ∣ x - s} := by
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact mem_filter.mpr ⟨hx0, hd⟩
    · exact filter_subset_filter _ hT hs
  have := (card_le_card hsub).trans (card_filter_dvd_Icc_le K q hq x)
  rw [card_insert_of_notMem (fun h => hx0T (mem_filter.mp h).1)] at this
  omega

theorem lt_pow_log_succ (K : ℕ) : 2 * K < p ^ (Nat.log p (2 * K) + 1) :=
  Nat.lt_pow_succ_log_self hp.out.one_lt _

theorem div_eq_zero_of_gt_log (K j : ℕ) (hj : Nat.log p (2 * K) < j) : 2 * K / p ^ j = 0 :=
  Nat.div_eq_of_lt ((lt_pow_log_succ K).trans_le
    (Nat.pow_le_pow_right hp.out.pos (by omega)))

/-! ## The product-difference estimate -/

theorem padicValRat_add_of_lt {a u : ℚ} (ha : a ≠ 0) (hu : u ≠ 0)
    (h : padicValRat p a < padicValRat p u) : a + u ≠ 0 ∧ padicValRat p (a + u) = padicValRat p a := by
  have hau : a + u ≠ 0 := by
    intro h0
    have : u = -a := by linarith
    rw [this, padicValRat.neg] at h; exact lt_irrefl _ h
  exact ⟨hau, by rw [padicValRat.add_eq_min hau ha hu h.ne, min_eq_left h.le]⟩

/-- `v(∏(aᵢ + u) - ∏ aᵢ) ≥ v(u) - L + ∑ v(aᵢ)` when every `v(aᵢ) ≤ L < v(u)`. -/
theorem vge_prod_add_sub_prod {ι : Type*} (s : Finset ι) (a : ι → ℚ) (u L : ℚ) (hu : u ≠ 0)
    (ha0 : ∀ i ∈ s, a i ≠ 0) (haL : ∀ i ∈ s, (padicValRat p (a i) : ℚ) ≤ L)
    (hL : L < padicValRat p u) :
    vge p (∏ i ∈ s, (a i + u) - ∏ i ∈ s, a i)
      (padicValRat p u - L + ∑ i ∈ s, (padicValRat p (a i) : ℚ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vge_zero (p := p) _
  | insert b s hb ih =>
    have ha0' : ∀ i ∈ s, a i ≠ 0 := fun i hi => ha0 i (mem_insert_of_mem hi)
    have haL' : ∀ i ∈ s, (padicValRat p (a i) : ℚ) ≤ L := fun i hi => haL i (mem_insert_of_mem hi)
    have hlt : ∀ i ∈ insert b s, padicValRat p (a i) < padicValRat p u := fun i hi => by
      have := haL i hi; exact_mod_cast this.trans_lt hL
    rw [prod_insert hb, prod_insert hb, sum_insert hb,
      show (a b + u) * ∏ i ∈ s, (a i + u) - a b * ∏ i ∈ s, a i =
        a b * (∏ i ∈ s, (a i + u) - ∏ i ∈ s, a i) + u * ∏ i ∈ s, (a i + u) by ring]
    refine vge_add ?_ ?_
    · have hab : vge p (a b) (padicValRat p (a b)) := fun _ => le_refl _
      exact vge_mono (vge_mul hab (ih ha0' haL')) (le_of_eq (by ring))
    · have hP : ∏ i ∈ s, (a i + u) ≠ 0 :=
        prod_ne_zero_iff.mpr fun i hi => (padicValRat_add_of_lt (ha0' i hi) hu
          (hlt i (mem_insert_of_mem hi))).1
      intro h0
      rw [padicValRat.mul hu hP, padicValRat_prod s _ fun i hi => (padicValRat_add_of_lt (ha0' i hi) hu
          (hlt i (mem_insert_of_mem hi))).1]
      rw [sum_congr rfl fun i hi => (padicValRat_add_of_lt (ha0' i hi) hu
          (hlt i (mem_insert_of_mem hi))).2]
      push_cast
      linarith [haL b (mem_insert_self b s)]

/-! ## Partial fractions with linear poles -/

omit hp in
theorem linPoleProd_natDegree (S : Finset ℤ) : (linPoleProd S).natDegree = S.card := by
  rw [linPoleProd, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  exact (sum_congr rfl fun j _ => natDegree_X_sub_C _).trans (by simp)

omit hp in
/-- Lagrange: `P mod ∏(x - r) = ∑_r res_r ∏_{s ≠ r} (x - s)`. -/
theorem modByMonic_linPoleProd (S : Finset ℤ) (P : ℚ[X]) :
    P %ₘ linPoleProd S = ∑ r ∈ S, C (linResidue S P r) * linPoleProd (S.erase r) := by
  classical
  set nodes := S.image fun r : ℤ => (r : ℚ)
  have hcard : nodes.card = S.card := card_image_of_injective _ Int.cast_injective
  apply eq_of_degrees_lt_of_eval_finset_eq nodes
  · rw [hcard]
    calc _ < degree (linPoleProd S) := degree_modByMonic_lt _ (linPoleProd_monic S)
      _ = S.card := by
        rw [degree_eq_natDegree (linPoleProd_monic S).ne_zero, linPoleProd_natDegree]
  · rw [hcard, ← mem_degreeLT]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_degreeLT, degree_eq_natDegree (linPoleProd_monic _).ne_zero, linPoleProd_natDegree,
      card_erase_of_mem hj]
    have : 0 < S.card := card_pos.mpr ⟨j, hj⟩
    exact_mod_cast Nat.sub_lt this one_pos
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    have hQ : (linPoleProd S).eval (k : ℚ) = 0 := by
      rw [linPoleProd, eval_prod]
      exact prod_eq_zero hk (by simp)
    have hmod := modByMonic_add_div P (linPoleProd S)
    have hl : (P %ₘ linPoleProd S).eval (k : ℚ) = P.eval (k : ℚ) := by
      conv_rhs => rw [← hmod]
      simp [hQ]
    rw [hl, eval_finsetSum, sum_eq_single k]
    · rw [eval_mul, eval_C, linResidue, linPoleProd, eval_prod]
      have hne : ∏ l ∈ S.erase k, ((k : ℚ) - l) ≠ 0 :=
        prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr (by exact_mod_cast (ne_of_mem_erase hl).symm)
      have : ∏ l ∈ S.erase k, eval (k : ℚ) (X - C (l : ℚ)) = ∏ l ∈ S.erase k, ((k : ℚ) - l) :=
        prod_congr rfl fun l _ => by simp
      rw [this, div_mul_cancel₀ _ hne]
    · intro j hj hjk
      rw [eval_mul, linPoleProd, eval_prod,
        prod_eq_zero (mem_erase.mpr ⟨fun h => hjk h.symm, hk⟩) (by simp), mul_zero]
    · intro h; exact absurd hk h

omit hp in
/-- Evaluating the partial fraction decomposition away from the poles. -/
theorem eval_divByMonic_linPoleProd (S : Finset ℤ) (P : ℚ[X]) (n : ℚ)
    (hn : ∀ r ∈ S, n - r ≠ 0) :
    (P /ₘ linPoleProd S).eval n =
      P.eval n / ∏ r ∈ S, (n - r) - ∑ r ∈ S, linResidue S P r / (n - r) := by
  have hPi : (linPoleProd S).eval n = ∏ r ∈ S, (n - r) := by
    rw [linPoleProd, eval_prod]; simp
  have hne : ∏ r ∈ S, (n - r) ≠ 0 := prod_ne_zero_iff.mpr hn
  have hmod := modByMonic_add_div P (linPoleProd S)
  have hP : P.eval n = ∑ r ∈ S, linResidue S P r * ∏ s ∈ S.erase r, (n - s) +
      (∏ r ∈ S, (n - r)) * (P /ₘ linPoleProd S).eval n := by
    conv_lhs => rw [← hmod]
    rw [modByMonic_linPoleProd, eval_add, eval_mul, hPi, eval_finsetSum]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [eval_mul, eval_C, linPoleProd, eval_prod]
    simp
  rw [hP, add_div, mul_div_cancel_left₀ _ hne, sum_div]
  have : ∀ r ∈ S, (linResidue S P r * ∏ s ∈ S.erase r, (n - s)) / ∏ r ∈ S, (n - r) =
      linResidue S P r / (n - r) := by
    intro r hr
    rw [← mul_prod_erase S (fun s => n - s) hr,
      mul_div_mul_right _ _ (prod_ne_zero_iff.mpr fun s hs => hn s (mem_of_mem_erase hs))]
  rw [sum_congr rfl this]
  ring

/-! ## Valuations of integers -/

theorem padicValRat_int_le_log (z : ℤ) (_hz : z ≠ 0) (M : ℕ) (hzM : z.natAbs ≤ M) :
    (padicValRat p z : ℚ) ≤ Nat.log p M := by
  rw [padicValRat.of_int, padicValInt]
  exact_mod_cast (padicValNat_le_nat_log _).trans (Nat.log_mono_right hzM)

theorem lt_padicValRat_of_dvd (z : ℤ) (hz : z ≠ 0) (k : ℕ) (h : (p : ℤ) ^ (k + 1) ∣ z) :
    (k : ℚ) < padicValRat p z := by
  rw [padicValRat.of_int]
  have := ((padicValInt_dvd_iff (k + 1) z).mp h).resolve_left hz
  exact_mod_cast (show (k : ℤ) < padicValInt p z by omega)

theorem vge_inv_int (z : ℤ) (_hz : z ≠ 0) (k : ℕ) (h : ¬ (p : ℤ) ^ (k + 1) ∣ z) :
    vge p (1 / (z : ℚ)) (-(k : ℚ)) := by
  intro _
  rw [one_div, padicValRat.inv, padicValRat.of_int]
  have : padicValInt p z ≤ k := by
    by_contra hc
    exact h ((padicValInt_dvd_iff (k + 1) z).mpr (Or.inr (by omega)))
  push_cast
  exact_mod_cast (show -(k : ℤ) ≤ -(padicValInt p z : ℤ) by omega)

/-! ## Lemma 3.3 -/

omit hp in
theorem mem_R {K : ℕ} {r : ℤ} (hr : r ∈ (Icc (-(K : ℤ)) K).erase 0) :
    r ≠ 0 ∧ -(K : ℤ) ≤ r ∧ r ≤ K := by
  simp only [mem_erase, mem_Icc] at hr; exact ⟨hr.1, hr.2⟩

/-- The pole values `H^{(5)}_m` for `m ≤ K` have `v_p ≥ -5⌊log_p K⌋`. -/
theorem vge_H5 (K m : ℕ) (hm : m ≤ K) : vge p (H5 m) (-5 * Nat.log p K) := by
  unfold H5
  refine vge_sum _ _ fun v hv => ?_
  simp only [mem_Icc] at hv
  intro _
  have hv0 : (v : ℚ) ≠ 0 := by exact_mod_cast (show v ≠ 0 by omega)
  rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have : padicValNat p v ≤ Nat.log p K :=
    (padicValNat_le_nat_log v).trans (Nat.log_mono_right (by omega))
  push_cast
  have : (padicValNat p v : ℚ) ≤ Nat.log p K := by exact_mod_cast this
  have hv' : ((padicValRat p (v : ℚ) : ℤ) : ℚ) = padicValNat p v := by rw [padicValRat.of_nat]; rfl
  linarith

omit hp in
theorem natAbs_sub_le_of_mem {K : ℕ} {r s : ℤ} (hr : r ∈ (Icc (-(K : ℤ)) K).erase 0)
    (hs : s ∈ (Icc (-(K : ℤ)) K).erase 0) : (r - s).natAbs ≤ 2 * K := by
  obtain ⟨-, h1, h2⟩ := mem_R hr
  obtain ⟨-, h3, h4⟩ := mem_R hs
  have : ((r - s).natAbs : ℤ) ≤ 2 * K := by
    rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨by omega, by omega⟩
  omega

omit hp in
theorem dIdx_le {K : ℕ} {r : ℤ} (hr : r ∈ (Icc (-(K : ℤ)) K).erase 0) : dIdx r ≤ K := by
  obtain ⟨h0, h1, h2⟩ := mem_R hr
  unfold dIdx; split_ifs <;> omega

theorem vpGge_X : vpGge p (X : ℚ[X]) 0 := fun n => by
  rw [coeff_X]; split_ifs
  · exact vge_one
  · exact vge_zero _

/-- **Lemma 3.3**, (3.10). -/
theorem lemma_3_3' (p : ℕ) [Fact p.Prime] (K d : ℕ) (A : ℚ[X]) (hA : IntValuedAt p A)
    (hd : A.natDegree ≤ d) :
    vpGge p (tauX ((Icc (-(K : ℤ)) K).erase 0) (C ((K.factorial : ℚ) ^ 2) * A))
      (-6 * Nat.log p (max (2 * K) (d + 1)) - padicValNat p 24) := by
  classical
  set R := (Icc (-(K : ℤ)) K).erase 0 with hRdef
  set G := C ((K.factorial : ℚ) ^ 2) * A with hG
  set L0 := Nat.log p (2 * K) with hL0def
  set Ld := Nat.log p (max 1 d) with hLddef
  set L' := Nat.log p (max (2 * K) (d + 1)) with hL'def
  have hL0 : L0 ≤ L' := Nat.log_mono_right (le_max_left _ _)
  have hLd : Ld ≤ L' := Nat.log_mono_right (by omega)
  have hLd1 : Nat.log p (d + 1) ≤ L' := Nat.log_mono_right (le_max_right _ _)
  have hLK : Nat.log p K ≤ L' := Nat.log_mono_right (by omega)
  have hRsub : R ⊆ Icc (-(K : ℤ)) K := erase_subset _ _
  have hGeval : ∀ x : ℚ, G.eval x = (K.factorial : ℚ) ^ 2 * A.eval x := fun x => by
    simp [hG]
  have hpj : ∀ j, 0 < p ^ j := fun j => pow_pos (Fact.out : p.Prime).pos j
  -- (a) residues
  have hF0 : ∀ r ∈ R, vge p ((K.factorial : ℚ) ^ 2 / ∏ s ∈ R.erase r, ((r : ℚ) - s)) (-(1 * L0 : ℚ)) := by
    intro r hr
    refine vge_factorial_sq_div_prod K r (R.erase r) (fun s hs => sub_ne_zero.mpr (ne_of_mem_erase hs).symm) 1
      fun j hj => ?_
    have := card_filter_dvd_le_excl K (p ^ j) (hpj j) r r (R.erase r)
      ((erase_subset _ _).trans hRsub) (hRsub hr) (notMem_erase r R) (by simp)
    push_cast at this
    split_ifs with hjL
    · exact this.trans (two_mul_div_le K _ (hpj j))
    · rw [div_eq_zero_of_gt_log K j (by omega)] at this; omega
  have hres : ∀ r ∈ R, vge p (linResidue R G r) (-(L0 : ℚ)) := by
    intro r hr
    have : linResidue R G r = A.eval (r : ℚ) * ((K.factorial : ℚ) ^ 2 / ∏ s ∈ R.erase r, ((r : ℚ) - s)) := by
      rw [linResidue, hGeval]; ring
    rw [this]
    have := vge_mul (hA.vge r) (hF0 r hr)
    exact vge_mono this (by simp)
  -- (c) the polynomial part
  set Q := G /ₘ linPoleProd R with hQdef
  have hQd : Q.natDegree ≤ d := by
    rw [hQdef, natDegree_divByMonic _ (linPoleProd_monic R)]
    exact (Nat.sub_le _ _).trans ((natDegree_C_mul_le _ _).trans hd)
  set a : ℚ := ((L0 + max L0 Ld : ℕ) : ℚ) with ha
  have h2L0 : -(2 * L0 : ℚ) ≥ -a := by
    rw [ha]; push_cast; have : (L0 : ℚ) ≤ max (L0 : ℚ) (Ld : ℚ) := le_max_left _ _
    linarith
  have hLdL0 : -((Ld : ℚ) + L0) ≥ -a := by
    rw [ha]; push_cast; have : (Ld : ℚ) ≤ max (L0 : ℚ) (Ld : ℚ) := le_max_right _ _
    linarith
  have hval : ∀ i ≤ d, vge p (Q.eval ((((K : ℤ) + 1 : ℤ) : ℚ) + i)) (-a) := by
    intro i _
    set n : ℤ := K + 1 + i with hn
    have hncast : ((((K : ℤ) + 1 : ℤ) : ℚ) + (i : ℚ)) = (n : ℚ) := by push_cast [hn]; ring
    rw [hncast]
    have hnr : ∀ r ∈ R, n - r ≠ 0 := fun r hr => by have := (mem_R hr).2.2; omega
    have hnrq : ∀ r ∈ R, (n : ℚ) - r ≠ 0 := fun r hr => by exact_mod_cast hnr r hr
    rw [eval_divByMonic_linPoleProd R G n hnrq, hGeval]
    -- a pole term `c_r/(n - r)` with `v(n - r) ≤ L₀`
    have hterm : ∀ r ∈ R, ¬ (p : ℤ) ^ (L0 + 1) ∣ n - r →
        vge p (linResidue R G r / ((n : ℚ) - r)) (-a) := by
      intro r hr hnd
      have := vge_mul (hres r hr) (vge_inv_int (n - r) (hnr r hr) L0 hnd)
      rw [mul_one_div] at this
      push_cast at this
      exact vge_mono this (by linarith)
    by_cases hB : ∃ r0 ∈ R, (p : ℤ) ^ (L0 + 1) ∣ n - r0
    · -- Case B: `n` is `p`-adically close to exactly one pole `r0`
      obtain ⟨r0, hr0, hdiv⟩ := hB
      set T := R.erase r0 with hT
      have hTsub : T ⊆ Icc (-(K : ℤ)) K := (erase_subset _ _).trans hRsub
      have hsep : ∀ s ∈ T, ¬ (p : ℤ) ^ (L0 + 1) ∣ r0 - s := by
        intro s hs hd'
        have hs0 : r0 - s ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hs).symm
        have hlt : (r0 - s).natAbs < ((p : ℤ) ^ (L0 + 1)).natAbs := by
          rw [Int.natAbs_pow, Int.natAbs_natCast]
          exact (natAbs_sub_le_of_mem hr0 (mem_of_mem_erase hs)).trans_lt (lt_pow_log_succ K)
        exact hs0 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd' hlt)
      have hu : (n : ℚ) - r0 ≠ 0 := hnrq r0 hr0
      have hP1 : ∏ s ∈ T, ((r0 : ℚ) - s) ≠ 0 :=
        prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (by exact_mod_cast (ne_of_mem_erase hs).symm)
      have hP2 : ∏ s ∈ T, ((n : ℚ) - s) ≠ 0 :=
        prod_ne_zero_iff.mpr fun s hs => hnrq s (mem_of_mem_erase hs)
      -- `F(n) = (K!)² / ∏_{s ≠ r0} (n - s)` has `v ≥ -L₀`
      have hFn : vge p ((K.factorial : ℚ) ^ 2 / ∏ s ∈ T, ((n : ℚ) - s)) (-(1 * L0 : ℚ)) := by
        refine vge_factorial_sq_div_prod K n T (fun s hs => hnr s (mem_of_mem_erase hs)) 1
          fun j hj => ?_
        split_ifs with hjL
        · have hdj : ((p ^ j : ℕ) : ℤ) ∣ n - r0 := by
            push_cast; exact dvd_trans (pow_dvd_pow _ (by omega)) hdiv
          have := card_filter_dvd_le_excl K (p ^ j) (hpj j) n r0 T hTsub (hRsub hr0)
            (notMem_erase r0 R) hdj
          push_cast at this
          exact this.trans (two_mul_div_le K _ (hpj j))
        · have : {s ∈ T | (p : ℤ) ^ j ∣ n - s} = ∅ := by
            refine filter_eq_empty_iff.mpr fun s hs hds => hsep s hs ?_
            have h1 : (p : ℤ) ^ (L0 + 1) ∣ n - s := dvd_trans (pow_dvd_pow _ (by omega)) hds
            have := dvd_sub h1 hdiv
            rwa [show n - s - (n - r0) = r0 - s by ring] at this
          rw [this, card_empty]; omega
      -- `(P₁ - P₂)/(P₁ u)` has `v ≥ -L₀`
      have hPD : vge p ((∏ s ∈ T, ((r0 : ℚ) - s) - ∏ s ∈ T, ((n : ℚ) - s)) /
          ((∏ s ∈ T, ((r0 : ℚ) - s)) * ((n : ℚ) - r0))) (-(L0 : ℚ)) := by
        have ha0 : ∀ s ∈ T, (r0 : ℚ) - s ≠ 0 := fun s hs =>
          sub_ne_zero.mpr (by exact_mod_cast (ne_of_mem_erase hs).symm)
        have haL : ∀ s ∈ T, (padicValRat p ((r0 : ℚ) - s) : ℚ) ≤ L0 := by
          intro s hs
          have h0 : r0 - s ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hs).symm
          have := padicValRat_int_le_log (p := p) (r0 - s) h0 (2 * K)
            (natAbs_sub_le_of_mem hr0 (mem_of_mem_erase hs))
          push_cast at this; exact this
        have hL : (L0 : ℚ) < padicValRat p ((n : ℚ) - r0) := by
          have := lt_padicValRat_of_dvd (p := p) (n - r0) (hnr r0 hr0) L0 hdiv
          push_cast at this; exact this
        have key := vge_prod_add_sub_prod (p := p) T (fun s => (r0 : ℚ) - s) ((n : ℚ) - r0) L0 hu
          ha0 haL hL
        have hP2eq : ∏ s ∈ T, ((r0 : ℚ) - s + ((n : ℚ) - r0)) = ∏ s ∈ T, ((n : ℚ) - s) :=
          prod_congr rfl fun s _ => by ring
        rw [hP2eq] at key
        intro hne
        have hne' : ∏ s ∈ T, ((r0 : ℚ) - s) - ∏ s ∈ T, ((n : ℚ) - s) ≠ 0 := by
          intro h0; apply hne; rw [h0, zero_div]
        have hne'' : ∏ s ∈ T, ((n : ℚ) - s) - ∏ s ∈ T, ((r0 : ℚ) - s) ≠ 0 := by
          intro h0; apply hne'; linarith
        have k2 := key hne''
        rw [padicValRat.div hne' (mul_ne_zero hP1 hu), padicValRat.mul hP1 hu,
          padicValRat_prod T _ ha0,
          show ∏ s ∈ T, ((r0 : ℚ) - s) - ∏ s ∈ T, ((n : ℚ) - s) =
            -(∏ s ∈ T, ((n : ℚ) - s) - ∏ s ∈ T, ((r0 : ℚ) - s)) by ring, padicValRat.neg]
        push_cast at k2 ⊢
        linarith
      -- the identity splitting off the close pole
      have hsplit : (K.factorial : ℚ) ^ 2 * A.eval (n : ℚ) / ∏ r ∈ R, ((n : ℚ) - r) -
          ∑ r ∈ R, linResidue R G r / ((n : ℚ) - r) =
          (A.eval (n : ℚ) - A.eval (r0 : ℚ)) / ((n : ℚ) - r0) *
              ((K.factorial : ℚ) ^ 2 / ∏ s ∈ T, ((n : ℚ) - s)) +
            A.eval (r0 : ℚ) * (((K.factorial : ℚ) ^ 2 / ∏ s ∈ T, ((n : ℚ) - s)) *
              ((∏ s ∈ T, ((r0 : ℚ) - s) - ∏ s ∈ T, ((n : ℚ) - s)) /
                ((∏ s ∈ T, ((r0 : ℚ) - s)) * ((n : ℚ) - r0)))) -
            ∑ r ∈ T, linResidue R G r / ((n : ℚ) - r) := by
        have hc0 : linResidue R G r0 = (K.factorial : ℚ) ^ 2 * A.eval (r0 : ℚ) /
            ∏ s ∈ T, ((r0 : ℚ) - s) := by rw [linResidue, hGeval]
        rw [← mul_prod_erase R (fun s => (n : ℚ) - s) hr0,
          ← add_sum_erase R (fun r => linResidue R G r / ((n : ℚ) - r)) hr0, hc0]
        simp only [← hT]
        generalize ∑ r ∈ T, linResidue R G r / ((n : ℚ) - r) = Sm
        generalize ∏ s ∈ T, ((n : ℚ) - s) = P2 at hP2 ⊢
        generalize ∏ s ∈ T, ((r0 : ℚ) - s) = P1 at hP1 ⊢
        generalize (n : ℚ) - r0 = u at hu ⊢
        field_simp
        ring
      rw [hsplit, sub_eq_add_neg]
      refine vge_add (vge_add ?_ ?_) (vge_neg (vge_sum _ _ fun r hr => hterm r
        (mem_of_mem_erase hr) fun h => hsep r hr ?_))
      · have := vge_mul (diffQuot_vge p A hA d hd n r0 (by have := (mem_R hr0).2.2; omega)) hFn
        exact vge_mono this (by linarith)
      · have := vge_mul (hA.vge r0) (vge_mul hFn hPD)
        exact vge_mono this (by linarith)
      · have := dvd_sub h hdiv
        rwa [show n - r - (n - r0) = r0 - r by ring] at this
    · -- Case A: `n` is `p`-adically far from every pole
      push Not at hB
      have hG : vge p ((K.factorial : ℚ) ^ 2 / ∏ r ∈ R, ((n : ℚ) - r)) (-(2 * L0 : ℚ)) := by
        refine vge_factorial_sq_div_prod K n R hnr 2 fun j hj => ?_
        split_ifs with hjL
        · have := card_filter_dvd_le K (p ^ j) (hpj j) n R hRsub
          push_cast at this
          have := two_mul_div_le K (p ^ j) (hpj j)
          omega
        · have : {s ∈ R | (p : ℤ) ^ j ∣ n - s} = ∅ :=
            filter_eq_empty_iff.mpr fun s hs hds =>
              hB s hs (dvd_trans (pow_dvd_pow _ (by omega)) hds)
          rw [this, card_empty]; omega
      rw [show (K.factorial : ℚ) ^ 2 * A.eval (n : ℚ) / ∏ r ∈ R, ((n : ℚ) - r) =
        A.eval (n : ℚ) * ((K.factorial : ℚ) ^ 2 / ∏ r ∈ R, ((n : ℚ) - r)) by ring, sub_eq_add_neg]
      refine vge_add ?_ (vge_neg (vge_sum _ _ fun r hr => hterm r hr (hB r hr)))
      have := vge_mul (hA.vge n) hG
      exact vge_mono this (by linarith)
  have hQv := tau_vge_of_values p Q d hQd ((K : ℤ) + 1) a hval
  -- assemble the coefficients
  unfold tauX
  have hnum : (-6 * L' - padicValNat p 24 : ℚ) ≤ -a - 4 * Nat.log p (d + 1) := by
    rw [ha]; push_cast
    have h1 : (L0 : ℚ) ≤ L' := by exact_mod_cast hL0
    have h2 : (max (L0 : ℚ) Ld) ≤ L' := by
      rw [max_le_iff]; exact ⟨h1, by exact_mod_cast hLd⟩
    have h3 : (Nat.log p (d + 1) : ℚ) ≤ L' := by exact_mod_cast hLd1
    have h4 : (0 : ℚ) ≤ padicValNat p 24 := by positivity
    linarith
  refine vpGge_add (vpGge_C (vge_mono hQv (by linarith)))
    (vpGge_sum _ _ fun r hr => ?_)
  unfold tauPole
  rw [sub_eq_add_neg]
  have hpole : vpGge p (C (H5 (dIdx r)) + -X) (-5 * Nat.log p K) :=
    vpGge_add (vpGge_C (vge_H5 K _ (dIdx_le hr)))
      (vpGge_mono (vpGge_neg vpGge_X) (by
        have : (0 : ℚ) ≤ Nat.log p K := by positivity
        linarith))
  refine vpGge_mono (vpGge_mul (vpGge_C (hres r hr)) hpole) ?_
  have h1 : (L0 : ℚ) ≤ L' := by exact_mod_cast hL0
  have h5 : (Nat.log p K : ℚ) ≤ L' := by exact_mod_cast hLK
  have h4 : (0 : ℚ) ≤ padicValNat p 24 := by positivity
  linarith

end Zeta5