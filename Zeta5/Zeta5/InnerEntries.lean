import Zeta5.Distribution
import Zeta5.OuterEntries

/-!
# §4.1 Entry bounds in the inner range, (4.2) and (4.3)

Every entry `µ_X(D_N⁶ E_x E_y / D_K)` is a `τ_X`-value by the pullback (3.1). The distribution
formula (3.7) splits it into `p` summands, one per residue class `c mod p`, and each summand is
bounded by Lemma 3.1 once its powers of `p` are extracted.
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Valuations versus `ℚ_p` norms -/

theorem norm_le_iff_vge (q : ℚ) (b : ℤ) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-b) ↔ vge p q b := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [Padic.eq_padicNorm]
  by_cases hq : q = 0
  · subst hq; simp [vge_zero, zpow_nonneg (by positivity : (0 : ℝ) ≤ p)]
  · rw [padicNorm.eq_zpow_of_nonzero hq]
    push_cast
    rw [zpow_le_zpow_iff_right₀ hp1, neg_le_neg_iff]
    constructor
    · intro h _; exact_mod_cast h
    · intro h; exact_mod_cast h hq

/-- `τ^ext` is linear in the numerator. -/
theorem tauExtP_C_mul (Y : ℚ_[p][X]) (a : ℚ_[p]) (U : ℚ_[p][X]) (S : Finset ℚ) :
    tauExtP p Y (C a * U) S = C a * tauExtP p Y U S := by
  unfold tauExtP tauP
  rw [← smul_eq_C_mul, smul_divByMonic, sum_smul_index _ _ _ (fun _ => by simp)]
  simp only [eval_smul, smul_eq_mul, Polynomial.sum, Finset.mul_sum, mul_add, ← C_mul, mul_div_assoc]
  congr 1
  · congr 1; exact sum_congr rfl fun _ _ => by ring
  · exact sum_congr rfl fun _ _ => by rw [C_mul, mul_assoc]

theorem distribNum_eq (S : Finset ℤ) (P : ℚ[X]) (c : ℕ) :
    distribNum p S P c =
      (C ((p : ℚ) ^ (-(S.card : ℤ))) * P.comp (C (c : ℚ) + C (p : ℚ) * X)).map (algebraMap ℚ ℚ_[p]) := by
  unfold distribNum
  rw [Polynomial.map_mul, map_C, Polynomial.map_comp]
  simp

/-! ## Extracting powers of `p` from `g(c + p z)` -/

/-- Integral, with every coefficient of degree `≥ 1` divisible by `p` (so `≡` a constant mod `p`). -/
def FarGood (p : ℕ) (F : ℚ[X]) : Prop := vpGge p F 0 ∧ ∀ d, 1 ≤ d → vge p (F.coeff d) 1

theorem FarGood.one : FarGood p (1 : ℚ[X]) :=
  ⟨vpGge_one, fun d hd => by rw [coeff_one, if_neg (by omega)]; exact vge_zero 1⟩

theorem FarGood.mul {F G : ℚ[X]} (hF : FarGood p F) (hG : FarGood p G) : FarGood p (F * G) := by
  refine ⟨vpGge_mul0 hF.1 hG.1, fun d hd => ?_⟩
  rw [coeff_mul]
  refine vge_sum _ _ fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  rcases Nat.eq_zero_or_pos x.1 with h1 | h1
  · have : 1 ≤ x.2 := by omega
    simpa using vge_mul (hF.1 x.1) (hG.2 x.2 this)
  · simpa using vge_mul (hF.2 x.1 h1) (hG.1 x.2)

/-- `Q = pᵉ N F` with `N` integral of degree `≤ n` and `F` far-good. -/
def Decomp (p : ℕ) (e n : ℕ) (Q : ℚ[X]) : Prop :=
  ∃ N F : ℚ[X], Q = C ((p : ℚ) ^ e) * N * F ∧ vpGge p N 0 ∧ N.natDegree ≤ n ∧ FarGood p F

theorem Decomp.mul {e n e' n' : ℕ} {Q Q' : ℚ[X]} (h : Decomp p e n Q) (h' : Decomp p e' n' Q') :
    Decomp p (e + e') (n + n') (Q * Q') := by
  obtain ⟨N, F, hQ, hN, hNd, hF⟩ := h
  obtain ⟨N', F', hQ', hN', hNd', hF'⟩ := h'
  refine ⟨N * N', F * F', ?_, vpGge_mul0 hN hN', natDegree_mul_le.trans (add_le_add hNd hNd'),
    hF.mul hF'⟩
  rw [hQ, hQ', pow_add, C_mul]; ring

theorem Decomp.one : Decomp p 0 0 (1 : ℚ[X]) :=
  ⟨1, 1, by simp, vpGge_one, by simp, FarGood.one⟩

theorem Decomp.pow {e n : ℕ} {Q : ℚ[X]} (h : Decomp p e n Q) (k : ℕ) :
    Decomp p (k * e) (k * n) (Q ^ k) := by
  induction k with
  | zero => simpa using Decomp.one (p := p)
  | succ k ih =>
    rw [pow_succ, show (k + 1) * e = k * e + e by ring, show (k + 1) * n = k * n + n by ring]
    exact ih.mul h

theorem Decomp.C_unit {e n : ℕ} {Q : ℚ[X]} (h : Decomp p e n Q) (u : ℚ) (hu : vge p u 0) :
    Decomp p e n (C u * Q) := by
  obtain ⟨N, F, hQ, hN, hNd, hF⟩ := h
  refine ⟨N, C u * F, by rw [hQ]; ring, hN, hNd, ⟨vpGge_mul0 (vpGge_C hu) hF.1, fun d hd => ?_⟩⟩
  rw [coeff_C_mul]; simpa using vge_mul hu (hF.2 d hd)

/-- A linear factor `α + σ p z` (`σ = ±1`) is `p·(near)` if `p ∣ α`, and far-good otherwise. -/
theorem Decomp.linear (α σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Decomp p (if (p : ℤ) ∣ α then 1 else 0) (if (p : ℤ) ∣ α then 1 else 0)
      (C (α : ℚ) + C ((σ * p : ℤ) : ℚ) * X) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  split_ifs with hd
  · obtain ⟨β, rfl⟩ := hd
    refine ⟨C (β : ℚ) + C (σ : ℚ) * X, 1, ?_, ?_, ?_, FarGood.one⟩
    · simp only [pow_one, mul_one]; push_cast; rw [C_mul, C_mul]; ring
    · exact vpGge_add (vpGge_C (vge_int p β)) (by
        simpa using vpGge_mul0 (vpGge_C (vge_int p σ)) vpGge_X)
    · exact (natDegree_add_le _ _).trans (max_le (by simp)
        ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  · refine ⟨1, C (α : ℚ) + C ((σ * p : ℤ) : ℚ) * X, by simp, vpGge_one, by simp, ?_, ?_⟩
    · exact vpGge_add (vpGge_C (vge_int p α)) (by
        simpa using vpGge_mul0 (vpGge_C (vge_int p (σ * p))) vpGge_X)
    · intro d hd
      rw [coeff_add, coeff_C, if_neg (by omega), zero_add, coeff_C_mul, coeff_X]
      split_ifs
      · rw [mul_one]
        exact vge_int_of_dvd (p := p) _ 1 (by rw [pow_one]; exact dvd_mul_left _ _)
      · rw [mul_zero]; exact vge_zero 1

theorem Decomp.prod {ι : Type*} (J : Finset ι) (f : ι → ℚ[X]) (e : ι → ℕ)
    (h : ∀ j ∈ J, Decomp p (e j) (e j) (f j)) :
    Decomp p (∑ j ∈ J, e j) (∑ j ∈ J, e j) (∏ j ∈ J, f j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using Decomp.one (p := p)
  | insert a J ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a J)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

/-- The number of `p`'s in `j² - (c + p z)² = (j - c - p z)(j + c + p z)`. -/
def omg (p c j : ℕ) : ℕ :=
  (if (p : ℤ) ∣ ((j : ℤ) - c) then 1 else 0) + (if (p : ℤ) ∣ ((j : ℤ) + c) then 1 else 0)

/-- The exponent of `p` extracted from the pulled-back numerator at the class `c`. -/
def eNum (p c : ℕ) (J : Finset ℕ) (k : ℕ → ℕ) : ℕ :=
  5 * (if (p : ℤ) ∣ (c : ℤ) then 1 else 0) + ∑ j ∈ J, k j * omg p c j

theorem decomp_pullback (c : ℕ) (J : Finset ℕ) (k : ℕ → ℕ) (ε : ℚ) (hε : vge p ε 0) :
    Decomp p (eNum p c J k) (eNum p c J k)
      ((C ε * X ^ 5 * (∏ j ∈ J, (X + C ((j : ℚ) ^ 2)) ^ (k j)).comp (-X ^ 2)).comp
        (C (c : ℚ) + C (p : ℚ) * X)) := by
  set L := C (c : ℚ) + C (p : ℚ) * X with hLdef
  have hL : L = C ((c : ℤ) : ℚ) + C (((1 : ℤ) * p : ℤ) : ℚ) * X := by
    rw [hLdef]; push_cast; simp
  have hfac : ∀ j : ℕ, ((X + C ((j : ℚ) ^ 2)).comp (-X ^ 2)).comp L =
      (C (((j : ℤ) - c : ℤ) : ℚ) + C (((-1 : ℤ) * p : ℤ) : ℚ) * X) *
        (C (((j : ℤ) + c : ℤ) : ℚ) + C (((1 : ℤ) * p : ℤ) : ℚ) * X) := by
    intro j
    rw [hLdef]
    simp only [add_comp, neg_comp, pow_comp, X_comp, C_comp]
    push_cast
    simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_one]
    ring
  have hQ : (C ε * X ^ 5 * (∏ j ∈ J, (X + C ((j : ℚ) ^ 2)) ^ (k j)).comp (-X ^ 2)).comp L =
      C ε * (L ^ 5 * ∏ j ∈ J, ((C (((j : ℤ) - c : ℤ) : ℚ) + C (((-1 : ℤ) * p : ℤ) : ℚ) * X) *
        (C (((j : ℤ) + c : ℤ) : ℚ) + C (((1 : ℤ) * p : ℤ) : ℚ) * X)) ^ (k j)) := by
    rw [mul_comp, mul_comp, C_comp, pow_comp, X_comp, Polynomial.prod_comp, Polynomial.prod_comp,
      mul_assoc]
    congr 2
    refine prod_congr rfl fun j _ => ?_
    rw [pow_comp, pow_comp, hfac]
  rw [hQ]
  refine Decomp.C_unit ?_ ε hε
  unfold eNum
  refine Decomp.mul ?_ ?_
  · rw [hL]; exact (Decomp.linear (p := p) (c : ℤ) 1 (Or.inl rfl)).pow 5
  · refine Decomp.prod J _ (fun j => k j * omg p c j) fun j _ => ?_
    exact ((Decomp.linear (p := p) ((j : ℤ) - c) (-1) (Or.inr rfl)).mul
      (Decomp.linear (p := p) ((j : ℤ) + c) 1 (Or.inl rfl))).pow (k j)

/-! ## One summand of the distribution formula -/

theorem Yp_norm (hp7 : 7 ≤ p) (i : ℕ) : ‖(Yp p).coeff i‖ ≤ 1 := by
  have hCp := Cp_norm_le' p hp7
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have h5 : (p : ℝ) ^ (-5 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hp1 (by norm_num)
  unfold Yp
  rw [coeff_add, coeff_C_mul, coeff_X, coeff_C]
  rcases i with _ | _ | i
  · simpa using hCp.trans h5
  · simp only [if_true, mul_one, Nat.succ_ne_zero, if_false, add_zero, zero_add]
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1)
  · simp

theorem coeff_high_vge {N F : ℚ[X]} (hN : vpGge p N 0) (hF : FarGood p F) {d : ℕ}
    (hd : N.natDegree < d) : vge p ((N * F).coeff d) 1 := by
  rw [coeff_mul]
  refine vge_sum _ _ fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : N.natDegree < x.1
  · rw [coeff_eq_zero_of_natDegree_lt h1, zero_mul]; exact vge_zero 1
  · simpa using vge_mul (hN x.1) (hF.2 x.2 (by omega))

/-- **One summand of (3.7).** If `P(c + p z) = pᵉ N F` (`Decomp`), with `e ≤ p + 1`, then the
class-`c` summand has valuation `≥ e - #{near poles}`. -/
theorem summand_bound (hp7 : 7 ≤ p) (K : ℕ) (hK1 : 2 * K < p ^ 2) (hK2 : K + p < p ^ 2)
    (S : Finset ℤ) (hS : ∀ r ∈ S, |r| ≤ K) (c : ℕ) (hc : c < p) (P : ℚ[X]) (e : ℕ)
    (hQ : Decomp p e e (P.comp (C (c : ℚ) + C (p : ℚ) * X))) (hdeg : e ≤ p + 1) (i : ℕ) :
    ‖(tauExtP p (Yp p) (distribNum p S P c) (distribPoles p S c)).coeff i‖ ≤
      (p : ℝ) ^ (-((e : ℤ) - (S.filter fun r => (p : ℤ) ∣ r - c).card)) := by
  obtain ⟨N, F, hQeq, hN, hNd, hF⟩ := hQ
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  set Sn := S.filter fun r => (p : ℤ) ∣ r - c
  set Sf := S.filter fun r => ¬ (p : ℤ) ∣ r - c
  set near : Finset ℤ := Sn.image fun r => (r - c) / p
  set far : Finset ℚ := Sf.image fun r : ℤ => ((r : ℚ) - c) / p
  have hinj : Set.InjOn (fun r : ℤ => ((r : ℚ) - c) / p) S := by
    intro a _ b _ hab
    simp only at hab
    have := (div_left_inj' hp0).mp hab
    exact_mod_cast (sub_left_inj.mp this)
  have hcardf : far.card = Sf.card :=
    card_image_of_injOn (hinj.mono (by intro x hx; exact (mem_filter.mp hx).1))
  have hcardS : S.card = Sn.card + Sf.card := (card_filter_add_card_filter_not _).symm
  have hpoles : distribPoles p S c = near.image (fun r : ℤ => (r : ℚ)) ∪ far := by
    unfold distribPoles
    rw [← filter_union_filter_not_eq (fun r => (p : ℤ) ∣ r - c) S, image_union, image_image]
    congr 1
    refine image_congr fun r hr => ?_
    obtain ⟨t, ht⟩ := (mem_filter.mp hr).2
    simp only [Function.comp]
    rw [ht, Int.mul_ediv_cancel_left _ (by omega)]
    have : (r : ℚ) - c = p * t := by exact_mod_cast ht
    rw [this]; field_simp
  -- near-pole hypotheses of Lemma 3.1
  have hnear : ∀ r ∈ Sn, (p : ℤ) * ((r - c) / p) = r - c := fun r hr =>
    Int.mul_ediv_cancel' (mem_filter.mp hr).2
  have hT : ∀ r ∈ near, ∀ s ∈ near, r ≠ s → ¬ (p : ℤ) ∣ r - s := by
    intro r hr s hs hrs hd
    obtain ⟨r0, hr0, rfl⟩ := mem_image.mp hr
    obtain ⟨s0, hs0, rfl⟩ := mem_image.mp hs
    obtain ⟨t, ht⟩ := hd
    have e1 := hnear r0 hr0
    have e2 := hnear s0 hs0
    have hr1 := hS r0 (mem_filter.mp hr0).1
    have hs1 := hS s0 (mem_filter.mp hs0).1
    have hdiff : r0 - s0 = (p : ℤ) * (p * t) := by rw [← ht]; linarith
    rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
    · have : (p : ℤ) * (p * t) ≤ -(p * p) := by nlinarith
      have : (2 * K : ℤ) < p ^ 2 := by exact_mod_cast hK1
      rw [abs_le] at hr1 hs1; nlinarith
    · subst ht0; exact hrs (by linarith)
    · have : (p : ℤ) * (p * t) ≥ p * p := by nlinarith
      have : (2 * K : ℤ) < p ^ 2 := by exact_mod_cast hK1
      rw [abs_le] at hr1 hs1; nlinarith
  have hd : ∀ r ∈ near, dIdx r < p := by
    intro r hr
    obtain ⟨r0, hr0, rfl⟩ := mem_image.mp hr
    have e1 := hnear r0 hr0
    have hr1 := hS r0 (mem_filter.mp hr0).1
    rw [abs_le] at hr1
    have hK' : (K : ℤ) + p < p ^ 2 := by exact_mod_cast hK2
    have hc' : (c : ℤ) < p := by exact_mod_cast hc
    have hlo : -(p : ℤ) < (r0 - c) / p := by nlinarith
    have hhi : (r0 - c) / p < p := by nlinarith
    unfold dIdx; split_ifs <;> omega
  have hFv : ∀ s ∈ far, padicValRat p s = -1 := by
    intro s hs
    obtain ⟨r0, hr0, rfl⟩ := mem_image.mp hs
    have hnd := (mem_filter.mp hr0).2
    have hne : ((r0 : ℚ) - c) ≠ 0 := by
      intro h0; apply hnd; rw [show r0 - c = 0 by exact_mod_cast h0]; exact dvd_zero _
    rw [padicValRat.div hne hp0, padicValRat.self hp.out.one_lt]
    have : padicValRat p ((r0 : ℚ) - c) = 0 := by
      rw [show ((r0 : ℚ) - c) = ((r0 - c : ℤ) : ℚ) by push_cast; ring]
      exact padicValRat_int_of_not_dvd _ hnd
    rw [this]; ring
  -- rewrite the numerator
  have hU : vpGge p (N * F) 0 := vpGge_mul0 hN hF.1
  have hU1 : ∀ d, p + 1 < d → vge p ((N * F).coeff d) 1 := fun d hd =>
    coeff_high_vge hN hF (by omega)
  have hconst : (p : ℚ) ^ (-(S.card : ℤ)) * (p : ℚ) ^ e =
      ((p : ℚ) ^ ((e : ℤ) - Sn.card) * (-1) ^ Sf.card) * (-(p : ℚ)) ^ (-(Sf.card : ℤ)) := by
    have h1 : (-1 : ℚ) ≠ 0 := by norm_num
    rw [hcardS, show (-(p : ℚ)) = (-1) * p by ring, mul_zpow, ← zpow_natCast (-1 : ℚ),
      ← zpow_natCast (p : ℚ) e]
    have hr : (p : ℚ) ^ ((e : ℤ) - Sn.card) * (-1) ^ (Sf.card : ℤ) *
        ((-1) ^ (-(Sf.card : ℤ)) * (p : ℚ) ^ (-(Sf.card : ℤ))) =
        (p : ℚ) ^ ((e : ℤ) - Sn.card) * (p : ℚ) ^ (-(Sf.card : ℤ)) *
          ((-1) ^ (Sf.card : ℤ) * (-1) ^ (-(Sf.card : ℤ))) := by ring
    rw [hr, ← zpow_add₀ h1, add_neg_cancel, zpow_zero, mul_one, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    congr 1
    push_cast; ring
  have hnum : distribNum p S P c =
      C (((p : ℚ) ^ ((e : ℤ) - Sn.card) * (-1) ^ Sf.card : ℚ) : ℚ_[p]) *
        (C ((-(p : ℚ)) ^ (-(far.card : ℤ))) * (N * F)).map (algebraMap ℚ ℚ_[p]) := by
    rw [distribNum_eq, hQeq, hcardf]
    rw [show C ((p : ℚ) ^ (-(S.card : ℤ))) * (C ((p : ℚ) ^ e) * N * F) =
        C ((p : ℚ) ^ (-(S.card : ℤ)) * (p : ℚ) ^ e) * (N * F) by rw [C_mul]; ring, hconst,
      C_mul, mul_assoc, Polynomial.map_mul, map_C]
    rfl
  rw [hnum, hpoles, tauExtP_C_mul, coeff_C_mul, norm_mul]
  have h31 := lemma_3_1_rat p hp7 near hT hd far hFv (Yp p) (Yp_norm hp7) (N * F) hU hU1 i
  have hk : ‖(((p : ℚ) ^ ((e : ℤ) - Sn.card) * (-1) ^ Sf.card : ℚ) : ℚ_[p])‖ =
      (p : ℝ) ^ (-((e : ℤ) - Sn.card)) := by
    push_cast
    rw [norm_mul, Padic.norm_p_zpow, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  rw [hk]
  exact mul_le_of_le_one_right (by positivity) h31

/-! ## The entry bound from the distribution formula -/

/-- The number of poles `r ∈ ±[1, K]` with `r ≡ c (mod p)`: the near poles of the class `c`. -/
def nearCount (p K c : ℕ) : ℕ :=
  ((signedPoles (Icc 1 K)).filter fun r => (p : ℤ) ∣ r - c).card

theorem signedPoles_abs_le (K : ℕ) : ∀ r ∈ signedPoles (Icc 1 K), |r| ≤ K := by
  intro r hr
  simp only [signedPoles, mem_union, mem_image, mem_Icc] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rw [abs_le] <;> constructor <;> omega

/-- **The inner-range entry bound, generic form.** If every class `c` of the distribution formula
gives `B + 4 ≤ e_c - n_c` (with `e_c ≤ p + 1` for Lemma 3.1), then
`v_p^G(µ_X(∏(t + j²)^{k_j} / D_K)) ≥ B`. -/
theorem entry_generic (hp7 : 7 ≤ p) (K : ℕ) (hK1 : 2 * K < p ^ 2) (hK2 : K + p < p ^ 2)
    (J : Finset ℕ) (k : ℕ → ℕ) (B : ℚ)
    (hB : ∀ c < p, B + 4 ≤ (eNum p c J k : ℚ) - nearCount p K c)
    (hdeg : ∀ c < p, eNum p c J k ≤ p + 1) :
    vpGge p (muX (Icc 1 K) (∏ j ∈ J, (X + C ((j : ℚ) ^ 2)) ^ (k j))) B := by
  have h0 : 0 ∉ Icc 1 K := by simp
  rw [pullback _ h0]
  set P := C ((-1 : ℚ) ^ (Icc 1 K).card) * X ^ 5 *
    (∏ j ∈ J, (X + C ((j : ℚ) ^ 2)) ^ (k j)).comp (-X ^ 2) with hP
  have hε : vge p ((-1 : ℚ) ^ (Icc 1 K).card) 0 := by
    have := vge_int p ((-1 : ℤ) ^ (Icc 1 K).card); push_cast at this; exact this
  intro n hn
  have hceil : vge p ((tauX (signedPoles (Icc 1 K)) P).coeff n) ⌈B⌉ := by
    rw [← norm_le_iff_vge]
    have hmap : (((tauX (signedPoles (Icc 1 K)) P).coeff n : ℚ) : ℚ_[p]) =
        ((tauX (signedPoles (Icc 1 K)) P).map (algebraMap ℚ ℚ_[p])).coeff n := by
      rw [coeff_map]; rfl
    rw [hmap, lemma_3_2' p hp7 _ P, coeff_C_mul, finsetSum_coeff, norm_mul, Padic.norm_p_zpow]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    have hsum : ‖∑ c ∈ range p, (tauExtP p (Yp p) (distribNum p (signedPoles (Icc 1 K)) P c)
        (distribPoles p (signedPoles (Icc 1 K)) c)).coeff n‖ ≤ (p : ℝ) ^ (-(⌈B⌉ + 4)) := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun c hc => ?_
      have hc' : c < p := mem_range.mp hc
      refine (summand_bound hp7 K hK1 hK2 _ (signedPoles_abs_le K) c hc' P _
        (decomp_pullback c J k _ hε) (hdeg c hc') n).trans ?_
      refine zpow_le_zpow_right₀ hp1 (neg_le_neg ?_)
      have := hB c hc'
      have h2 : (⌈B⌉ : ℚ) + 4 ≤ (eNum p c J k : ℚ) - nearCount p K c := by
        have : (⌈B⌉ : ℤ) ≤ (eNum p c J k : ℤ) - nearCount p K c - 4 := by
          rw [Int.ceil_le]; push_cast; linarith
        have := (Int.cast_le (R := ℚ)).mpr this
        push_cast at this; linarith
      unfold nearCount at h2
      exact_mod_cast (show ((⌈B⌉ + 4 : ℤ) : ℚ) ≤ ((eNum p c J k : ℤ) -
        ((signedPoles (Icc 1 K)).filter fun r => (p : ℤ) ∣ r - c).card : ℤ) by push_cast; linarith)
    calc (p : ℝ) ^ (-(-4 : ℤ)) * _ ≤ (p : ℝ) ^ (-(-4 : ℤ)) * (p : ℝ) ^ (-(⌈B⌉ + 4)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (p : ℝ) ^ (-⌈B⌉) := by
          rw [← zpow_add₀ (by positivity)]; congr 1; ring
  exact vge_mono hceil (Int.le_ceil B) hn

end Zeta5