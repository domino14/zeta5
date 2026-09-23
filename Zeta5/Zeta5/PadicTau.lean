import Zeta5.Functionals
import Zeta5.Valuation
import Zeta5.MuMod
import Zeta5.IntValued

/-!
# The `p`-adic series of §3.1–3.2

* `tauAnPole_sub`: the difference identity for a far pole,
  `τ(1/(z-s)) - τ(1/(z-(s-1))) = s⁻⁵`.
* `Cp_norm_le'`: `C_p ∈ p⁵ ℤ_p`.
* `lemma_3_1_rat`: Lemma 3.1 with far poles, in rational form.
-/

open Polynomial Finset Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## From rational valuations to `ℚ_p` norms -/

theorem pt_norm_le_of_vge {x : ℚ} {b : ℤ} (h : vge p x b) :
    ‖(x : ℚ_[p])‖ ≤ (p : ℝ) ^ (-b) := by
  by_cases hx : x = 0
  · subst hx; simp; positivity
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hx]
  push_cast
  have h1 : (b : ℚ) ≤ padicValRat p x := h hx
  have h2 : b ≤ padicValRat p x := by exact_mod_cast h1
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)

theorem pt_norm_le_one_of_vge {x : ℚ} (h : vge p x 0) : ‖(x : ℚ_[p])‖ ≤ 1 := by
  have := pt_norm_le_of_vge (b := 0) (by simpa using h); simpa using this

theorem pt_kappa_vge (d : ℕ) : vge p (kappa d) (-4) := by
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · rw [kappa_of_lt hlt]; exact vge_zero _
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  rw [kappa_eq]
  have h24 : vge p ((24 : ℚ)⁻¹) (-3) := by
    have := mm_vge_inv_nat (p := p) (n := 24) (by norm_num) 3 (by
      intro hd
      have h2 := hp.out.two_le
      have h24 : p ^ 4 ≤ 24 := Nat.le_of_dvd (by norm_num) hd
      rcases (by omega : p = 2 ∨ 3 ≤ p) with h | h
      · subst h; norm_num at hd
      · have : 3 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h 4
        omega)
    simpa using this
  have := vge_mul (vge_mul (mm_vge_nat (p := p) ((m + 3).descFactorial 3)) (bern_vge m)) h24
  exact vge_mono this (by norm_num)

theorem pt_kappa_norm (d : ℕ) : ‖((kappa d : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ 4 := by
  have := pt_norm_le_of_vge (p := p) (b := -4) (by simpa using pt_kappa_vge (p := p) d)
  simpa using this

theorem pt_norm_natCast_le (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := p) n; simpa using this

/-- `‖1/s‖ ≤ 1/p` when `v_p(s) < 0`. -/
theorem pt_norm_inv_le {s : ℚ} (hs : padicValRat p s < 0) :
    ‖((s : ℚ_[p]))⁻¹‖ ≤ (p : ℝ)⁻¹ := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have : vge p s⁻¹ 1 := by
    intro _; rw [padicValRat.inv]; push_cast
    have : padicValRat p s ≤ -1 := by omega
    exact_mod_cast (by omega : (1 : ℤ) ≤ -padicValRat p s)
  have h := pt_norm_le_of_vge (p := p) (b := 1) (by simpa using this)
  simpa using h

theorem pt_inv_p_le_half : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have := hp.out.two_le
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)

/-! ## `τ(zᵈ) = κ_d` and the difference coefficients -/

theorem tau_X_pow_eq_kappa (d : ℕ) : tau ((X : ℚ[X]) ^ d) = kappa d := by
  rw [tau_X_pow]
  unfold kappa
  rcases Nat.lt_or_ge d 3 with h | h
  · interval_cases d <;> simp [Nat.descFactorial]
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
    simp only [Nat.descFactorial, Nat.add_sub_cancel]
    push_cast
    ring

/-- `∑_{d ≤ n} C(n,d) κ_d = [n = 4] + κ_n`. -/
theorem sum_choose_kappa (n : ℕ) :
    ∑ d ∈ range (n + 1), (n.choose d : ℚ) * kappa d = (if n = 4 then 1 else 0) + kappa n := by
  have h := tau_fwd ((X : ℚ[X]) ^ n)
  rw [X_pow_comp, add_pow, sub_eq_add_neg, tau_add, tau_neg, tau_sum] at h
  have h2 : ∀ d ∈ range (n + 1), tau (X ^ d * 1 ^ (n - d) * (n.choose d : ℚ[X])) =
      (n.choose d : ℚ) * kappa d := by
    intro d _
    rw [one_pow, mul_one, ← C_eq_natCast, mul_comm, tau_C_mul, tau_X_pow_eq_kappa]
  rw [sum_congr rfl h2, tau_X_pow_eq_kappa, coeff_X_pow] at h
  have : (if 4 = n then (1 : ℚ) else 0) = if n = 4 then 1 else 0 := by
    split_ifs <;> first | rfl | omega
  rw [← this]
  linarith

/-! ## `τ` of a far pole as a series in `1/s` -/

theorem pt_summable_kappa {t : ℚ_[p]} (ht : ‖t‖ ≤ 1 / 2) :
    Summable fun d : ℕ => ((kappa d : ℚ) : ℚ_[p]) * t ^ (d + 1) := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => (p : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (d + 1)) ?_ ?_
  · simp only [pow_succ]
    exact ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_right
      (1 / 2)).mul_left _
  · intro d
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pt_kappa_norm d) (pow_le_pow_left₀ (norm_nonneg _) ht _) (by positivity)
      (by positivity)

theorem kappa_add_three (k : ℕ) : kappa (k + 3) = ((k + 3).choose 3 : ℚ) * _root_.bernoulli k / 4 := by
  rw [kappa_eq, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  simp [Nat.factorial]
  ring

/-- (3.5) reindexed: `τ(1/(z - s)) = -∑_d κ_d s^{-d-1}`. -/
theorem tauAnPole_eq {s : ℚ} (hs : padicValRat p s < 0) :
    tauAnPole p s = -∑' d : ℕ, ((kappa d : ℚ) : ℚ_[p]) * ((s : ℚ_[p])⁻¹) ^ (d + 1) := by
  set t : ℚ_[p] := (s : ℚ_[p])⁻¹
  have ht : ‖t‖ ≤ 1 / 2 := (pt_norm_inv_le hs).trans pt_inv_p_le_half
  have hsum := pt_summable_kappa (p := p) ht
  rw [← hsum.sum_add_tsum_nat_add 3]
  simp only [sum_range_succ, sum_range_zero, kappa_of_lt (by norm_num : (0 : ℕ) < 3),
    kappa_of_lt (by norm_num : (1 : ℕ) < 3), kappa_of_lt (by norm_num : (2 : ℕ) < 3),
    Rat.cast_zero, zero_mul, zero_add]
  unfold tauAnPole
  rw [← tsum_mul_left, ← tsum_neg]
  congr 1
  funext k
  rw [kappa_add_three, zpow_neg, ← inv_zpow, show ((k : ℤ) + 4) = ((k + 3 + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast]
  push_cast
  ring

theorem pt_valRat_sub_one {s : ℚ} (hs : padicValRat p s < 0) : padicValRat p (s - 1) < 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h; have : s = 1 := by linarith
    rw [this] at hs; simp at hs
  have := padicValRat.add_eq_min (p := p) (q := s) (r := -1) (by simpa [sub_eq_add_neg] using hs1)
    hs0 (by norm_num) (by rw [padicValRat.neg, padicValRat.one]; omega)
  rw [← sub_eq_add_neg] at this
  rw [this, padicValRat.neg, padicValRat.one]
  omega

/-- The difference identity (3.3) for a far pole: `τ(1/(z-s)) - τ(1/(z-(s-1))) = s⁻⁵`. -/
theorem tauAnPole_sub (p : ℕ) [Fact p.Prime] (s : ℚ) (hs : padicValRat p s < 0) (hs0 : s ≠ 0) :
    tauAnPole p s - tauAnPole p (s - 1) = (s : ℚ_[p]) ^ (-5 : ℤ) := by
  set t : ℚ_[p] := (s : ℚ_[p])⁻¹ with htdef
  have ht : ‖t‖ ≤ 1 / 2 := (pt_norm_inv_le hs).trans pt_inv_p_le_half
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht (by norm_num)
  have hs1 : s - 1 ≠ 0 := by
    intro h; have : s = 1 := by linarith
    rw [this] at hs; simp at hs
  have hsQ : (s : ℚ_[p]) ≠ 0 := by exact_mod_cast hs0
  have htne : (1 : ℚ_[p]) - t ≠ 0 := by
    intro h
    have : ‖(1 : ℚ_[p])‖ = ‖t‖ := by rw [sub_eq_zero] at h; rw [h]
    rw [norm_one] at this; linarith
  have hu : (((s - 1 : ℚ) : ℚ_[p]))⁻¹ = t / (1 - t) := by
    rw [htdef]; push_cast
    have : (s : ℚ_[p]) - 1 ≠ 0 := by exact_mod_cast hs1
    field_simp
  -- the double series
  set a : ℕ → ℕ → ℚ_[p] := fun d n =>
    if d ≤ n then ((kappa d : ℚ) : ℚ_[p]) * ((n.choose d : ℕ) : ℚ_[p]) * t ^ (n + 1) else 0 with ha
  have hbound : ∀ d n, ‖a d n‖ ≤ (p : ℝ) ^ 4 * ((2 / 3 : ℝ) ^ d * (3 / 4 : ℝ) ^ n) := by
    intro d n
    simp only [ha]
    split_ifs with hdn
    · rw [norm_mul, norm_mul, norm_pow]
      have h1 : ‖t‖ ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
        calc ‖t‖ ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) ht _
          _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h2 : (1 / 2 : ℝ) ^ n ≤ (2 / 3 : ℝ) ^ d * (3 / 4 : ℝ) ^ n := by
        calc (1 / 2 : ℝ) ^ n = (2 / 3 : ℝ) ^ n * (3 / 4 : ℝ) ^ n := by rw [← mul_pow]; norm_num
          _ ≤ (2 / 3 : ℝ) ^ d * (3 / 4 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hdn)
              (by positivity)
      calc ‖((kappa d : ℚ) : ℚ_[p])‖ * ‖((n.choose d : ℕ) : ℚ_[p])‖ * ‖t‖ ^ (n + 1)
          ≤ (p : ℝ) ^ 4 * 1 * (1 / 2 : ℝ) ^ n := by
            gcongr
            · exact pt_kappa_norm d
            · exact pt_norm_natCast_le _
        _ ≤ _ := by rw [mul_one]; gcongr
    · simp only [norm_zero]; positivity
  have hsum : Summable (Function.uncurry a) := by
    refine Summable.of_norm_bounded (g := fun x : ℕ × ℕ =>
      (p : ℝ) ^ 4 * ((2 / 3 : ℝ) ^ x.1 * (3 / 4 : ℝ) ^ x.2)) ?_ (fun x => hbound x.1 x.2)
    exact (Summable.mul_of_nonneg (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (fun _ => by positivity) (fun _ => by positivity)).mul_left _
  -- fibers
  have hn : ∀ n, ∑' d, a d n = t ^ (n + 1) * (((if n = 4 then 1 else 0) + kappa n : ℚ) : ℚ_[p]) := by
    intro n
    rw [tsum_eq_sum (s := range (n + 1)) (fun d hd => by
      simp only [ha, mem_range, not_lt] at hd ⊢; rw [if_neg (by omega)])]
    rw [← sum_choose_kappa n]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    simp only [ha, mem_range] at hd ⊢
    rw [if_pos (by omega)]
    ring
  have hd : ∀ d, ∑' n, a d n = ((kappa d : ℚ) : ℚ_[p]) * (((s - 1 : ℚ) : ℚ_[p]))⁻¹ ^ (d + 1) := by
    intro d
    have hf : Summable (a d) := hsum.prod_factor d
    rw [← hf.sum_add_tsum_nat_add d]
    have h0 : ∑ n ∈ range d, a d n = 0 :=
      sum_eq_zero fun n hn => by simp only [ha, mem_range] at hn ⊢; rw [if_neg (by omega)]
    rw [h0, zero_add]
    have e : ∀ m, a d (m + d) = (((kappa d : ℚ) : ℚ_[p]) * t ^ (d + 1)) *
        ((((m + d).choose d : ℕ) : ℚ_[p]) * t ^ m) := by
      intro m; simp only [ha]; rw [if_pos (by omega)]; ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one d ht1, hu, div_pow]
    ring
  have hcomm := hsum.tsum_comm
  simp_rw [hn, hd] at hcomm
  -- assemble
  rw [tauAnPole_eq hs, tauAnPole_eq (pt_valRat_sub_one hs)]
  have hk := pt_summable_kappa (p := p) ht
  have hsplit : ∑' n, t ^ (n + 1) * (((if n = 4 then 1 else 0) + kappa n : ℚ) : ℚ_[p]) =
      t ^ 5 + ∑' n, ((kappa n : ℚ) : ℚ_[p]) * t ^ (n + 1) := by
    have h1 : ∑' n : ℕ, t ^ (n + 1) * (((if n = 4 then (1 : ℚ) else 0) : ℚ) : ℚ_[p]) = t ^ 5 := by
      rw [tsum_eq_single 4 (fun n hn => by simp [hn])]; simp
    have hs1' : Summable fun n : ℕ => t ^ (n + 1) * (((if n = 4 then (1 : ℚ) else 0) : ℚ) : ℚ_[p]) :=
      summable_of_ne_finset_zero (s := {4}) (fun n hn => by simp at hn; simp [hn])
    rw [← h1, ← hs1'.tsum_add hk]
    congr 1; funext n; push_cast; ring
  rw [hsplit] at hcomm
  rw [zpow_neg, ← inv_zpow, show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, zpow_natCast]
  linear_combination -hcomm

/-! ## `C_p ∈ p⁵ ℤ_p` -/

theorem vge_pow0' {x : ℚ} (hx : vge p x 0) (n : ℕ) : vge p (x ^ n) 0 := by
  induction n with
  | zero => simpa using vge_one (p := p)
  | succ n ih => rw [pow_succ]; simpa using vge_mul ih hx

/-- `∑_{a=1}^{p-1} a^k ≡ 0 (mod p)` for `0 < k < p - 1`. -/
theorem pt_powSum_dvd (k : ℕ) (hk0 : 0 < k) (hk : k < p - 1) :
    (p : ℤ) ∣ ∑ a ∈ Ico 1 p, (a : ℤ) ^ k := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hsum := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) k (by rw [ZMod.card]; exact hk)
  have hrange : ∑ x : ZMod p, x ^ k = ∑ a ∈ range p, ((a : ℕ) : ZMod p) ^ k := by
    symm
    refine Finset.sum_nbij' (fun a => (a : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro a _; simp
    · intro x _; simp [ZMod.val_lt]
    · intro a ha
      have ha' : a < p := by simpa using ha
      exact ZMod.val_natCast_of_lt ha'
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro a _; rfl
  rw [hrange, range_eq_Ico, sum_eq_sum_Ico_succ_bot hp.out.pos] at hsum
  simpa [zero_pow hk0.ne'] using hsum

theorem pt_vge_inv_unit {a : ℕ} (ha : ¬ p ∣ a) : vge p ((a : ℚ)⁻¹) 0 := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero p)
  have := mm_vge_inv_nat (p := p) ha0 0 (by simpa using ha)
  simpa using this

/-- `∑_{a=1}^{p-1} a⁻⁴ ≡ 0 (mod p)` for `p ≥ 7`. -/
theorem pt_invPowSum_vge (hp7 : 7 ≤ p) : vge p (∑ a ∈ Ico 1 p, ((a : ℚ)⁻¹) ^ 4) 1 := by
  have hM := pt_powSum_dvd (p := p) (p - 5) (by omega) (by omega)
  have hsplit : ∑ a ∈ Ico 1 p, ((a : ℚ)⁻¹) ^ 4 =
      ∑ a ∈ Ico 1 p, ((a : ℚ)⁻¹) ^ 4 * (1 - (a : ℚ) ^ (p - 1)) +
        ((∑ a ∈ Ico 1 p, (a : ℤ) ^ (p - 5) : ℤ) : ℚ) := by
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_Ico] at ha
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have : (a : ℚ) ^ (p - 1) = (a : ℚ) ^ 4 * (a : ℚ) ^ (p - 5) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; field_simp; ring
  rw [hsplit]
  refine vge_add (vge_sum _ _ fun a ha => ?_) (mm_vge_int_dvd hM)
  rw [mem_Ico] at ha
  have hna : ¬ p ∣ a := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hF : (p : ℤ) ∣ (a : ℤ) ^ (p - 1) - 1 := by
    have := Int.ModEq.pow_card_sub_one_eq_one hp.out (n := a) (by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime a p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hna))
      simpa [Int.gcd_natCast_natCast] using this)
    exact (Int.ModEq.dvd this.symm)
  have h1 : vge p (1 - (a : ℚ) ^ (p - 1)) 1 := by
    have := mm_vge_int_dvd (p := p) (dvd_neg.mpr hF)
    push_cast at this; convert this using 1; ring
  simpa using vge_mul (vge_pow0' (pt_vge_inv_unit hna) 4) h1

theorem pt_norm_le_pow {x : ℚ} {n : ℕ} (h : vge p x n) : ‖(x : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
  have := pt_norm_le_of_vge (p := p) (b := n) (by exact_mod_cast h)
  rwa [zpow_neg, zpow_natCast, ← inv_pow] at this

theorem pt_kappa_norm_p (hp2 : p ≠ 2) (d : ℕ) : ‖((kappa d : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) := by
  have h : vge p (kappa d) (-1) := fun hd => by exact_mod_cast kappa_padicVal_ge' p hp2 d hd
  have := pt_norm_le_of_vge (p := p) (b := -1) (by exact_mod_cast h)
  simpa using this

theorem pt_kappa_norm_one (hp7 : 7 ≤ p) {d : ℕ} (hd : d ≤ p + 1) :
    ‖((kappa d : ℚ) : ℚ_[p])‖ ≤ 1 := by
  refine pt_norm_le_one_of_vge fun hk => ?_
  exact_mod_cast kappa_integral' p hp7 d hd hk

/-- §3.2: `C_p ∈ p⁵ ℤ_p`. -/
theorem Cp_norm_le' (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : ‖Cp p‖ ≤ (p : ℝ) ^ (-5 : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  set q : ℝ := (p : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
  have hC : (p : ℝ) ^ (-5 : ℤ) = q ^ 5 := by rw [hq, zpow_neg, inv_pow]; norm_cast
  rw [hC]
  have hpq : (p : ℝ) * q = 1 := by rw [hq]; field_simp
  -- each far pole `-a/p`
  have hterm : ∀ a ∈ Ico 1 p, ∃ R : ℚ_[p], ‖R‖ ≤ q ^ 5 ∧
      tauAnPole p (-(a : ℚ) / p) = -((((1 / 4 : ℚ) * (p : ℚ) ^ 4 * ((a : ℚ)⁻¹) ^ 4 : ℚ) : ℚ_[p]) + R) := by
    intro a ha
    rw [mem_Ico] at ha
    have hna : ¬ p ∣ a := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hv : padicValRat p (-(a : ℚ) / p) < 0 := by
      rw [neg_div, padicValRat.neg, padicValRat.div ha0 hp0, padicValRat.self (Fact.out : p.Prime).one_lt,
        padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hna]
      norm_num
    set t : ℚ_[p] := ((-(a : ℚ) / p : ℚ) : ℚ_[p])⁻¹ with htdef
    have htq : t = ((-(p : ℚ) * (a : ℚ)⁻¹ : ℚ) : ℚ_[p]) := by
      rw [htdef, ← Rat.cast_inv]; congr 1; field_simp
    have ht : ‖t‖ ≤ q := pt_norm_inv_le hv
    have hsum := pt_summable_kappa (p := p) (ht.trans pt_inv_p_le_half)
    rw [tauAnPole_eq hv, hsum.tsum_eq_add_tsum_ite 3]
    refine ⟨∑' d, if d = 3 then 0 else ((kappa d : ℚ) : ℚ_[p]) * t ^ (d + 1), ?_, ?_⟩
    · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun d => ?_
      split_ifs with hd3
      · simp; positivity
      rw [norm_mul, norm_pow]
      rcases Nat.lt_or_ge d 3 with hlt | hge
      · rw [kappa_of_lt hlt]; simp; positivity
      rcases Nat.lt_or_ge d 5 with hlt5 | hge5
      · obtain rfl : d = 4 := by omega
        calc ‖((kappa 4 : ℚ) : ℚ_[p])‖ * ‖t‖ ^ (4 + 1) ≤ 1 * q ^ 5 :=
              mul_le_mul (pt_kappa_norm_one hp (by omega)) (pow_le_pow_left₀ (norm_nonneg _) ht _)
                (by positivity) (by norm_num)
          _ = q ^ 5 := one_mul _
      · calc ‖((kappa d : ℚ) : ℚ_[p])‖ * ‖t‖ ^ (d + 1) ≤ (p : ℝ) * q ^ (d + 1) :=
              mul_le_mul (pt_kappa_norm_p hp2 d) (pow_le_pow_left₀ (norm_nonneg _) ht _)
                (by positivity) (by positivity)
          _ = q ^ d := by rw [pow_succ, ← mul_assoc, mul_comm (p : ℝ), mul_assoc, hpq, mul_one]
          _ ≤ q ^ 5 := pow_le_pow_of_le_one hq0 hq1 hge5
    · congr 1
      rw [htq, kappa_three]
      push_cast
      ring
  choose! R hR hRe using hterm
  unfold Cp
  rw [sum_congr rfl hRe, sum_neg_distrib, norm_neg, sum_add_distrib]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [← Rat.cast_sum]
    refine (pt_norm_le_pow (n := 5) ?_)
    rw [← mul_sum]
    have h4 : vge p ((1 / 4 : ℚ) * (p : ℚ) ^ 4) 4 := by
      have h1 : vge p (1 / 4 : ℚ) 0 := by
        have := pt_vge_inv_unit (p := p) (a := 4) (fun hd => by
          have := Nat.le_of_dvd (by norm_num) hd; omega)
        simpa using this
      have h2 : vge p ((p : ℚ) ^ 4) 4 := by
        intro _
        rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]
        norm_num
      simpa using vge_mul h1 h2
    have := vge_mul h4 (pt_invPowSum_vge hp)
    norm_num at this ⊢
    exact this
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) hR

/-! ## Lemma 3.1 with far poles: rational preliminaries -/

/-- `∏_{s ∈ S} (X - s)` over `ℚ`. -/
def qPoleProd (S : Finset ℚ) : ℚ[X] := ∏ s ∈ S, (X - C s)

theorem qPoleProd_monic (S : Finset ℚ) : (qPoleProd S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem qPoleProd_natDegree (S : Finset ℚ) : (qPoleProd S).natDegree = S.card := by
  rw [qPoleProd, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  exact (sum_congr rfl fun j _ => natDegree_X_sub_C _).trans (by simp)

/-- The residue of `P / ∏_{s ∈ S}(X - s)` at `s`. -/
def qRes (S : Finset ℚ) (P : ℚ[X]) (s : ℚ) : ℚ := P.eval s / ∏ s' ∈ S.erase s, (s - s')

/-- Lagrange: `P = Π (P /ₘ Π) + ∑_s res_s ∏_{s' ≠ s} (X - s')`. -/
theorem pt_lagrange (S : Finset ℚ) (P : ℚ[X]) :
    P = qPoleProd S * (P /ₘ qPoleProd S) + ∑ s ∈ S, C (qRes S P s) * qPoleProd (S.erase s) := by
  classical
  have hmod := modByMonic_add_div P (qPoleProd S)
  suffices h : P %ₘ qPoleProd S = ∑ s ∈ S, C (qRes S P s) * qPoleProd (S.erase s) by
    rw [← h]; linear_combination -hmod
  apply eq_of_degrees_lt_of_eval_finset_eq S
  · calc _ < degree (qPoleProd S) := degree_modByMonic_lt _ (qPoleProd_monic S)
      _ = S.card := by rw [degree_eq_natDegree (qPoleProd_monic S).ne_zero, qPoleProd_natDegree]
  · rw [← mem_degreeLT]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_degreeLT, degree_eq_natDegree (qPoleProd_monic _).ne_zero, qPoleProd_natDegree,
      card_erase_of_mem hj]
    have : 0 < S.card := card_pos.mpr ⟨j, hj⟩
    exact_mod_cast Nat.sub_lt this one_pos
  · intro k hk
    have hQ : (qPoleProd S).eval k = 0 := by
      rw [qPoleProd, eval_prod]; exact prod_eq_zero hk (by simp)
    have hl : (P %ₘ qPoleProd S).eval k = P.eval k := by
      conv_rhs => rw [← hmod]
      simp [hQ]
    rw [hl, eval_finsetSum, sum_eq_single k]
    · rw [eval_mul, eval_C, qRes, qPoleProd, eval_prod]
      have hne : ∏ l ∈ S.erase k, (k - l) ≠ 0 :=
        prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr (ne_of_mem_erase hl).symm
      have : ∏ l ∈ S.erase k, eval k (X - C l) = ∏ l ∈ S.erase k, (k - l) :=
        prod_congr rfl fun l _ => by simp
      rw [this, div_mul_cancel₀ _ hne]
    · intro j hj hjk
      rw [eval_mul, qPoleProd, eval_prod,
        prod_eq_zero (mem_erase.mpr ⟨fun h => hjk h.symm, hk⟩) (by simp), mul_zero]
    · intro h; exact absurd hk h

/-- The subring of `p`-integral rationals. -/
def ptZp (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | vge p x 0}
  mul_mem' ha hb := by simpa using vge_mul ha hb
  one_mem' := vge_one
  add_mem' ha hb := vge_add ha hb
  zero_mem' := vge_zero 0
  neg_mem' ha := vge_neg ha

theorem pt_lifts {P : ℚ[X]} (hP : vpGge p P 0) : P ∈ lifts (ptZp p).subtype :=
  (lifts_iff_coeff_lifts P).mpr fun n => ⟨⟨P.coeff n, hP n⟩, rfl⟩

/-- Division of an integral polynomial by an integral monic polynomial is integral. -/
theorem pt_divByMonic_vge {P Q : ℚ[X]} (hP : vpGge p P 0) (hQ : Q.Monic) (hQi : vpGge p Q 0) :
    vpGge p (P /ₘ Q) 0 := by
  obtain ⟨Q', hQ'map, -, hQ'monic⟩ := lifts_and_degree_eq_and_monic (pt_lifts hQi) hQ
  obtain ⟨P', hP'⟩ := pt_lifts hP
  have hP'' : P'.map (ptZp p).subtype = P := hP'
  rw [← hQ'map, ← hP'', ← map_divByMonic _ hQ'monic]
  intro n; rw [coeff_map]; exact (P' /ₘ Q').coeff n |>.2

theorem pt_eval_vge {P : ℚ[X]} (hP : vpGge p P 0) {x : ℚ} (hx : vge p x 0) :
    vge p (P.eval x) 0 := by
  rw [eval_eq_sum_range]
  exact vge_sum _ _ fun n _ => by simpa using vge_mul (hP n) (vge_pow0' hx n)

/-! ## Power series of the far part -/

/-- `-1/(X - s) = ∑ s^{-(d+1)} X^d`. -/
def farSeries (s : ℚ) : PowerSeries ℚ := PowerSeries.mk fun d => (s⁻¹) ^ (d + 1)

theorem X_sub_C_mul_farSeries {s : ℚ} (hs : s ≠ 0) :
    ((X - C s : ℚ[X]) : PowerSeries ℚ) * farSeries s = -1 := by
  ext n
  rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, sub_mul]
  rcases n with _ | n
  · simp [farSeries, hs]
  · rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    simp only [farSeries, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_one]
    simp only [Nat.succ_ne_zero, if_false, neg_zero]
    have h1 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    linear_combination (-(s⁻¹) ^ (n + 1)) * h1

/-- The Taylor coefficients of the analytic part `Q + ∑_{s ∈ F} ρ_s/(z - s)`. -/
def fCoeff (Q : ℚ[X]) (F : Finset ℚ) (ρ : ℚ → ℚ) (d : ℕ) : ℚ :=
  Q.coeff d - ∑ s ∈ F, ρ s * (s⁻¹) ^ (d + 1)

/-- `Φ · (Q + ∑ ρ_s/(z-s)) = Φ Q + ∑ ρ_s ∏_{s' ≠ s}(z - s')`. -/
theorem qPoleProd_mul_fCoeff (Q : ℚ[X]) (F : Finset ℚ) (hF0 : ∀ s ∈ F, s ≠ 0) (ρ : ℚ → ℚ) :
    (qPoleProd F : PowerSeries ℚ) * PowerSeries.mk (fCoeff Q F ρ) =
      ((qPoleProd F * Q + ∑ s ∈ F, C (ρ s) * qPoleProd (F.erase s) : ℚ[X]) : PowerSeries ℚ) := by
  have hmk : PowerSeries.mk (fCoeff Q F ρ) =
      (Q : PowerSeries ℚ) - ∑ s ∈ F, PowerSeries.C (ρ s) * farSeries s := by
    ext d
    simp [fCoeff, farSeries, map_sum, PowerSeries.coeff_C_mul]
  have hcoe : ((qPoleProd F * Q + ∑ s ∈ F, C (ρ s) * qPoleProd (F.erase s) : ℚ[X]) :
      PowerSeries ℚ) = (qPoleProd F : PowerSeries ℚ) * (Q : PowerSeries ℚ) +
        ∑ s ∈ F, PowerSeries.C (ρ s) * (qPoleProd (F.erase s) : PowerSeries ℚ) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_mul, map_sum]
    simp only [map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
  rw [hcoe, hmk, mul_sub, Finset.mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun s hs => ?_
  have hsplit : qPoleProd F = (X - C s) * qPoleProd (F.erase s) := by
    rw [qPoleProd, qPoleProd, mul_prod_erase F (fun x => X - C x) hs]
  rw [hsplit, Polynomial.coe_mul]
  have := X_sub_C_mul_farSeries (hF0 s hs)
  linear_combination (-(PowerSeries.C (ρ s)) * (qPoleProd (F.erase s) : PowerSeries ℚ)) * this

/-- If `Ψ · f = N` as power series, with `Ψ(0)` a unit, the other coefficients of `Ψ` in `pℤ_p`, `N`
integral and `≡ 0 (mod p)` beyond degree `p + 1`, then `f` is integral and `≡ 0` beyond `p + 1`. -/
theorem pt_series_vge (Ψ N : ℚ[X]) (f : ℕ → ℚ)
    (hΨ0 : Ψ.coeff 0 ≠ 0) (hΨ0v : padicValRat p (Ψ.coeff 0) = 0)
    (hΨ : ∀ n, 1 ≤ n → vge p (Ψ.coeff n) 1)
    (hN : vpGge p N 0) (hN1 : ∀ d, p + 1 < d → vge p (N.coeff d) 1)
    (hmul : (Ψ : PowerSeries ℚ) * PowerSeries.mk f = (N : PowerSeries ℚ)) :
    ∀ d, vge p (f d) 0 ∧ (p + 1 < d → vge p (f d) 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  have hc := congrArg (PowerSeries.coeff d) hmul
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ'] at hc
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk, Nat.sub_zero] at hc
  have hf : f d = (Ψ.coeff 0)⁻¹ *
      (N.coeff d - ∑ i ∈ range d, Ψ.coeff (i + 1) * f (d - (i + 1))) := by
    field_simp
    linarith
  have hinv : vge p ((Ψ.coeff 0)⁻¹) 0 := by
    intro _; rw [padicValRat.inv, hΨ0v]; simp
  have hS : vge p (∑ i ∈ range d, Ψ.coeff (i + 1) * f (d - (i + 1))) 1 := by
    refine vge_sum _ _ fun i hi => ?_
    rw [mem_range] at hi
    have := vge_mul (hΨ (i + 1) (by omega)) (ih (d - (i + 1)) (by omega)).1
    simpa using this
  rw [hf]
  constructor
  · have := vge_mul hinv (vge_add (hN d) (vge_neg (vge_mono hS (by norm_num))))
    simpa [sub_eq_add_neg] using this
  · intro hd
    have := vge_mul hinv (vge_add (hN1 d hd) (vge_neg hS))
    simpa [sub_eq_add_neg] using this

/-- The shape of `Ψ = ∏ (p s - p z)`: unit constant term, other coefficients in `pℤ_p`. -/
def PsiShape (p : ℕ) (P : ℚ[X]) : Prop :=
  P.coeff 0 ≠ 0 ∧ padicValRat p (P.coeff 0) = 0 ∧ ∀ n, 1 ≤ n → vge p (P.coeff n) 1

theorem psiShape_one : PsiShape p (1 : ℚ[X]) := by
  refine ⟨by simp, by simp, fun n hn => ?_⟩
  rw [coeff_one, if_neg (by omega)]; exact vge_zero _

theorem psiShape_mul {P Q : ℚ[X]} (hP : PsiShape p P) (hQ : PsiShape p Q) :
    PsiShape p (P * Q) := by
  obtain ⟨hP0, hP0v, hP1⟩ := hP
  obtain ⟨hQ0, hQ0v, hQ1⟩ := hQ
  have hP0' : vge p (P.coeff 0) 0 := fun _ => by rw [hP0v]; simp
  have hQ0' : vge p (Q.coeff 0) 0 := fun _ => by rw [hQ0v]; simp
  have hPall : ∀ n, vge p (P.coeff n) 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hP0'
    · exact vge_mono (hP1 n hn) (by norm_num)
  have hQall : ∀ n, vge p (Q.coeff n) 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hQ0'
    · exact vge_mono (hQ1 n hn) (by norm_num)
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rw [mul_coeff_zero]; exact mul_ne_zero hP0 hQ0
  · rw [mul_coeff_zero, padicValRat.mul hP0 hQ0, hP0v, hQ0v, add_zero]
  · rw [coeff_mul]
    refine vge_sum _ _ fun x hx => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    rcases Nat.eq_zero_or_pos x.1 with h1 | h1
    · have := vge_mul (hPall x.1) (hQ1 x.2 (by omega)); simpa using this
    · have := vge_mul (hP1 x.1 h1) (hQall x.2); simpa using this

theorem psiShape_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, PsiShape p (f i)) :
    PsiShape p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psiShape_one (p := p)
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact psiShape_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

/-- A factor `p s - p z` with `v_p(s) = -1`. -/
theorem psiShape_factor {s : ℚ} (hs : padicValRat p s = -1) :
    PsiShape p (C ((p : ℚ) * s) - C (p : ℚ) * X) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨by simp [hp0, hs0], ?_, fun n hn => ?_⟩
  · simp only [coeff_sub, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, sub_zero]
    rw [padicValRat.mul hp0 hs0, padicValRat.self hp.out.one_lt, hs]; norm_num
  · rw [coeff_sub, coeff_C, if_neg (by omega), zero_sub, coeff_C_mul, coeff_X]
    split_ifs with h1
    · subst h1
      intro _; rw [padicValRat.neg, mul_one, padicValRat.self hp.out.one_lt]; norm_num
    · simpa using vge_zero (p := p) 1

/-! ## The near residues -/

theorem pt_padicValRat_prod {ι : Type*} (T : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ T, f i ≠ 0) :
    padicValRat p (∏ i ∈ T, f i) = ∑ i ∈ T, padicValRat p (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a T))
      (prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem pt_vge_div_of_le {x y b U : ℚ} (hx : vge p x b) (hy : y ≠ 0)
    (hU : (padicValRat p y : ℚ) ≤ U) : vge p (x / y) (b - U) := by
  intro hxy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxy
  rw [padicValRat.div hx0 hy]
  push_cast
  linarith [hx hx0]

theorem pt_valRat_int_nonneg (r : ℤ) (_hr : (r : ℚ) ≠ 0) : 0 ≤ padicValRat p (r : ℚ) := by
  rw [padicValRat.of_int]; exact_mod_cast Nat.zero_le _

/-- An integer minus a far pole has valuation exactly `-1`. -/
theorem pt_valRat_int_sub_far (r : ℤ) {s : ℚ} (hs : padicValRat p s = -1) :
    (r : ℚ) - s ≠ 0 ∧ padicValRat p ((r : ℚ) - s) = -1 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  by_cases hr : (r : ℚ) = 0
  · rw [hr, zero_sub, padicValRat.neg]; exact ⟨neg_ne_zero.mpr hs0, hs⟩
  have hne : (r : ℚ) - s ≠ 0 := by
    intro h
    have : s = r := by linarith
    have := pt_valRat_int_nonneg (p := p) r hr
    rw [← ‹s = r›] at this; omega
  refine ⟨hne, ?_⟩
  have := padicValRat.add_eq_min (p := p) (q := (r : ℚ)) (r := -s) (by simpa [sub_eq_add_neg] using hne)
    hr (neg_ne_zero.mpr hs0) (by rw [padicValRat.neg, hs]; have := pt_valRat_int_nonneg (p := p) r hr; omega)
  rw [← sub_eq_add_neg, padicValRat.neg, hs] at this
  rw [this]
  have := pt_valRat_int_nonneg (p := p) r hr
  omega

theorem pt_valRat_c (n : ℕ) : padicValRat p ((-(p : ℚ)) ^ (-(n : ℤ))) = -n := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow, padicValRat.neg,
    padicValRat.self hp.out.one_lt]
  ring

/-- **The near residues are integral** (Lemma 3.1 with far poles). -/
theorem pt_near_res_vge (T : Finset ℤ) (hT : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → ¬ (p : ℤ) ∣ r - s)
    (F : Finset ℚ) (hF : ∀ s ∈ F, padicValRat p s = -1) (U : ℚ[X]) (hU : vpGge p U 0)
    (r : ℤ) (hr : r ∈ T) :
    vge p (qRes (T.image (fun r : ℤ => (r : ℚ)) ∪ F)
      (C ((-(p : ℚ)) ^ (-(F.card : ℤ))) * U) (r : ℚ)) 0 := by
  set Tq := T.image (fun r : ℤ => (r : ℚ))
  have hdisj : Disjoint Tq F := by
    rw [Finset.disjoint_left]
    intro x hx hxF
    obtain ⟨r', _, rfl⟩ := mem_image.mp hx
    have h1 := hF _ hxF
    by_cases h0 : ((r' : ℤ) : ℚ) = 0
    · rw [h0] at h1; simp at h1
    · have := pt_valRat_int_nonneg (p := p) r' h0; omega
  have hrq : (r : ℚ) ∈ Tq := mem_image_of_mem _ hr
  have herase : (Tq ∪ F).erase (r : ℚ) = Tq.erase (r : ℚ) ∪ F := by
    rw [erase_union_distrib, erase_eq_of_notMem (fun h => Finset.disjoint_left.mp hdisj hrq h)]
  unfold qRes
  rw [herase, prod_union (Finset.disjoint_of_subset_left (erase_subset _ _) hdisj)]
  have hnear : ∀ x ∈ Tq.erase (r : ℚ), (r : ℚ) - x ≠ 0 ∧ padicValRat p ((r : ℚ) - x) = 0 := by
    intro x hx
    obtain ⟨hxr, hxT⟩ := mem_erase.mp hx
    obtain ⟨r', hr', rfl⟩ := mem_image.mp hxT
    have hne : r ≠ r' := fun h => hxr (by rw [h])
    refine ⟨sub_ne_zero.mpr (fun h => hne (by exact_mod_cast h)), ?_⟩
    rw [show (r : ℚ) - (r' : ℚ) = ((r - r' : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd (hT r hr r' hr' hne)]
    rfl
  have hfar : ∀ s ∈ F, (r : ℚ) - s ≠ 0 ∧ padicValRat p ((r : ℚ) - s) = -1 :=
    fun s hs => pt_valRat_int_sub_far r (hF s hs)
  have hden0 : (∏ x ∈ Tq.erase (r : ℚ), ((r : ℚ) - x)) * ∏ s ∈ F, ((r : ℚ) - s) ≠ 0 :=
    mul_ne_zero (prod_ne_zero_iff.mpr fun x hx => (hnear x hx).1)
      (prod_ne_zero_iff.mpr fun s hs => (hfar s hs).1)
  have hdenv : (padicValRat p ((∏ x ∈ Tq.erase (r : ℚ), ((r : ℚ) - x)) *
      ∏ s ∈ F, ((r : ℚ) - s)) : ℚ) ≤ -(F.card : ℚ) := by
    rw [padicValRat.mul (prod_ne_zero_iff.mpr fun x hx => (hnear x hx).1)
      (prod_ne_zero_iff.mpr fun s hs => (hfar s hs).1),
      pt_padicValRat_prod _ _ fun x hx => (hnear x hx).1,
      pt_padicValRat_prod _ _ fun s hs => (hfar s hs).1,
      sum_congr rfl fun x hx => (hnear x hx).2, sum_congr rfl fun s hs => (hfar s hs).2]
    simp
  have hnum : vge p ((C ((-(p : ℚ)) ^ (-(F.card : ℤ))) * U).eval (r : ℚ)) (-(F.card : ℚ)) := by
    rw [eval_mul, eval_C]
    have hc : vge p ((-(p : ℚ)) ^ (-(F.card : ℤ))) (-(F.card : ℚ)) := fun _ => by
      rw [pt_valRat_c]; push_cast; rfl
    have := vge_mul hc (pt_eval_vge hU (by
      have := mm_vge_int (p := p) r; simpa using this))
    simpa using this
  have := pt_vge_div_of_le hnum hden0 hdenv
  simpa using this

/-! ## Division preserves "`≡ 0 (mod p)` beyond degree `p + 1`" -/

theorem pt_divByMonic_high {R Q : ℚ[X]} (hR : vpGge p R 0)
    (hR1 : ∀ d, p + 1 < d → vge p (R.coeff d) 1) (hQ : Q.Monic) (hQi : vpGge p Q 0) :
    ∀ d, p + 1 < d → vge p ((R /ₘ Q).coeff d) 1 := by
  set Rlo : ℚ[X] := ∑ d ∈ range (p + 2), C (R.coeff d) * X ^ d with hRlo
  have hRlo_coeff : ∀ d, Rlo.coeff d = if d < p + 2 then R.coeff d else 0 := by
    intro d
    rw [hRlo, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq]
    simp [mem_range]
  set Rhi : ℚ[X] := C ((p : ℚ)⁻¹) * (R - Rlo) with hRhi
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hsplit : R = Rlo + C (p : ℚ) * Rhi := by
    rw [hRhi, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hp0, C_1, one_mul]; ring
  have hRhi_int : vpGge p Rhi 0 := by
    intro n
    rw [hRhi, coeff_C_mul, coeff_sub, hRlo_coeff]
    split_ifs with hn
    · simpa using vge_zero (p := p) 0
    · have hinv : vge p ((p : ℚ)⁻¹) (-1) := by
        intro _; rw [padicValRat.inv, padicValRat.self hp.out.one_lt]; norm_num
      rw [sub_zero]
      exact vge_mono (vge_mul hinv (hR1 n (by omega))) (by norm_num)
  have hdeg : (Rlo /ₘ Q).natDegree ≤ p + 1 := by
    refine (natDegree_divByMonic _ hQ).le.trans ?_
    refine le_trans (Nat.sub_le _ _) ?_
    refine natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; rw [mem_range] at hd; omega
  intro d hd
  rw [hsplit, add_divByMonic, ← smul_eq_C_mul, smul_divByMonic, coeff_add, coeff_smul,
    coeff_eq_zero_of_natDegree_lt (by omega), zero_add, smul_eq_mul]
  have hp1 : vge p (p : ℚ) 1 := by
    intro _; rw [padicValRat.self hp.out.one_lt]; norm_num
  simpa using vge_mul hp1 (pt_divByMonic_vge hRhi_int hQ hQi d)

/-! ## The analytic part -/

theorem pt_disj (T : Finset ℤ) (F : Finset ℚ) (hF : ∀ s ∈ F, padicValRat p s = -1) :
    Disjoint (T.image fun r : ℤ => (r : ℚ)) F := by
  rw [Finset.disjoint_left]
  intro x hx hxF
  obtain ⟨r', _, rfl⟩ := mem_image.mp hx
  have h1 := hF _ hxF
  by_cases h0 : ((r' : ℤ) : ℚ) = 0
  · rw [h0] at h1; simp at h1
  · have := pt_valRat_int_nonneg (p := p) r' h0; omega

theorem qPoleProd_union {A B : Finset ℚ} (h : Disjoint A B) :
    qPoleProd (A ∪ B) = qPoleProd A * qPoleProd B := prod_union h

theorem pt_vpGge_X : vpGge p (X : ℚ[X]) 0 := fun n => by
  rw [coeff_X]; split_ifs
  · exact vge_one
  · exact vge_zero 0

theorem pt_vpGge_X_sub_int (r : ℤ) : vpGge p (X - C (r : ℚ)) 0 := by
  rw [sub_eq_add_neg, ← C_neg]
  exact vpGge_add pt_vpGge_X (vpGge_C (by simpa using vge_neg (mm_vge_int (p := p) r)))

theorem pt_qPoleProd_int (T : Finset ℤ) (A : Finset ℚ) (hA : A ⊆ T.image fun r : ℤ => (r : ℚ)) :
    vpGge p (qPoleProd A) 0 := by
  have := vpGge_prod (p := p) A (fun s => X - C s) (fun _ => 0) fun s hs => by
    obtain ⟨r, _, rfl⟩ := mem_image.mp (hA hs)
    exact pt_vpGge_X_sub_int r
  simpa [qPoleProd] using this

theorem pt_card_le (T : Finset ℤ) (hT : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → ¬ (p : ℤ) ∣ r - s) :
    T.card ≤ p := by
  have hinj : Set.InjOn (fun r : ℤ => (r % p).toNat) T := by
    intro r hr s hs h
    by_contra hne
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have h1 : r % p = s % p := by
      have := Int.emod_nonneg r hp0.ne'; have := Int.emod_nonneg s hp0.ne'
      simp only at h; omega
    exact hT r hr s hs hne (Int.ModEq.dvd h1.symm)
  have := card_le_card_of_injOn (t := range p) _ (fun r _ => ?_) hinj
  · simpa using this
  · simp only [coe_range, Set.mem_Iio]
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have := Int.emod_lt_of_pos r hp0
    have := Int.emod_nonneg r hp0.ne'
    omega

/-- **The analytic part is integral**: every `κ_d f_d` is `p`-integral, where `f_d` are the Taylor
coefficients of `Q + ∑_{s ∈ F} ρ_s/(z - s)`. -/
theorem pt_far_vge (hp7 : 7 ≤ p) (T : Finset ℤ)
    (hT : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → ¬ (p : ℤ) ∣ r - s)
    (F : Finset ℚ) (hF : ∀ s ∈ F, padicValRat p s = -1)
    (U : ℚ[X]) (hU : vpGge p U 0) (hU1 : ∀ d, p + 1 < d → vge p (U.coeff d) 1) (d : ℕ) :
    vge p (kappa d * fCoeff ((C ((-(p : ℚ)) ^ (-(F.card : ℤ))) * U) /ₘ
      qPoleProd (T.image (fun r : ℤ => (r : ℚ)) ∪ F)) F
      (qRes (T.image (fun r : ℤ => (r : ℚ)) ∪ F) (C ((-(p : ℚ)) ^ (-(F.card : ℤ))) * U)) d) 0 := by
  set Tq := T.image (fun r : ℤ => (r : ℚ)) with hTq
  set S := Tq ∪ F with hS
  set c : ℚ := (-(p : ℚ)) ^ (-(F.card : ℤ)) with hc
  set U' := C c * U with hU'
  set Q := U' /ₘ qPoleProd S with hQ
  set ρ := qRes S U' with hρ
  have hdisj := pt_disj (p := p) T F hF
  have hF0 : ∀ s ∈ F, s ≠ 0 := fun s hs h => by have := hF s hs; rw [h] at this; simp at this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  -- the Lagrange decomposition, split into near and far poles
  set M := qPoleProd F * Q + ∑ s ∈ F, C (ρ s) * qPoleProd (F.erase s) with hM
  set W0 := ∑ r ∈ Tq, C (ρ r) * qPoleProd (Tq.erase r) with hW0
  have hLag : U' = qPoleProd Tq * M + qPoleProd F * W0 := by
    have h := pt_lagrange S U'
    rw [← hQ, ← hρ, hS, qPoleProd_union hdisj, sum_union hdisj] at h
    have hfar : ∀ s ∈ F, qPoleProd ((Tq ∪ F).erase s) = qPoleProd Tq * qPoleProd (F.erase s) := by
      intro s hs
      rw [erase_union_distrib, erase_eq_of_notMem (fun h => Finset.disjoint_left.mp hdisj h hs),
        qPoleProd_union (Finset.disjoint_of_subset_right (erase_subset _ _) hdisj)]
    have hnear : ∀ r ∈ Tq, qPoleProd ((Tq ∪ F).erase r) = qPoleProd (Tq.erase r) * qPoleProd F := by
      intro r hr
      rw [erase_union_distrib, erase_eq_of_notMem (fun h => Finset.disjoint_left.mp hdisj hr h),
        qPoleProd_union (Finset.disjoint_of_subset_left (erase_subset _ _) hdisj)]
    rw [show ∑ x ∈ Tq, C (ρ x) * qPoleProd ((Tq ∪ F).erase x) =
        ∑ x ∈ Tq, C (ρ x) * (qPoleProd (Tq.erase x) * qPoleProd F) from
        sum_congr rfl fun r hr => by rw [hnear r hr],
      show ∑ x ∈ F, C (ρ x) * qPoleProd ((Tq ∪ F).erase x) =
        ∑ x ∈ F, C (ρ x) * (qPoleProd Tq * qPoleProd (F.erase x)) from
        sum_congr rfl fun s hs => by rw [hfar s hs]] at h
    rw [← hTq] at h
    rw [h, hM, hW0]
    have s1 : qPoleProd Tq * ∑ i ∈ F, C (ρ i) * qPoleProd (F.erase i) =
        ∑ x ∈ F, C (ρ x) * (qPoleProd Tq * qPoleProd (F.erase x)) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    have s2 : qPoleProd F * ∑ i ∈ Tq, C (ρ i) * qPoleProd (Tq.erase i) =
        ∑ x ∈ Tq, C (ρ x) * (qPoleProd (Tq.erase x) * qPoleProd F) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [mul_add, s1, s2]
    ring
  -- clearing `c`
  set κ : ℚ := (-(p : ℚ)) ^ F.card with hκ
  have hκc : κ * c = 1 := by
    rw [hκ, hc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr hp0))]
  set Ψ : ℚ[X] := ∏ s ∈ F, (C ((p : ℚ) * s) - C (p : ℚ) * X) with hΨdef
  have hΨ : Ψ = C κ * qPoleProd F := by
    rw [hΨdef, hκ, qPoleProd, ← prod_const, map_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ => ?_
    simp only [map_neg, map_natCast, map_mul]; ring
  set N := C κ * M with hN
  have hUeq : U = qPoleProd Tq * N + Ψ * W0 := by
    have : U = C κ * U' := by rw [hU', ← mul_assoc, ← C_mul, hκc, C_1, one_mul]
    rw [this, hLag, hN, hΨ]; ring
  have hNdiv : N = (U - Ψ * W0) /ₘ qPoleProd Tq := by
    rw [show U - Ψ * W0 = qPoleProd Tq * N by rw [hUeq]; ring,
      mul_divByMonic_cancel_left _ (qPoleProd_monic Tq)]
  -- integrality
  have hρT : ∀ r ∈ Tq, vge p (ρ r) 0 := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := mem_image.mp hr
    exact pt_near_res_vge T hT F hF U hU r' hr'
  have hTqi : ∀ A ⊆ Tq, vpGge p (qPoleProd A) 0 := fun A hA => pt_qPoleProd_int T A hA
  have hW0i : vpGge p W0 0 := by
    have := vpGge_sum (p := p) Tq (fun r => C (ρ r) * qPoleProd (Tq.erase r)) (b := 0)
      fun r hr => by simpa using vpGge_mul (vpGge_C (hρT r hr)) (hTqi _ (erase_subset _ _))
    simpa [hW0] using this
  have hshape : PsiShape p Ψ := psiShape_prod _ _ fun s hs => psiShape_factor (hF s hs)
  have hΨi : vpGge p Ψ 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact fun _ => by rw [hshape.2.1]; simp
    · exact vge_mono (hshape.2.2 n hn) (by norm_num)
  have hRi : vpGge p (U - Ψ * W0) 0 := by
    rw [sub_eq_add_neg]
    exact vpGge_add hU (vpGge_neg (by simpa using vpGge_mul hΨi hW0i))
  have hW0deg : ∀ j, p ≤ j → W0.coeff j = 0 := by
    intro j hj
    rw [hW0, finsetSum_coeff]
    refine sum_eq_zero fun r hr => ?_
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [qPoleProd_natDegree, card_erase_of_mem hr]
    have h1 : Tq.card ≤ T.card := card_image_le
    have h2 := pt_card_le (p := p) T hT
    have : 0 < Tq.card := card_pos.mpr ⟨r, hr⟩
    omega
  have hR1 : ∀ d, p + 1 < d → vge p ((U - Ψ * W0).coeff d) 1 := by
    intro d hd
    rw [coeff_sub, sub_eq_add_neg]
    refine vge_add (hU1 d hd) (vge_neg ?_)
    rw [coeff_mul]
    refine vge_sum _ _ fun x hx => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hj : p ≤ x.2
    · rw [hW0deg _ hj, mul_zero]; exact vge_zero _
    · have := vge_mul (hshape.2.2 x.1 (by omega)) (hW0i x.2); simpa using this
  have hNi : vpGge p N 0 := by
    rw [hNdiv]; exact pt_divByMonic_vge hRi (qPoleProd_monic Tq) (hTqi Tq subset_rfl)
  have hN1 : ∀ d, p + 1 < d → vge p (N.coeff d) 1 := by
    rw [hNdiv]; exact pt_divByMonic_high hRi hR1 (qPoleProd_monic Tq) (hTqi Tq subset_rfl)
  -- the power series identity
  have hmul : (Ψ : PowerSeries ℚ) * PowerSeries.mk (fCoeff Q F ρ) = (N : PowerSeries ℚ) := by
    rw [hΨ, hN, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc,
      qPoleProd_mul_fCoeff Q F hF0 ρ]
  have hf := pt_series_vge Ψ N _ hshape.1 hshape.2.1 hshape.2.2 hNi hN1 hmul d
  -- `κ_d`
  rcases Nat.lt_or_ge (p + 1) d with hd | hd
  · have hk : vge p (kappa d) (-1) := fun hk => by
      exact_mod_cast kappa_padicVal_ge' p (by omega) d hk
    exact vge_mono (vge_mul hk (hf.2 hd)) (by norm_num)
  · have hk : vge p (kappa d) 0 := fun hk => by exact_mod_cast kappa_integral' p hp7 d hd hk
    simpa using vge_mul hk hf.1

/-! ## Assembly of Lemma 3.1 with far poles -/

theorem pt_H5_vge {n : ℕ} (hn : n < p) : vge p (H5 n) 0 := by
  unfold H5
  refine vge_sum _ _ fun v hv => ?_
  rw [mem_Icc] at hv
  have hnv : ¬ p ∣ v := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have := vge_pow0' (pt_vge_inv_unit (p := p) hnv) 5
  rw [one_div, ← inv_pow]; exact this

theorem pt_eval_map (P : ℚ[X]) (s : ℚ) :
    (P.map (algebraMap ℚ ℚ_[p])).eval (s : ℚ_[p]) = ((P.eval s : ℚ) : ℚ_[p]) := by
  rw [← eq_ratCast (algebraMap ℚ ℚ_[p]) s, eval_map, eval₂_at_apply, eq_ratCast]

/-- `τ` on polynomials through `κ`. -/
def tauK (Q : ℚ[X]) : ℚ := ∑ d ∈ range (Q.natDegree + 1), Q.coeff d * kappa d

theorem tauP_map (Q : ℚ[X]) : tauP p (Q.map (algebraMap ℚ ℚ_[p])) = ((tauK Q : ℚ) : ℚ_[p]) := by
  unfold tauP tauK
  rw [sum_over_range' _ (fun _ => by simp) (Q.natDegree + 1)
    (by rw [natDegree_map_eq_of_injective (algebraMap ℚ ℚ_[p]).injective]; omega)]
  push_cast
  refine sum_congr rfl fun d _ => ?_
  rw [coeff_map, eq_ratCast]

/-- The Taylor sum of the analytic part: `τ(Q) + ∑_{s ∈ F} ρ_s τ(1/(z - s)) = ∑_d κ_d f_d`. -/
theorem pt_analytic_eq (Q : ℚ[X]) (F : Finset ℚ) (hF : ∀ s ∈ F, padicValRat p s < 0) (ρ : ℚ → ℚ) :
    ((tauK Q : ℚ) : ℚ_[p]) + ∑ s ∈ F, ((ρ s : ℚ) : ℚ_[p]) * tauAnPole p s =
      ∑' d, ((kappa d * fCoeff Q F ρ d : ℚ) : ℚ_[p]) := by
  have hsum : ∀ s ∈ F, Summable fun d : ℕ =>
      ((ρ s : ℚ) : ℚ_[p]) * (((kappa d : ℚ) : ℚ_[p]) * ((s : ℚ_[p])⁻¹) ^ (d + 1)) := fun s hs =>
    (pt_summable_kappa ((pt_norm_inv_le (hF s hs)).trans pt_inv_p_le_half)).mul_left _
  have h1 : ∑ s ∈ F, ((ρ s : ℚ) : ℚ_[p]) * tauAnPole p s =
      -∑' d, ∑ s ∈ F, ((ρ s : ℚ) : ℚ_[p]) *
        (((kappa d : ℚ) : ℚ_[p]) * ((s : ℚ_[p])⁻¹) ^ (d + 1)) := by
    rw [Summable.tsum_finsetSum hsum, ← sum_neg_distrib]
    refine sum_congr rfl fun s hs => ?_
    rw [tauAnPole_eq (hF s hs), tsum_mul_left]; ring
  have h2 : ((tauK Q : ℚ) : ℚ_[p]) = ∑' d, ((Q.coeff d * kappa d : ℚ) : ℚ_[p]) := by
    rw [tsum_eq_sum (s := range (Q.natDegree + 1)) (fun d hd => by
      rw [mem_range, not_lt] at hd
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp)]
    unfold tauK; push_cast; rfl
  have hs2 : Summable fun d => ((Q.coeff d * kappa d : ℚ) : ℚ_[p]) :=
    summable_of_ne_finset_zero (s := range (Q.natDegree + 1)) (fun d hd => by
      rw [mem_range, not_lt] at hd
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp)
  have hs1 : Summable fun d : ℕ => ∑ s ∈ F, ((ρ s : ℚ) : ℚ_[p]) *
      (((kappa d : ℚ) : ℚ_[p]) * ((s : ℚ_[p])⁻¹) ^ (d + 1)) := summable_sum hsum
  rw [h1, h2, ← sub_eq_add_neg, ← hs2.tsum_sub hs1]
  congr 1; funext d
  unfold fCoeff
  push_cast
  rw [mul_sub, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun s _ => by ring

/-- Lemma 3.1 with far poles, in rational form. -/
theorem lemma_3_1_rat (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (T : Finset ℤ)
    (hT : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → ¬ (p : ℤ) ∣ r - s) (hd : ∀ r ∈ T, dIdx r < p)
    (F : Finset ℚ) (hF : ∀ s ∈ F, padicValRat p s = -1)
    (Y : ℚ_[p][X]) (hY : ∀ i, ‖Y.coeff i‖ ≤ 1)
    (U : ℚ[X]) (hU : vpGge p U 0) (hU1 : ∀ d, p + 1 < d → vge p (U.coeff d) 1) :
    ∀ i, ‖(tauExtP p Y ((C ((-(p : ℚ)) ^ (-(F.card : ℤ))) * U).map (algebraMap ℚ ℚ_[p]))
        (T.image (fun r : ℤ => (r : ℚ)) ∪ F)).coeff i‖ ≤ 1 := by
  set Tq := T.image (fun r : ℤ => (r : ℚ)) with hTq
  set S := Tq ∪ F with hS
  set U' := C ((-(p : ℚ)) ^ (-(F.card : ℤ))) * U with hU'
  set Q := U' /ₘ qPoleProd S with hQ
  set ρ := qRes S U' with hρ
  have hdisj := pt_disj (p := p) T F hF
  -- transfer to `ℚ`
  have hprod : ∏ s ∈ S, (X - C (s : ℚ_[p])) = (qPoleProd S).map (algebraMap ℚ ℚ_[p]) := by
    rw [qPoleProd, Polynomial.map_prod]
    exact prod_congr rfl fun s _ => by simp
  have hExt : tauExtP p Y (U'.map (algebraMap ℚ ℚ_[p])) S =
      C ((tauK Q : ℚ) : ℚ_[p]) + ∑ s ∈ S, C ((ρ s : ℚ) : ℚ_[p]) * tauPoleP p Y s := by
    unfold tauExtP
    rw [hprod, ← map_divByMonic _ (qPoleProd_monic S), tauP_map]
    congr 1
    refine sum_congr rfl fun s _ => ?_
    congr 2
    rw [hρ, qRes, pt_eval_map]
    push_cast
    rfl
  -- the pole values
  have hnearP : ∀ r ∈ T, tauPoleP p Y (r : ℚ) = C ((H5 (dIdx r) : ℚ) : ℚ_[p]) - Y := by
    intro r _; unfold tauPoleP; rw [if_pos (by simp)]; simp
  have hfarP : ∀ s ∈ F, tauPoleP p Y s = C (tauAnPole p s) := by
    intro s hs
    unfold tauPoleP
    rw [if_neg]
    intro hden
    have : s = (s.num : ℚ) := ((Rat.den_eq_one_iff s).mp hden).symm
    have hv := hF s hs
    rw [this] at hv
    by_cases h0 : ((s.num : ℤ) : ℚ) = 0
    · rw [h0] at hv; simp at hv
    · have := pt_valRat_int_nonneg (p := p) s.num h0; omega
  have hρT : ∀ r ∈ T, ‖((ρ r : ℚ) : ℚ_[p])‖ ≤ 1 :=
    fun r hr => pt_norm_le_one_of_vge (pt_near_res_vge T hT F hF U hU r hr)
  intro i
  rw [hExt, hS, sum_union hdisj, sum_image (fun a _ b _ h => by exact_mod_cast h)]
  rw [show ∑ r ∈ T, C ((ρ (r : ℚ) : ℚ) : ℚ_[p]) * tauPoleP p Y (r : ℚ) =
      ∑ r ∈ T, C ((ρ (r : ℚ) : ℚ) : ℚ_[p]) * (C ((H5 (dIdx r) : ℚ) : ℚ_[p]) - Y) from
      sum_congr rfl fun r hr => by rw [hnearP r hr],
    show ∑ s ∈ F, C ((ρ s : ℚ) : ℚ_[p]) * tauPoleP p Y s =
      ∑ s ∈ F, C ((ρ s : ℚ) : ℚ_[p]) * C (tauAnPole p s) from
      sum_congr rfl fun s hs => by rw [hfarP s hs]]
  by_cases hi : i = 0
  · -- constant coefficient
    subst hi
    simp only [coeff_add, coeff_C_zero, finsetSum_coeff, coeff_C_mul, coeff_sub]
    have hA := pt_analytic_eq Q F (fun s hs => by rw [hF s hs]; norm_num) ρ
    have hAn : ‖∑' d, ((kappa d * fCoeff Q F ρ d : ℚ) : ℚ_[p])‖ ≤ 1 :=
      IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun d =>
        pt_norm_le_one_of_vge (pt_far_vge hp T hT F hF U hU hU1 d)
    have hB : ‖∑ r ∈ T, ((ρ r : ℚ) : ℚ_[p]) * (((H5 (dIdx r) : ℚ) : ℚ_[p]) - Y.coeff 0)‖ ≤ 1 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun r hr => ?_
      rw [norm_mul]
      refine mul_le_one₀ (hρT r hr) (norm_nonneg _) ?_
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact hY 0))
      exact pt_norm_le_one_of_vge (pt_H5_vge (hd r hr))
    have e : ((tauK Q : ℚ) : ℚ_[p]) + (∑ r ∈ T, ((ρ r : ℚ) : ℚ_[p]) *
        (((H5 (dIdx r) : ℚ) : ℚ_[p]) - Y.coeff 0) + ∑ s ∈ F, ((ρ s : ℚ) : ℚ_[p]) * tauAnPole p s) =
        (((tauK Q : ℚ) : ℚ_[p]) + ∑ s ∈ F, ((ρ s : ℚ) : ℚ_[p]) * tauAnPole p s) +
          ∑ r ∈ T, ((ρ r : ℚ) : ℚ_[p]) * (((H5 (dIdx r) : ℚ) : ℚ_[p]) - Y.coeff 0) := by ring
    rw [e, hA]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hAn hB)
  · -- higher coefficients
    simp only [coeff_add, coeff_C, if_neg hi, finsetSum_coeff, coeff_C_mul, coeff_sub, mul_zero,
      sum_const_zero, add_zero, zero_add, zero_sub]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun r hr => ?_
    rw [norm_mul, norm_neg]
    exact mul_le_one₀ (hρT r hr) (norm_nonneg _) (hY i)

end Zeta5