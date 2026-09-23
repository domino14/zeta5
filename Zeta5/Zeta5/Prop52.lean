import Zeta5.Section5Final
import Zeta5.RCont
import Zeta5.PrimeSums

/-!
# Proposition 5.2 and (5.21)

The PNT-dependent prime sums and the continuity of the limiting functions are used through the
interface lemmas below.
-/

open Polynomial Finset MeasureTheory Filter Topology

noncomputable section

namespace Zeta5


namespace P52

/-- The inner prime-sum bound in the form used below (`x = K/p ∈ [3, M)`). -/
theorem inner_sum_le (M : ℕ) (hM3 : (3 : ℝ) < M) (f : ℝ → ℝ)
    (hfb : ∃ B, ∀ x ∈ Set.Icc (3 : ℝ) M, |f x| ≤ B)
    (hfc : ∃ D : Set ℝ, D.Countable ∧ ∀ x : ℝ, 0 < x → x ∉ D → ContinuousAt f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      (∑ p ∈ (range (K + 1)).filter (fun p : ℕ => p.Prime ∧ (K : ℝ) < p * (M : ℝ) ∧ (p : ℝ) * 3 ≤ K),
        (p : ℝ) * f (K / p) * Real.log p) / (K : ℝ) ^ 2 ≤ (∫ x in (3 : ℝ)..M, f x / x ^ 3) + ε := by
  obtain ⟨B, hB⟩ := hfb
  obtain ⟨D, hD, hc⟩ := hfc
  have hM : 3 < M := by exact_mod_cast hM3
  filter_upwards [inner_prime_sum_limsup M hM f B hB D hD
    (fun x hx hxD => hc x (by linarith [hx.1]) hxD) ε hε, eventually_gt_atTop 0] with K hK hK0
  have hKr : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hKr]
  convert hK using 2
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by exact_mod_cast h3, by exact_mod_cast (by linarith : (3 * p : ℝ) ≤ K)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, by exact_mod_cast h3, ?_⟩
    have : ((3 * p : ℕ) : ℝ) ≤ K := by exact_mod_cast h4
    push_cast at this; linarith

/-- The outer prime-sum bound in the form used below (`y = p/K ∈ (a, b]`). -/
theorem outer_sum_le (a b : ℝ) (ha : 0 < a) (hab : a < b) (φ : ℝ → ℝ)
    (hφb : ∃ B, ∀ y ∈ Set.Icc a b, |φ y| ≤ B)
    (hφc : ∃ D : Set ℝ, D.Countable ∧ ∀ y : ℝ, 0 < y → y ∉ D → ContinuousAt φ y)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      (∑ p ∈ (range (⌊b * K⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ a * K < p),
        φ (p / K) * Real.log p) / K ≤ (∫ y in a..b, φ y) + ε := by
  obtain ⟨B, hB⟩ := hφb
  obtain ⟨D, hD, hc⟩ := hφc
  filter_upwards [outer_prime_sum_limsup a b ha hab.le φ B hB D hD
    (fun y hy hyD => hc y (by linarith [hy.1]) hyD) ε hε, eventually_gt_atTop 0] with K hK hK0
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  rw [div_le_iff₀ hKr]
  convert hK using 2
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hb : 0 ≤ b * K := by have := ha.trans hab; positivity
    exact (Nat.le_floor_iff hb).mp (by omega)
  · rintro ⟨h1, h2, h3, -⟩
    exact ⟨h1, h2, h3⟩

end P52


namespace P52

/-- Chebyshev's bound `θ(N) ≤ N log 4`, from `N# ≤ 4^N`. -/
theorem sum_log_primes_le (N : ℕ) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p ≤ N * Real.log 4 := by
  have h := primorial_le_four_pow N
  have hpos : (0 : ℝ) < (primorial N : ℝ) := by exact_mod_cast primorial_pos N
  have hlog : Real.log (primorial N : ℝ) ≤ Real.log ((4 : ℝ) ^ N) :=
    Real.log_le_log hpos (by exact_mod_cast h)
  rw [Real.log_pow] at hlog
  unfold primorial at hlog
  rw [Nat.cast_prod, Real.log_prod] at hlog
  · exact hlog
  · intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero

theorem log_mKM (K M : ℕ) :
    Real.log (mKM K M : ℝ) =
      ∑ p ∈ (range (2 * hof K + 1)).filter Nat.Prime, (-(Lp K M p : ℝ)) * Real.log p := by
  unfold mKM
  push_cast
  rw [Real.log_prod]
  · refine sum_congr rfl fun p hp => ?_
    rw [Real.log_zpow]; push_cast; ring
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

theorem hof_real {K : ℕ} (hK : 40 ∣ K) : (hof K : ℝ) = Lim.lam * K := by
  obtain ⟨n, rfl⟩ := hK
  have : hof (40 * n) = 37 * n := by unfold hof; omega
  rw [this, Lim.lam]; push_cast; ring


/-- For `K < p ≤ 2h`: `-v_p(S_K) ≤ K · outerIntegrand(p/K)`. -/
theorem vpS_large {K p : ℕ} [hp : Fact p.Prime] (hK : 40 ∣ K) (hK40 : 40 ≤ K) (hKp : K < p)
    (hp2h : p ≤ 2 * hof K) :
    -(vpS K p : ℝ) ≤ K * Lim.outerIntegrand (p / K) := by
  have hK0 : 0 < K := by omega
  have hleg := vpS_legendre' K p hK hK0
  simp only at hleg
  have hhK : hof K ≤ K := by unfold hof; omega
  have hp2 : K < p ^ 2 := by nlinarith
  have hp2' : 2 * hof K < p ^ 2 := by nlinarith
  rw [sum_div_pow_single K _ (by omega) hp2,
    sum_div_pow_single (Nof K) _ (by omega) (by unfold Nof; omega),
    sum_congr rfl (fun i hi => sum_div_pow_single (2 * i) _ (by omega) (by
      rw [mem_Icc] at hi; omega))] at hleg
  have h4' : padicValNat p 4 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have : p ∣ 2 := hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hd)
    have := Nat.le_of_dvd (by norm_num) this; omega
  rw [h4', Nat.div_eq_of_lt hKp, Nat.div_eq_of_lt (show Nof K < p by unfold Nof; omega),
    sum_floor_eq (h := hof K) (by omega)] at hleg
  have hv : -(vpS K p : ℝ) = ∑ j ∈ Icc 1 5, 2 * ((hof K - (j * p + 1) / 2 : ℕ) : ℝ) := by
    rw [hleg]; push_cast; rw [mul_sum]; ring
  rw [hv]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK0
  have hy1 : (1 : ℝ) < (p : ℝ) / K := by
    rw [one_lt_div hK']; exact_mod_cast hKp
  have hR0 : Lim.R0 ((p : ℝ) / K) = 0 := by
    unfold Lim.R0; rw [if_neg (by intro h; linarith [h.2]), if_neg (by intro h; linarith [h.2])]
  have hd : Lim.dfun ((p : ℝ) / K) = 0 := by
    unfold Lim.dfun; rw [if_neg (by intro h; linarith [h.2])]
  have hfl : ⌊1 / ((p : ℝ) / K)⌋ = 0 := by
    rw [Int.floor_eq_iff]; constructor
    · push_cast; positivity
    · push_cast; rw [zero_add, div_lt_one (by positivity)]; exact hy1
  rw [Lim.outerIntegrand, hR0, hd, hfl]
  simp only [Int.cast_zero, mul_zero, sub_zero, zero_add]
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  have hh := hof_real hK
  have hpos : K * (2 * Lim.lam - (j : ℝ) * ((p : ℝ) / K)) = 2 * hof K - j * p := by
    rw [hh]; field_simp
  unfold Lim.pos
  rw [mul_max_of_nonneg _ _ hK'.le, hpos, mul_zero]
  generalize hm : j * p = m
  have hmr : (j : ℝ) * p = m := by rw [← hm]; push_cast; ring
  rw [hmr]
  rcases (by omega : 2 * (hof K - (m + 1) / 2) + m ≤ 2 * hof K ∨ hof K - (m + 1) / 2 = 0) with h | h
  · refine le_max_of_le_left ?_
    have : ((2 * (hof K - (m + 1) / 2) + m : ℕ) : ℝ) ≤ (2 * hof K : ℕ) := by exact_mod_cast h
    push_cast at this; linarith
  · rw [h]; simp

/-- The main term of `-L_p(K, M)`. -/
def mainCoef (K M p : ℕ) : ℝ :=
  if p * M ≤ K then ((6 * hof K * Nat.log p (5 * K) + hof K * padicValNat p 24 : ℕ) : ℝ)
  else if 3 * p ≤ K then (p : ℝ) * Lim.R ((K : ℝ) / p)
  else (K : ℝ) * Lim.outerIntegrand ((p : ℝ) / K)

theorem neg_Lp_le (M : ℕ) (hM : 40 ≤ M) {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hin : ∀ K p : ℕ, [Fact p.Prime] → InnerHyp K M p →
      |(gammaIn K M p : ℝ) - p * Lim.Gam ((K : ℝ) / p)| ≤ C1 ∧
      |(vpS K p : ℝ) - p * Lim.Nfun ((K : ℝ) / p)| ≤ C1)
    (hout : ∀ K p : ℕ, [Fact p.Prime] → 40 ∣ K → OuterHyp K p →
      |-(gammaOut K p : ℝ) - K * (Lim.R0 ((p : ℝ) / K) - Lim.dfun ((p : ℝ) / K))| ≤ C2 ∧
      |-(vpS K p : ℝ) - K * (-2 * Lim.lam * ⌊(K : ℝ) / p⌋ +
          ∑ j ∈ Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K)))| ≤ C2)
    {K p : ℕ} (hK : 40 ∣ K) (hKM : 200 * M ^ 2 ≤ K) (hK0 : 0 < K) (hpp : p.Prime)
    (hp2h : p ≤ 2 * hof K) :
    -(Lp K M p : ℝ) ≤ mainCoef K M p + (2 * C1 + 1 + 2 * C2) := by
  have := Fact.mk hpp
  have hM2 : 40 * 40 ≤ M ^ 2 := by nlinarith
  have hK60 : 60 ≤ K := by nlinarith
  unfold mainCoef Lp
  by_cases hs : p * M ≤ K
  · rw [if_pos hs, if_pos hs]
    simp only [Int.cast_neg, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_add,
      Nat.cast_mul, Int.cast_ofNat, Nat.cast_ofNat]
    linarith
  rw [if_neg hs, if_neg hs]
  by_cases hi : 3 * p ≤ K
  · rw [if_pos hi, if_pos hi]
    have hIH : InnerHyp K M p := ⟨hM, hK, hK0, by nlinarith, by omega, hi⟩
    obtain ⟨h1, h2⟩ := hin K p hIH
    have hfl : (gammaIn K M p : ℝ) - 1 ≤ ((⌊gammaIn K M p⌋ : ℤ) : ℝ) := by
      have := (Int.sub_one_lt_floor (gammaIn K M p)).le
      exact_mod_cast this
    rw [abs_le] at h1 h2
    push_cast
    unfold Lim.R
    nlinarith
  rw [if_neg hi, if_neg hi]
  by_cases hpK : p ≤ K
  · rw [if_pos hpK]
    have hOH : OuterHyp K p := by
      refine ⟨by omega, hpK, by omega, by nlinarith, by unfold Nof; omega, by unfold Nof; omega⟩
    obtain ⟨h1, h2⟩ := hout K p hK hOH
    rw [abs_le] at h1 h2
    have hfl : ⌊1 / ((p : ℝ) / K)⌋ = ⌊(K : ℝ) / p⌋ := by rw [one_div_div]
    unfold Lim.outerIntegrand
    rw [hfl]
    push_cast
    nlinarith
  · rw [if_neg hpK]
    have := vpS_large hK (by omega) (by omega) hp2h
    linarith

theorem R_bounded (M : ℕ) : ∃ B, ∀ x ∈ Set.Icc (3 : ℝ) M, |Lim.R x| ≤ B := by
  refine ⟨18 * M + 2, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := R_decomp_bound x hx.1
  have f1 := Int.fract_nonneg x
  have f2 := (Int.fract_lt_one x).le
  have g1 := Int.fract_nonneg (Lim.α * x)
  have g2 := (Int.fract_lt_one (Lim.α * x)).le
  have hx3 := hx.1
  have hxM := hx.2
  simp only [Lim.lam] at h1 h2
  rw [abs_le]; constructor <;> nlinarith

theorem sum_log_P_le {K : ℕ} (hK0 : 0 < K) :
    ∑ p ∈ (range (2 * hof K + 1)).filter Nat.Prime, Real.log p ≤ 2 * K * Real.log 4 := by
  refine (sum_log_primes_le _).trans ?_
  have : hof K ≤ K := by unfold hof; omega
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have : ((2 * hof K : ℕ) : ℝ) ≤ 2 * K := by exact_mod_cast (by omega : 2 * hof K ≤ 2 * K)
  nlinarith

end P52

open P52 in
/-- Proposition 5.2. -/
theorem prop_5_2' (M : ℕ) (hM : 40 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (mKM (40 * n) M) / ((40 * n : ℕ) : ℝ) ^ 2 ≤
        Iout + 6 * Lim.lam / M + (∫ x in (3 : ℝ)..M, Lim.R x / x ^ 3) + ε := by
  obtain ⟨C1', hC1'⟩ := uniformity_5_7 M hM
  obtain ⟨C2', hC2'⟩ := uniformity_outer
  have hin : ∀ K p : ℕ, [Fact p.Prime] → InnerHyp K M p →
      |(gammaIn K M p : ℝ) - p * Lim.Gam ((K : ℝ) / p)| ≤ max C1' 0 ∧
      |(vpS K p : ℝ) - p * Lim.Nfun ((K : ℝ) / p)| ≤ max C1' 0 := fun K p _ h =>
    ⟨(hC1' K p h).1.trans (le_max_left _ _), (hC1' K p h).2.trans (le_max_left _ _)⟩
  have hout : ∀ K p : ℕ, [Fact p.Prime] → 40 ∣ K → OuterHyp K p →
      |-(gammaOut K p : ℝ) - K * (Lim.R0 ((p : ℝ) / K) - Lim.dfun ((p : ℝ) / K))| ≤ max C2' 0 ∧
      |-(vpS K p : ℝ) - K * (-2 * Lim.lam * ⌊(K : ℝ) / p⌋ +
          ∑ j ∈ Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K)))| ≤ max C2' 0 :=
    fun K p _ hK h =>
      ⟨(hC2' K p hK h).1.trans (le_max_left _ _), (hC2' K p hK h).2.trans (le_max_left _ _)⟩
  set C := 2 * max C1' 0 + 1 + 2 * max C2' 0 with hCdef
  have hC : 0 ≤ C := by positivity
  have hε4 : 0 < ε / 4 := by positivity
  have hM3 : (3 : ℝ) < M := by
    have : (40 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have E1 := small_prime_sum_bound M (by omega) (ε / 4) hε4
  have E2 := inner_sum_le M hM3 Lim.R (R_bounded M) R_continuousAt_off (ε / 4) hε4
  have E3 := outer_sum_le (1 / 3) (2 * Lim.lam) (by norm_num)
    (by norm_num [Lim.lam]) Lim.outerIntegrand outerIntegrand_bounded
    outerIntegrand_continuousAt_off (ε / 4) hε4
  rw [integral_5_10] at E3
  have E4 : ∀ᶠ K : ℕ in atTop, 200 * M ^ 2 ≤ K ∧
      C * (2 * K * Real.log 4) ≤ ε / 4 * (K : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop (200 * M ^ 2),
      eventually_ge_atTop (⌈8 * C * Real.log 4 / ε⌉₊)] with K hK1 hK2
    refine ⟨hK1, ?_⟩
    have h1 : 8 * C * Real.log 4 / ε ≤ K :=
      (Nat.le_ceil _).trans (by exact_mod_cast hK2)
    rw [div_le_iff₀ hε] at h1
    have hK0 : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hT : Tendsto (fun n : ℕ => 40 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by show n ≤ 40 * n; omega) tendsto_id
  filter_upwards [hT.eventually (E1.and (E2.and (E3.and E4))), eventually_gt_atTop 0]
    with n ⟨h1, h2, h3, hKM, h4⟩ hn
  have hK : 40 ∣ 40 * n := dvd_mul_right _ _
  set K := 40 * n with hKdef
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  set P := (range (2 * hof K + 1)).filter Nat.Prime with hP
  -- termwise bound
  have hterm : Real.log (mKM K M : ℝ) ≤
      ∑ p ∈ P, mainCoef K M p * Real.log p + C * ∑ p ∈ P, Real.log p := by
    rw [log_mKM, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpr, hpp⟩ := mem_filter.mp hp
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have := neg_Lp_le M hM (le_max_right C1' 0) (le_max_right C2' 0) hin hout hK hKM hK0 hpp
      (by rw [mem_range] at hpr; omega)
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right this hlog
  -- split the main sum
  have hsplit : ∑ p ∈ P, mainCoef K M p * Real.log p =
      ∑ p ∈ (range (K + 1)).filter (fun p => p.Prime ∧ p * M ≤ K),
        ((6 * hof K * Nat.log p (5 * K) + hof K * padicValNat p 24 : ℕ) : ℝ) * Real.log p +
      ∑ p ∈ (range (K + 1)).filter
          (fun p : ℕ => p.Prime ∧ (K : ℝ) < p * (M : ℝ) ∧ (p : ℝ) * 3 ≤ K),
        (p : ℝ) * Lim.R (K / p) * Real.log p +
      K * ∑ p ∈ (range (⌊2 * Lim.lam * K⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ 1 / 3 * (K : ℝ) < p),
        Lim.outerIntegrand (p / K) * Real.log p := by
    unfold mainCoef
    simp only [ite_mul]
    rw [sum_ite, sum_ite, mul_sum, ← add_assoc]
    simp only [filter_filter]
    have hfl : ⌊2 * Lim.lam * K⌋₊ = 2 * hof K := by
      have hh := hof_real hK
      rw [show 2 * Lim.lam * (K : ℝ) = ((2 * hof K : ℕ) : ℝ) by
        rw [show ((2 * hof K : ℕ) : ℝ) = 2 * (hof K : ℝ) by push_cast; ring, hh]; ring]
      exact Nat.floor_natCast _
    have hhK : K ≤ 2 * hof K := by unfold hof; omega
    rw [hfl]
    congr 1
    congr 1
    · refine sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [hP, mem_filter, mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨by nlinarith, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨by omega, h2⟩, h3⟩
    · refine sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [hP, mem_filter, mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨by omega, h2, ?_, by exact_mod_cast (by omega : p * 3 ≤ K)⟩
        exact_mod_cast (by omega : K < p * M)
      · rintro ⟨h1, h2, h3, h4⟩
        have h3' : K < p * M := by exact_mod_cast h3
        have h4' : p * 3 ≤ K := by exact_mod_cast h4
        exact ⟨⟨by omega, h2⟩, by omega, by omega⟩
    · refine sum_congr ?_ fun p _ => by ring
      ext p
      simp only [hP, mem_filter, mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨h1, h2, ?_⟩
        have : K < 3 * p := by omega
        have : (K : ℝ) < 3 * p := by exact_mod_cast this
        linarith
      · rintro ⟨h1, h2, h3⟩
        have : (K : ℝ) < 3 * p := by linarith
        have h3' : K < 3 * p := by exact_mod_cast this
        refine ⟨⟨h1, h2⟩, ?_, by omega⟩
        intro h
        have : 3 * p ≤ p * M := by nlinarith
        omega
  rw [hsplit] at hterm
  have hlogP := sum_log_P_le hK0
  rw [div_le_iff₀ (by positivity)] at h2 h3 ⊢
  have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
  have h3' := mul_le_mul_of_nonneg_left h3 hKr.le
  have h5 : C * ∑ p ∈ P, Real.log p ≤ C * (2 * K * Real.log 4) :=
    mul_le_mul_of_nonneg_left hlogP hC
  have hM0 : (0 : ℝ) < M := by linarith
  linear_combination hterm + h1 + h2 + h3' + h5 + h4

/-- (5.21). -/
theorem limsup_5_21' (M : ℕ) (hM : 40 ≤ M) (hM40 : 40 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (mKM (40 * n) M) / ((40 * n : ℕ) : ℝ) ^ 2 ≤ AM M + ε := by
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hint := R_integrableOn
  have hsub : ∀ a b : ℝ, 3 ≤ a → a ≤ b →
      IntervalIntegrable (fun x => Lim.R x / x ^ 3) volume a b := fun a b ha hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hint.mono_set fun x hx => le_trans ha hx.1.le)
  have hsplit : (∫ x in (3 : ℝ)..M, Lim.R x / x ^ 3) =
      (∫ x in (3 : ℝ)..20, Lim.R x / x ^ 3) +
        ((∫ x in Set.Ioi (20 : ℝ), Lim.R x / x ^ 3) - ∫ x in Set.Ioi (M : ℝ), Lim.R x / x ^ 3) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hsub 3 20 le_rfl (by norm_num))
      (hsub 20 M (by norm_num) (by linarith)), intervalIntegral.integral_of_le (show (20 : ℝ) ≤ M by linarith),
      ← Set.Ioc_union_Ioi_eq_Ioi (show (20 : ℝ) ≤ M by linarith),
      setIntegral_union (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi
        (hint.mono_set (show Set.Ioc (20 : ℝ) M ⊆ Set.Ici 3 from fun x hx => by
          simp only [Set.mem_Ioc] at hx; simp only [Set.mem_Ici]; linarith))
        (hint.mono_set (show Set.Ioi (M : ℝ) ⊆ Set.Ici 3 from fun x hx => by
          simp only [Set.mem_Ioi] at hx; simp only [Set.mem_Ici]; linarith))]
    ring
  have h16 := tail_5_16
  have h17 := tail_5_17 M hM40 (by omega)
  have hI : (Iout : ℝ) + 6 * Lim.lam / M + (∫ x in (3 : ℝ)..M, Lim.R x / x ^ 3) ≤ (AM M : ℝ) := by
    rw [hsplit, integral_5_18]
    simp only [AM, Astar, Iout, lam, Lim.lam] at h17 ⊢
    push_cast
    linear_combination h16 + h17
  filter_upwards [prop_5_2' M hM ε hε] with n hn
  linarith


/-- Proposition 5.2 (with `K = 40n`):
`limsup K⁻² log m_{K,M} ≤ I_out + 6λ/M + ∫₃^M R(x)/x³ dx`. -/
theorem prop_5_2 (M : ℕ) (hM : 40 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (mKM (40 * n) M) / ((40 * n : ℕ) : ℝ) ^ 2 ≤
        Iout + 6 * Lim.lam / M + (∫ x in (3 : ℝ)..M, Lim.R x / x ^ 3) + ε := by
  exact prop_5_2' M hM ε hε

/-- (5.21): `limsup K⁻² log m_{K,M} ≤ A_M` for `M ∈ 40ℤ`, `M ≥ 40`. -/
theorem limsup_5_21 (M : ℕ) (hM : 40 ≤ M) (hM40 : 40 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (mKM (40 * n) M) / ((40 * n : ℕ) : ℝ) ^ 2 ≤ AM M + ε := by
  exact limsup_5_21' M hM hM40 ε hε

end Zeta5
