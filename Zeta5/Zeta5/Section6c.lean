import Zeta5.Section6b
import Zeta5.Config69

/-!
# §6 (end): (6.14) and Proposition 6.3

`log_Delta_6_14'` bounds the Andréief integral (6.10) pointwise, using (6.11), the Riemann-sum
estimate (6.12) and the configuration bound (6.9), and then integrates the product majorant
coordinate by coordinate. `prop_6_3'` combines (6.14), (6.15) and (6.4).
-/

open Polynomial Finset MeasureTheory Filter Topology

noncomputable section

namespace Zeta5

namespace S6c

/-- `∑_{k<m} log(k+1) ≤ m log m - m + log m + 1` for `m ≥ 1`. -/
theorem sum_log_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range m, Real.log ((k : ℝ) + 1) ≤ m * Real.log m - m + Real.log m + 1 := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_range_succ]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < m + 1 := by linarith
    have hl := Real.log_le_sub_one_of_pos (div_pos hm0 hm1)
    rw [Real.log_div hm0.ne' hm1.ne'] at hl
    have key : ((m : ℝ) + 1) * (Real.log m - Real.log (m + 1)) ≤ -1 := by
      have : ((m : ℝ) + 1) * (m / (m + 1) - 1) = -1 := by field_simp; ring
      nlinarith
    push_cast
    nlinarith

theorem F_cont {t : ℝ} (ht : 0 < t) : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
  Continuous.log (by fun_prop) (fun u => by positivity)

theorem adj {t κ : ℝ} (ht : 0 < t) (m : ℕ) :
    ∑ k ∈ range m, ∫ u in ((k : ℝ) / κ)..(((k : ℝ) + 1) / κ), Real.log (t + u ^ 2) =
      ∫ u in (0 : ℝ)..(m / κ), Real.log (t + u ^ 2) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun u => Real.log (t + u ^ 2)) (a := fun k : ℕ => (k : ℝ) / κ) (n := m)
    (fun k _ => (F_cont ht).intervalIntegrable _ _)
  simpa using h

theorem adj_log {κ : ℝ} (m : ℕ) :
    ∑ k ∈ range m, ∫ u in ((k : ℝ) / κ)..(((k : ℝ) + 1) / κ), Real.log u =
      ∫ u in (0 : ℝ)..(m / κ), Real.log u := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := Real.log) (a := fun k : ℕ => (k : ℝ) / κ) (n := m)
    (fun k _ => intervalIntegral.intervalIntegrable_log')
  simpa using h

/-- (6.12), lower half: `K ∫₀^{m/K} log(t + u²) du ≤ ∑_{j ≤ m} log(t + (j/K)²)`. -/
theorem sum_ge_int {t κ : ℝ} (ht : 0 < t) (hκ : 0 < κ) (m : ℕ) :
    κ * ∫ u in (0 : ℝ)..(m / κ), Real.log (t + u ^ 2) ≤
      ∑ k ∈ range m, Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) := by
  rw [← adj ht, mul_sum]
  refine sum_le_sum fun k _ => ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hab : (k : ℝ) / κ ≤ ((k : ℝ) + 1) / κ := by gcongr; linarith
  have h := intervalIntegral.integral_mono_on hab ((F_cont ht).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := Real.log (t + (((k : ℝ) + 1) / κ) ^ 2)))
    (fun u hu => by
      have h0 : 0 ≤ u := le_trans (by positivity) hu.1
      exact Real.log_le_log (by positivity) (by nlinarith [hu.2]))
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  have e : κ * (((k : ℝ) + 1) / κ - k / κ) = 1 := by field_simp; ring
  calc κ * ∫ u in ((k : ℝ) / κ)..(((k : ℝ) + 1) / κ), Real.log (t + u ^ 2)
      ≤ κ * ((((k : ℝ) + 1) / κ - k / κ) * Real.log (t + (((k : ℝ) + 1) / κ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h hκ.le
    _ = _ := by rw [← mul_assoc, e, one_mul]

/-- (6.12), upper half: `∑_{j ≤ m} log(t + (j/K)²) ≤ K ∫₀^{m/K} log(t + u²) du + 2 log m + 2`. -/
theorem sum_le_int {t κ : ℝ} (ht : 0 < t) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range m, Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) ≤
      κ * (∫ u in (0 : ℝ)..(m / κ), Real.log (t + u ^ 2)) + 2 * Real.log m + 2 := by
  -- per piece
  have piece : ∀ k : ℕ,
      (((k : ℝ) + 1) / κ - k / κ) * Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) -
          ∫ u in ((k : ℝ) / κ)..(((k : ℝ) + 1) / κ), Real.log (t + u ^ 2) ≤
        (((k : ℝ) + 1) / κ - k / κ) * (2 * Real.log (((k : ℝ) + 1) / κ)) -
          2 * ∫ u in ((k : ℝ) / κ)..(((k : ℝ) + 1) / κ), Real.log u := by
    intro k
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have hab : (k : ℝ) / κ ≤ ((k : ℝ) + 1) / κ := by gcongr; linarith
    set b := ((k : ℝ) + 1) / κ with hb
    have hb0 : 0 < b := by positivity
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hab
      (intervalIntegrable_const.sub ((F_cont ht).intervalIntegrable _ _))
      (intervalIntegrable_const.sub (intervalIntegral.intervalIntegrable_log'.const_mul 2))
      (fun u hu => by
        have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu.1
        have hub : u ≤ b := hu.2.le
        show Real.log (t + b ^ 2) - Real.log (t + u ^ 2) ≤ 2 * Real.log b - 2 * Real.log u
        have hsq : u ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hu0.le hub 2
        have h1 : (t + b ^ 2) * u ^ 2 ≤ b ^ 2 * (t + u ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hsq ht.le]
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h2
        push_cast at h2
        linarith)
    rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((F_cont ht).intervalIntegrable _ _),
      intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_log'.const_mul 2),
      intervalIntegral.integral_const, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul, smul_eq_mul] at h
    exact h
  have hsum := sum_le_sum fun k (_ : k ∈ range m) => piece k
  rw [sum_sub_distrib, sum_sub_distrib, adj ht, ← mul_sum, adj_log, integral_log] at hsum
  have hw : ∀ k : ℕ, ((k : ℝ) + 1) / κ - k / κ = 1 / κ := fun k => by ring
  simp only [hw] at hsum
  rw [← mul_sum, ← mul_sum, ← mul_sum] at hsum
  have hlog : ∀ k : ℕ, Real.log (((k : ℝ) + 1) / κ) = Real.log ((k : ℝ) + 1) - Real.log κ :=
    fun k => Real.log_div (by positivity) hκ.ne'
  simp only [hlog, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.log_div hm0.ne' hκ.ne'] at hsum
  have hL := sum_log_le m hm
  simp only [Real.log_zero, mul_zero, sub_zero, add_zero] at hsum
  have hsum' := mul_le_mul_of_nonneg_left hsum hκ.le
  have e1 : κ * (1 / κ * ∑ k ∈ range m, Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) -
      ∫ u in (0 : ℝ)..(m / κ), Real.log (t + u ^ 2)) =
      ∑ k ∈ range m, Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) -
        κ * ∫ u in (0 : ℝ)..(m / κ), Real.log (t + u ^ 2) := by field_simp
  have e2 : κ * (1 / κ * (2 * (∑ k ∈ range m, Real.log ((k : ℝ) + 1) - m * Real.log κ)) -
      2 * (m / κ * (Real.log m - Real.log κ) - m / κ)) =
      2 * (∑ k ∈ range m, Real.log ((k : ℝ) + 1)) - 2 * m * Real.log m + 2 * m := by
    field_simp; ring
  rw [e1, e2] at hsum'
  linarith

theorem prod_Icc_one (m : ℕ) (f : ℕ → ℝ) : ∏ j ∈ Icc 1 m, f j = ∏ k ∈ range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [prod_Icc_succ_top (by omega), ih, prod_range_succ]

/-- `D_m(y²) = K^{2m} exp(∑_{j ≤ m} log(t + (j/K)²))` with `t = (y/K)²`. -/
theorem aeval_D_exp {κ y : ℝ} (hκ : 0 < κ) (hy : 0 < y) (m : ℕ) :
    aeval (y ^ 2) (D m) = (κ ^ 2) ^ m *
      Real.exp (∑ k ∈ range m, Real.log ((y / κ) ^ 2 + (((k : ℝ) + 1) / κ) ^ 2)) := by
  rw [aeval_D, prod_Icc_one, Real.exp_sum,
    show (κ ^ 2) ^ m = ∏ _k ∈ range m, κ ^ 2 by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [Real.exp_log (by positivity)]
  push_cast
  field_simp

/-- The one-coordinate bound: (6.11) and (6.12) give
`D_N(y²)⁶/D_K(y²) w(y) ≤ 8192 e¹² K^{12N+12}/K^{2K} (1+y)⁵ e^{-K V((y/K)²)}`. -/
theorem g_le (K N : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hN40 : (N : ℝ) / K = 3 / 40)
    {y : ℝ} (hy : 0 < y) :
    aeval (y ^ 2) (D N) ^ 6 / aeval (y ^ 2) (D K) * weight y ≤
      8192 * Real.exp 12 * (K : ℝ) ^ (12 * N + 12) / (K : ℝ) ^ (2 * K) *
        ((1 + y) ^ 5 * Real.exp (-(K : ℝ) * V ((y / K) ^ 2))) := by
  set κ : ℝ := (K : ℝ) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; exact_mod_cast (by omega : 0 < K)
  set t := (y / κ) ^ 2 with ht
  have ht0 : 0 < t := by positivity
  set SN := ∑ k ∈ range N, Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) with hSN
  set SK := ∑ k ∈ range K, Real.log (t + (((k : ℝ) + 1) / κ) ^ 2) with hSK
  set I1 := ∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2) with hI1
  set Ia := ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2) with hIa
  have hlow := sum_ge_int ht0 hκ K
  have hup := sum_le_int ht0 hκ N hN
  rw [div_self hκ.ne'] at hlow
  rw [hN40] at hup
  have hlogN : Real.log N ≤ Real.log κ :=
    Real.log_le_log (by exact_mod_cast hN) (by rw [hκdef]; exact_mod_cast hNK)
  have hsqrt : Real.sqrt t = y / κ := Real.sqrt_sq (by positivity)
  have hVt : κ * V t = 2 * Real.pi * y + κ * I1 - 6 * κ * Ia := by
    simp only [V, hsqrt]
    field_simp
    ring
  have hexp : 6 * SN - SK ≤ -κ * V t + 2 * Real.pi * y + 12 * Real.log κ + 12 := by
    nlinarith
  have hw := weight_le' y hy
  have hw0 := weight_nonneg hy
  have hk12 : Real.exp (12 * Real.log κ) = κ ^ 12 := by
    rw [show (12 : ℝ) * Real.log κ = Real.log (κ ^ 12) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  have h6 : Real.exp (6 * SN - SK) = Real.exp SN ^ 6 / Real.exp SK := by
    rw [Real.exp_sub, show (6 : ℝ) * SN = ((6 : ℕ) : ℝ) * SN by norm_num, Real.exp_nat_mul]
  rw [aeval_D_exp hκ hy, aeval_D_exp hκ hy]
  calc ((κ ^ 2) ^ N * Real.exp SN) ^ 6 / ((κ ^ 2) ^ K * Real.exp SK) * weight y
      = ((κ ^ 2) ^ N) ^ 6 / (κ ^ 2) ^ K * Real.exp (6 * SN - SK) * weight y := by
        rw [h6]; field_simp
    _ ≤ ((κ ^ 2) ^ N) ^ 6 / (κ ^ 2) ^ K *
          Real.exp (-κ * V t + 2 * Real.pi * y + 12 * Real.log κ + 12) *
          (8192 * (1 + y) ^ 5 * Real.exp (-2 * Real.pi * y)) := by
        gcongr
    _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add, hk12]
        have e2 : Real.exp (-2 * Real.pi * y) = (Real.exp (2 * Real.pi * y))⁻¹ := by
          rw [show -2 * Real.pi * y = -(2 * Real.pi * y) by ring, Real.exp_neg]
        have : ((κ ^ 2) ^ N) ^ 6 = κ ^ (12 * N) := by rw [← pow_mul, ← pow_mul]; ring_nf
        rw [this, e2, ← pow_mul, pow_add]
        field_simp

/-- The pointwise bound on the Andréief integrand, via (6.9). -/
theorem pointwise {h : ℕ} {κ c0 E : ℝ} (hκ : 0 < κ) (hc0 : 0 ≤ c0) (W g : ℝ → ℝ)
    (hg : ∀ y, 0 < y → g y ≤ c0 * ((1 + y) ^ 5 * Real.exp (-κ * W ((y / κ) ^ 2))))
    (hg0 : ∀ y, 0 < y → 0 ≤ g y)
    (hconf : ∀ t : Fin h → ℝ, (∀ i, 0 ≤ t i) → Function.Injective t →
      2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), Real.log |t i - t j|
        - κ * ∑ i, W (t i) + ∑ i, Real.sqrt (t i) ≤ E)
    (y : Fin h → ℝ) (hy : ∀ i, 0 < y i) :
    (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) * ∏ i, g (y i) ≤
      (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) * c0 ^ h * Real.exp E *
        ∏ i, ((1 + y i) ^ 5 * Real.exp (-(y i / κ))) := by
  set t : Fin h → ℝ := fun i => (y i / κ) ^ 2 with htdef
  have hyt : ∀ i, (y i) ^ 2 = κ ^ 2 * t i := fun i => by simp only [htdef]; field_simp
  have hR0 : 0 ≤ (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) * c0 ^ h *
      Real.exp E * ∏ i, ((1 + y i) ^ 5 * Real.exp (-(y i / κ))) := by
    have : 0 ≤ ∏ i, ((1 + y i) ^ 5 * Real.exp (-(y i / κ))) :=
      prod_nonneg fun i _ => mul_nonneg (pow_nonneg (by linarith [hy i]) _) (Real.exp_pos _).le
    positivity
  by_cases hinj : Function.Injective t
  · set L : Fin h → Fin h → ℝ := fun i j => Real.log |t i - t j| with hL
    have hV : (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) =
        (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) *
          Real.exp (2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), L i j) := by
      have hfac : ∀ i j, i < j → ((y i) ^ 2 - (y j) ^ 2) ^ 2 = κ ^ 4 * Real.exp (2 * L i j) := by
        intro i j hij
        have hne : t i - t j ≠ 0 := sub_ne_zero.mpr fun e => hij.ne (hinj e)
        have : Real.exp (2 * L i j) = (t i - t j) ^ 2 := by
          rw [two_mul, Real.exp_add, Real.exp_log (abs_pos.mpr hne), ← sq, sq_abs]
        rw [this, hyt, hyt]; ring
      rw [mul_sum, Real.exp_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [mul_sum, Real.exp_sum, ← prod_const, ← prod_mul_distrib]
      exact prod_congr rfl fun j hj => hfac i j (mem_filter.mp hj).2
    have hG : ∏ i, g (y i) ≤ c0 ^ h * (∏ i, (1 + y i) ^ 5) * Real.exp (-κ * ∑ i, W (t i)) := by
      calc ∏ i, g (y i) ≤ ∏ i, (c0 * ((1 + y i) ^ 5 * Real.exp (-κ * W (t i)))) :=
            prod_le_prod₀ (fun i _ => hg0 _ (hy i)) (fun i _ => hg _ (hy i))
        _ = _ := by
            rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
              ← Real.exp_sum, mul_sum]
            simp only [neg_mul]
            ring
    have hc := hconf t (fun i => by positivity) hinj
    have hsq : ∀ i, Real.sqrt (t i) = y i / κ := fun i => Real.sqrt_sq (by have := hy i; positivity)
    simp only [hsq] at hc
    have hexp : Real.exp (2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), L i j) *
        Real.exp (-κ * ∑ i, W (t i)) ≤ Real.exp E * Real.exp (-∑ i, y i / κ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hP0 : 0 ≤ ∏ i, (1 + y i) ^ 5 := prod_nonneg fun i _ => pow_nonneg (by linarith [hy i]) _
    rw [hV]
    calc (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) *
          Real.exp (2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), L i j) * ∏ i, g (y i)
        ≤ (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) *
          Real.exp (2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), L i j) *
            (c0 ^ h * (∏ i, (1 + y i) ^ 5) * Real.exp (-κ * ∑ i, W (t i))) := by gcongr
      _ = (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) * c0 ^ h *
            (∏ i, (1 + y i) ^ 5) * (Real.exp (2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), L i j) *
              Real.exp (-κ * ∑ i, W (t i))) := by ring
      _ ≤ (κ ^ 4) ^ (∑ i : Fin h, (univ.filter (fun j => i < j)).card) * c0 ^ h *
            (∏ i, (1 + y i) ^ 5) * (Real.exp E * Real.exp (-∑ i, y i / κ)) := by gcongr
      _ = _ := by
            rw [prod_mul_distrib, ← Real.exp_sum]
            simp only [sum_neg_distrib]
            ring
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have hz : (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact prod_eq_zero (mem_univ i) (prod_eq_zero (mem_filter.2 ⟨mem_univ j, hlt⟩)
          (by rw [hyt i, hyt j, hij]; ring))
      · exact prod_eq_zero (mem_univ j) (prod_eq_zero (mem_filter.2 ⟨mem_univ i, hlt⟩)
          (by rw [hyt i, hyt j, hij]; ring))
    rw [hz, zero_mul]
    exact hR0

theorem one_add_pow_five_le {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ 5 ≤ 32 * (1 + y ^ 5) := by
  rcases le_total y 1 with h1 | h1
  · calc (1 + y) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ ≤ 32 * (1 + y ^ 5) := by nlinarith [pow_nonneg hy 5]
  · calc (1 + y) ^ 5 ≤ (2 * y) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ = 32 * y ^ 5 := by ring
      _ ≤ 32 * (1 + y ^ 5) := by linarith

/-- `∫₀^∞ (1+y)⁵ e^{-y/K} dy ≤ 3872 K⁶`. -/
theorem phi_bound {κ : ℝ} (hκ : 1 ≤ κ) :
    Integrable (fun y : ℝ => (1 + y) ^ 5 * Real.exp (-(y / κ))) (volume.restrict (Set.Ioi 0)) ∧
      ∫ y in Set.Ioi (0 : ℝ), (1 + y) ^ 5 * Real.exp (-(y / κ)) ≤ 3872 * κ ^ 6 := by
  have hκ0 : 0 < κ := by linarith
  have hint : ∀ a : ℝ, 0 < a →
      IntegrableOn (fun y : ℝ => y ^ (a - 1) * Real.exp (-(1 / κ * y))) (Set.Ioi 0) := by
    intro a ha
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := 1 / κ)
      (by linarith) one_pos (by positivity)
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  set ψ : ℝ → ℝ := fun y => y ^ ((1 : ℝ) - 1) * Real.exp (-(1 / κ * y)) +
    y ^ ((6 : ℝ) - 1) * Real.exp (-(1 / κ * y)) with hψdef
  have hψ : IntegrableOn ψ (Set.Ioi 0) := (hint 1 one_pos).add (hint 6 (by norm_num))
  have g6 : Real.Gamma 6 = 120 := by
    rw [show (6 : ℝ) = (5 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hψval : ∫ y in Set.Ioi (0 : ℝ), ψ y = κ + 120 * κ ^ 6 := by
    rw [hψdef, integral_add (hint 1 one_pos) (hint 6 (by norm_num)),
      Real.integral_rpow_mul_exp_neg_mul_Ioi one_pos (by positivity),
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by positivity), g6, Real.Gamma_one,
      one_div_one_div, Real.rpow_one, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hle : ∀ y ∈ Set.Ioi (0 : ℝ), (1 + y) ^ 5 * Real.exp (-(y / κ)) ≤ 32 * ψ y := by
    intro y hy
    have hy0 : 0 < y := hy
    simp only [hψdef]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero,
      show (6 : ℝ) - 1 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show -(1 / κ * y) = -(y / κ) by ring]
    have := one_add_pow_five_le hy0.le
    have he := (Real.exp_pos (-(y / κ))).le
    nlinarith
  have hcont : Continuous fun y : ℝ => (1 + y) ^ 5 * Real.exp (-(y / κ)) := by fun_prop
  have hI : Integrable (fun y : ℝ => (1 + y) ^ 5 * Real.exp (-(y / κ)))
      (volume.restrict (Set.Ioi 0)) := by
    refine Integrable.mono' (hψ.const_mul 32) hcont.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y hy => ?_
    have hy0 : 0 < y := hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle y hy
  refine ⟨hI, ?_⟩
  calc ∫ y in Set.Ioi (0 : ℝ), (1 + y) ^ 5 * Real.exp (-(y / κ))
      ≤ ∫ y in Set.Ioi (0 : ℝ), 32 * ψ y := by
        refine setIntegral_mono_on hI (hψ.const_mul 32) measurableSet_Ioi hle
    _ = 32 * (κ + 120 * κ ^ 6) := by rw [integral_const_mul, hψval]
    _ ≤ 3872 * κ ^ 6 := by
        have : κ ≤ κ ^ 6 := le_self_pow₀ hκ (by norm_num)
        linarith

theorem pairs (h : ℕ) : (∑ i : Fin h, (univ.filter (fun j => i < j)).card) * 2 = h * (h - 1) := by
  simp_rw [filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i) h, sum_range_reflect (fun i => i) h]
  exact sum_range_id_mul_two h

end S6c

open S6c in
/-- (6.14): `log Δ_K(ζ(5)) ≤ 2h(h + 6N - K) log K + (λM₀ - I(ρ))K² + 18h log K + 160h`. -/
theorem log_Delta_6_14' (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) :
    Real.log (aeval ζ5 (Delta K)) ≤
      2 * hof K * ((hof K : ℝ) + 6 * Nof K - K) * Real.log K +
        (Lim.lam * M0 - logEnergy rho) * (K : ℝ) ^ 2 + 18 * hof K * Real.log K + 160 * hof K := by
  obtain ⟨n, hn⟩ := hK
  have hn1 : 1 ≤ n := by omega
  have hhn : hof K = 37 * n := by unfold hof; omega
  have hNn : Nof K = 3 * n := by unfold Nof; omega
  set h := hof K with hhdef
  set N := Nof K with hNdef
  set κ : ℝ := (K : ℝ) with hκdef
  have hκ1 : 1 ≤ κ := by rw [hκdef]; exact_mod_cast hK0
  have hκ0 : 0 < κ := by linarith
  have hN40 : (N : ℝ) / K = 3 / 40 := by
    rw [hNn, hn]; push_cast
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    field_simp
  set E : ℝ := (Lim.lam * M0 - logEnergy rho) * (K : ℝ) ^ 2 + (120 + Real.sqrt 2) * h +
    2 * h * Real.log K with hEdef
  set c0 : ℝ := 8192 * Real.exp 12 * (K : ℝ) ^ (12 * N + 12) / (K : ℝ) ^ (2 * K) with hc0def
  have hc0 : 0 < c0 := by positivity
  set P : ℕ := ∑ i : Fin h, (univ.filter (fun j => i < j)).card with hPdef
  set g : ℝ → ℝ := fun y => aeval (y ^ 2) (D N) ^ 6 / aeval (y ^ 2) (D K) * weight y with hgdef
  set φ : ℝ → ℝ := fun y => (1 + y) ^ 5 * Real.exp (-(y / κ)) with hφdef
  have hg0 : ∀ y, 0 < y → 0 ≤ g y := by
    intro y hy
    simp only [hgdef]
    rw [aeval_D, aeval_D]
    exact mul_nonneg (div_nonneg (by positivity) (prod_nonneg fun _ _ => by positivity))
      (weight_nonneg hy)
  have hg : ∀ y, 0 < y → g y ≤ c0 * ((1 + y) ^ 5 * Real.exp (-κ * V ((y / κ) ^ 2))) :=
    fun y hy => g_le K N (by omega) (by omega) hN40 hy
  have hpt := pointwise hκ0 hc0.le V g hg hg0
    (fun t ht hinj => config_bound_6_9 K ⟨n, hn⟩ hK0 t ht hinj)
  -- the integral
  set Cst : ℝ := (κ ^ 4) ^ P * c0 ^ h * Real.exp E with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  have hS : {y : Fin h → ℝ | ∀ i, 0 < y i} = Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)) := by
    ext y; simp
  have hSm : MeasurableSet (Set.univ.pi (fun _ : Fin h => Set.Ioi (0 : ℝ))) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hμ : (volume : Measure (Fin h → ℝ)).restrict (Set.univ.pi (fun _ => Set.Ioi (0 : ℝ))) =
      Measure.pi (fun _ => volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  obtain ⟨hφi, hφb⟩ := phi_bound hκ1
  have hprodI : Integrable (fun y : Fin h → ℝ => Cst * ∏ i, φ (y i))
      ((volume : Measure (Fin h → ℝ)).restrict (Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)))) := by
    rw [hμ]
    exact (Integrable.fintype_prod (f := fun _ => φ) (fun _ => hφi)).const_mul Cst
  have hint_le :
      (∫ y in {y : Fin h → ℝ | ∀ i, 0 < y i},
          (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) *
            ∏ i, (aeval ((y i) ^ 2) (D N) ^ 6 / aeval ((y i) ^ 2) (D K) * weight (y i))) ≤
        Cst * (3872 * κ ^ 6) ^ h := by
    rw [hS]
    calc _ ≤ ∫ y in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)), Cst * ∏ i, φ (y i) := by
          refine integral_mono_of_nonneg ?_ hprodI ?_
          · rw [EventuallyLE, ae_restrict_iff' hSm]
            refine Eventually.of_forall fun y hy => ?_
            simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies] at hy
            exact mul_nonneg (prod_nonneg fun _ _ => prod_nonneg fun _ _ => sq_nonneg _)
              (prod_nonneg fun i _ => hg0 _ (hy i))
          · rw [EventuallyLE, ae_restrict_iff' hSm]
            refine Eventually.of_forall fun y hy => ?_
            simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies] at hy
            have := hpt y hy
            simpa [hCst, mul_assoc] using this
      _ = Cst * (∫ y in Set.Ioi (0 : ℝ), φ y) ^ h := by
          rw [hμ, integral_const_mul, integral_fintype_prod_eq_prod (f := fun _ => φ), prod_const,
            card_univ, Fintype.card_fin]
      _ ≤ Cst * (3872 * κ ^ 6) ^ h := by
          gcongr
          exact setIntegral_nonneg measurableSet_Ioi fun y hy => by
            have : (0 : ℝ) < y := hy
            simp only [hφdef]; positivity
  have hΔpos := Delta_zeta5_pos K
  have hΔle : aeval ζ5 (Delta K) ≤ Cst * (3872 * κ ^ 6) ^ h := by
    have hA := andreief_6_10 K ⟨n, hn⟩
    rw [hA] at hΔpos ⊢
    have hI0 := (pos_of_mul_pos_right hΔpos (by positivity)).le
    have hf : 1 / ((hof K).factorial : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    calc _ ≤ 1 * ∫ y in {y : Fin h → ℝ | ∀ i, 0 < y i},
          (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) *
            ∏ i, (aeval ((y i) ^ 2) (D N) ^ 6 / aeval ((y i) ^ 2) (D K) * weight (y i)) :=
          mul_le_mul_of_nonneg_right hf hI0
      _ ≤ _ := by rw [one_mul]; exact hint_le
  have hlog := Real.log_le_log hΔpos hΔle
  have hκne : κ ≠ 0 := hκ0.ne'
  have hc0log : Real.log c0 = Real.log 8192 + 12 + ((12 * N + 12 : ℕ) : ℝ) * Real.log κ -
      ((2 * K : ℕ) : ℝ) * Real.log κ := by
    rw [hc0def, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_exp, Real.log_pow,
      Real.log_pow]
  have hXlog : Real.log ((3872 * κ ^ 6) ^ h) = h * (Real.log 3872 + 6 * Real.log κ) := by
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hClog : Real.log Cst = P * (4 * Real.log κ) + h * Real.log c0 + E := by
    rw [hCst, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow, Real.log_exp, Real.log_pow]; push_cast; ring
  rw [Real.log_mul (by positivity) (by positivity), hClog, hXlog, hc0log] at hlog
  have hP : (P : ℝ) * 2 = h * h - h := by
    have := pairs h
    have h1 : 1 ≤ h := by omega
    rw [← hPdef] at this
    have : ((P * 2 : ℕ) : ℝ) = ((h * (h - 1) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub h1] at this
    linarith
  have h8192 : Real.log 8192 = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]; norm_num
  have h3872 : Real.log 3872 ≤ 12 * Real.log 2 := by
    rw [show (12 : ℝ) * Real.log 2 = Real.log (2 ^ 12) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hs2 : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hh0 : (0 : ℝ) ≤ h := h.cast_nonneg
  have hlk : 0 ≤ Real.log κ := Real.log_nonneg hκ1
  have e1 : (h : ℝ) * Real.log 3872 ≤ h * (12 * Real.log 2) := mul_le_mul_of_nonneg_left h3872 hh0
  have e2 : (h : ℝ) * Real.log 2 ≤ h * 0.6931471808 := mul_le_mul_of_nonneg_left hl2.le hh0
  have e3 : (h : ℝ) * Real.sqrt 2 ≤ h * 1.5 := mul_le_mul_of_nonneg_left hs2.le hh0
  have e4 : (P : ℝ) * (4 * Real.log κ) = (2 * h * h - 2 * h) * Real.log κ := by
    linear_combination (2 * Real.log κ) * hP
  push_cast at hlog
  rw [h8192] at hlog
  simp only [hEdef] at hlog
  nlinarith [e1, e2, e3, e4, hlog]


/-- Proposition 6.3: `0 < F_K(ζ(5))` and `log F_K(ζ(5)) ≤ U K² + 24 K log K + 200 K`. -/
theorem prop_6_3' (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) :
    0 < aeval ζ5 (F K) ∧
      Real.log (aeval ζ5 (F K)) ≤ U * (K : ℝ) ^ 2 + 24 * K * Real.log K + 200 * K := by
  have hS : (0 : ℝ) < (S K : ℝ) := by
    have : (0 : ℚ) < S K := by unfold S; positivity
    exact_mod_cast this
  have hΔ := Delta_zeta5_pos K
  have hF : aeval ζ5 (F K) = (S K : ℝ) * aeval ζ5 (Delta K) := by
    simp [F, aeval_C]
  refine ⟨hF ▸ mul_pos hS hΔ, ?_⟩
  rw [hF, Real.log_mul hS.ne' hΔ.ne']
  have h14 := log_Delta_6_14' K hK hK0
  have h15 := log_S_6_15 K hK hK0
  have h61 := (lemma_6_1).2.2.2
  obtain ⟨n, rfl⟩ := hK
  have hn1 : 1 ≤ n := by omega
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  rw [hh, hN] at h14
  rw [hh] at h15
  simp only [Lim.lam, Lim.α] at h14 h15 h61 ⊢
  push_cast at h14 h15 h61 ⊢
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hlk : 0 ≤ Real.log (40 * (n : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith)
  have hq := mul_le_mul_of_nonneg_right h61 (sq_nonneg (40 * (n : ℝ)))
  nlinarith [mul_nonneg hn0 hlk]


/-- (6.14): `log Δ_K(ζ(5)) ≤ 2h(h + 6N - K) log K + (λM₀ - I(ρ))K² + 18h log K + 160h`. -/
theorem log_Delta_6_14 (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) :
    Real.log (aeval ζ5 (Delta K)) ≤
      2 * hof K * ((hof K : ℝ) + 6 * Nof K - K) * Real.log K +
        (Lim.lam * M0 - logEnergy rho) * (K : ℝ) ^ 2 + 18 * hof K * Real.log K + 160 * hof K := by
  exact log_Delta_6_14' K hK hK0

/-- Proposition 6.3: `0 < F_K(ζ(5))` and `log F_K(ζ(5)) ≤ U K² + 24 K log K + 200 K`. -/
theorem prop_6_3 (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) :
    0 < aeval ζ5 (F K) ∧
      Real.log (aeval ζ5 (F K)) ≤ U * (K : ℝ) ^ 2 + 24 * K * Real.log K + 200 * K := by
  exact prop_6_3' K hK hK0

end Zeta5
