import Zeta5.Section5
import Zeta5.OuterCount

/-!
# §5: Legendre's formula (5.3) and the outer-range uniformity

`vpS_legendre'` is (5.3). As stated in `Section5.lean` without `0 < K` it fails at `K = 0`,
`p = 2` (see `vpS_legendre_false_zero`): there `S_0 = 1`, but the right side is
`(0 - 1)·v₂(4) = -2`, because `hof K - 1` is elaborated in `ℤ`. So we add `0 < K`.
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValNat_factorial_Icc (n B : ℕ) (hn : n ≤ B) :
    padicValNat p n.factorial = ∑ a ∈ Icc 1 B, n / p ^ a := by
  have hlog : Nat.log p n < B + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · refine Nat.log_lt_of_lt_pow hn0.ne' ?_
      calc n < p ^ n := Nat.lt_pow_self hp.out.one_lt
        _ ≤ p ^ (B + 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
  rw [padicValNat_factorial hlog]
  congr 1

/-- **(5.3)**, Legendre's formula for `v_p(S_K)` (for `K > 0`). -/
theorem vpS_legendre' (K p : ℕ) [Fact p.Prime] (hK : 40 ∣ K) (hK0 : 0 < K) :
    let B := 2 * hof K + K + 1
    vpS K p = 2 * hof K * ∑ a ∈ Icc 1 B, (K / p ^ a : ℕ)
      - 12 * hof K * ∑ a ∈ Icc 1 B, (Nof K / p ^ a : ℕ)
      - 2 * ∑ i ∈ Icc 1 (hof K - 1), ∑ a ∈ Icc 1 B, (2 * i / p ^ a : ℕ)
      + (hof K - 1) * padicValNat p 4 := by
  intro B
  have hh : 1 ≤ hof K := by unfold hof; omega
  set A : ℕ := K.factorial ^ (2 * hof K) * 4 ^ (hof K - 1) with hA
  set Bd : ℕ := (Nof K).factorial ^ (12 * hof K) *
    ∏ i ∈ Icc 1 (hof K - 1), (2 * i).factorial ^ 2 with hBd
  have hS : S K = (A : ℚ) / Bd := by unfold S; simp only [hA, hBd]; push_cast; ring
  have hA0 : A ≠ 0 := by positivity
  have hB0 : Bd ≠ 0 := by positivity
  have hvA : padicValNat p A = 2 * hof K * ∑ a ∈ Icc 1 B, K / p ^ a +
      (hof K - 1) * padicValNat p 4 := by
    rw [hA, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ _,
      padicValNat.pow _ _, padicValNat_factorial_Icc K B (by omega)]
  have hvB : padicValNat p Bd = 12 * hof K * ∑ a ∈ Icc 1 B, Nof K / p ^ a +
      2 * ∑ i ∈ Icc 1 (hof K - 1), ∑ a ∈ Icc 1 B, 2 * i / p ^ a := by
    rw [hBd, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ _,
      padicValNat_factorial_Icc (Nof K) B (by unfold Nof; omega)]
    congr 1
    have : ∀ s : Finset ℕ, (∀ i ∈ s, 2 * i ≤ B) → padicValNat p (∏ i ∈ s, (2 * i).factorial ^ 2) =
        2 * ∑ i ∈ s, ∑ a ∈ Icc 1 B, 2 * i / p ^ a := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | insert b s hb ih =>
        rw [prod_insert hb, sum_insert hb, padicValNat.mul (by positivity) (by positivity),
          padicValNat.pow _ _, padicValNat_factorial_Icc _ B (hs b (mem_insert_self b s)),
          ih fun i hi => hs i (mem_insert_of_mem hi)]
        ring
    exact this _ fun i hi => by rw [mem_Icc] at hi; omega
  show padicValRat p (S K) = _
  rw [hS, padicValRat.div (by exact_mod_cast hA0) (by exact_mod_cast hB0), padicValRat.of_nat,
    padicValRat.of_nat, hvA, hvB]
  push_cast [Nat.cast_sub hh]
  ring

/-- The statement of `vpS_legendre` fails at `K = 0`, `p = 2`. -/
theorem vpS_legendre_false_zero :
    ¬ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let B := 2 * hof 0 + 0 + 1
      vpS 0 2 = 2 * hof 0 * ∑ a ∈ Icc 1 B, (0 / 2 ^ a : ℕ)
        - 12 * hof 0 * ∑ a ∈ Icc 1 B, (Nof 0 / 2 ^ a : ℕ)
        - 2 * ∑ i ∈ Icc 1 (hof 0 - 1), ∑ a ∈ Icc 1 B, (2 * i / 2 ^ a : ℕ)
        + (hof 0 - 1) * padicValNat 2 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  simp only [hof, Nof, vpS, S] at h
  norm_num at h

/-! ## The outer range: `v_p(S_K)` -/

theorem sum_div_pow_single (n B : ℕ) (hB : 1 ≤ B) (hn : n < p ^ 2) :
    ∑ a ∈ Icc 1 B, n / p ^ a = n / p := by
  rw [sum_eq_single 1]
  · simp
  · intro a ha ha1
    rw [mem_Icc] at ha
    apply Nat.div_eq_of_lt
    calc n < p ^ 2 := hn
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.out.pos (by omega)
  · intro h; exact absurd (mem_Icc.mpr ⟨le_rfl, hB⟩) h

theorem vpS_outer {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) :
    vpS K p = 2 * hof K * (K / p : ℕ) - 2 * ∑ i ∈ Icc 1 (hof K - 1), (2 * i / p : ℕ) := by
  obtain ⟨h7, h2, h3, h4, h5, h6⟩ := h
  have hK0 : 0 < K := by omega
  have hleg := vpS_legendre' K p hK hK0
  simp only at hleg
  have hKp : K < p ^ 2 := by omega
  rw [hleg, sum_div_pow_single K _ (by omega) hKp,
    sum_div_pow_single (Nof K) _ (by omega) (by unfold Nof at *; nlinarith),
    sum_congr rfl (fun i hi => sum_div_pow_single (2 * i) _ (by omega) (by
      rw [mem_Icc] at hi; unfold hof at hi; omega))]
  have h4' : padicValNat p 4 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have : p ∣ 2 := hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hd)
    have := Nat.le_of_dvd (by norm_num) this; omega
  rw [h4', Nat.div_eq_of_lt (show Nof K < p by omega)]
  push_cast; ring

/-- `∑_{i=1}^{h-1} ⌊2i/p⌋ = ∑_{j=1}^{5} (h - ⌈jp/2⌉)₊` when `2h < 6p`. -/
theorem sum_floor_eq {h : ℕ} (hh : 2 * h < 6 * p) :
    ∑ i ∈ Icc 1 (h - 1), 2 * i / p = ∑ j ∈ Icc 1 5, (h - (j * p + 1) / 2) := by
  have hp0 := hp.out.pos
  have h1 : ∀ i ∈ Icc 1 (h - 1), 2 * i / p =
      ((Icc 1 5).filter fun j => j * p ≤ 2 * i).card := by
    intro i hi
    rw [mem_Icc] at hi
    have hq : 2 * i / p ≤ 5 := by
      rw [Nat.div_le_iff_le_mul_add_pred hp0]; omega
    have : (Icc 1 5).filter (fun j => j * p ≤ 2 * i) = Icc 1 (2 * i / p) := by
      ext j; simp only [mem_filter, mem_Icc]
      rw [← Nat.le_div_iff_mul_le hp0]; omega
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  rw [sum_congr rfl h1]
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← card_filter]
  rw [mem_Icc] at hj
  have hjp : 1 ≤ j * p := Nat.mul_pos (by omega) hp0
  have : (Icc 1 (h - 1)).filter (fun i => j * p ≤ 2 * i) = Icc ((j * p + 1) / 2) (h - 1) := by
    ext i; simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; omega
    · rintro ⟨h1, h2⟩
      omega
  rw [this, Nat.card_Icc]; omega

/-! ## The outer range: `γ_out` -/

/-- The integer `K (R₀(p/K) - d(p/K))`. -/
def Eout (K p : ℕ) : ℤ :=
  let N : ℤ := Nof K
  if K < 2 * p then
    7 * (K - p) - 6 * min N (K - p) - 6 * max (K + N - 2 * p) 0 + max (K + 4 * N - 2 * p) 0
  else
    8 * K - 9 * p - 8 * N - 5 * min N (K - 2 * p) - 5 * max (K + N - 3 * p) 0
      - max (K + 4 * N - 3 * p - max (K + N - 3 * p) 0) 0

theorem gammaOut_sub_Eout {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) :
    |-gammaOut K p - Eout K p| ≤ 7 := by
  obtain ⟨h7, h2, h3, h4, h5, h6⟩ := h
  have hp0 := hp.out.pos
  have h2p : ¬ 2 ∣ p := fun hd => by
    have := hp.out.eq_one_or_self_of_dvd 2 hd; omega
  have hmod := Nat.mod_add_div K p
  simp only [gammaOut, rOut, Eout]
  unfold Nof at *
  split_ifs with hc
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)] at hmod
    rw [abs_le]; push_cast; constructor <;> omega
  · rw [Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)] at hmod
    rw [abs_le]; push_cast; constructor <;> omega



theorem K_mul_R0_sub_dfun {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) :
    (K : ℝ) * (Lim.R0 ((p : ℝ) / K) - Lim.dfun ((p : ℝ) / K)) = Eout K p := by
  obtain ⟨h7, h2, h3, h4, h5, h6⟩ := h
  have h2p : ¬ 2 ∣ p := fun hd => by
    have := hp.out.eq_one_or_self_of_dvd 2 hd; omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hN : ((Nof K : ℕ) : ℝ) = K * Lim.α := by
    obtain ⟨m, rfl⟩ := hK
    simp only [Nof, Lim.α]
    rw [show 3 * (40 * m) / 40 = 3 * m by omega]; push_cast; ring
  have hKy : (K : ℝ) * ((p : ℝ) / K) = p := by field_simp
  generalize (p : ℝ) / K = y at hKy ⊢
  have hmin : ∀ a b : ℝ, (K : ℝ) * min a b = min (K * a) (K * b) :=
    fun a b => mul_min_of_nonneg _ _ hK0.le
  have hpos : ∀ a : ℝ, (K : ℝ) * Lim.pos a = max (K * a) 0 := fun a => by
    simp only [Lim.pos]; rw [mul_max_of_nonneg _ _ hK0.le, mul_zero]
  have hpK : (p : ℝ) < K := by exact_mod_cast (show p < K by omega)
  have hK3 : (K : ℝ) < 3 * p := by exact_mod_cast h3
  simp only [Eout]
  split_ifs with hc
  · have hc' : (K : ℝ) < 2 * p := by exact_mod_cast hc
    have hy1 : 1 / 2 < y ∧ y < 1 := by constructor <;> nlinarith
    have hy2 : ¬ (1 / 3 < y ∧ y < 1 / 2) := fun h => by linarith [h.2, hy1.1]
    simp only [Lim.R0, Lim.dfun, hy1, hy2, and_self, ↓reduceIte, sub_zero]
    rw [mul_add, mul_sub, mul_sub, mul_left_comm _ (6 : ℝ), hmin, mul_left_comm _ (6 : ℝ),
      hpos, hpos]
    push_cast
    rw [hN, ← hKy]
    ring_nf
  · have hc' : 2 * (p : ℝ) < K := by
      have : 2 * p < K := by omega
      exact_mod_cast this
    have hy1 : 1 / 3 < y ∧ y < 1 / 2 := by constructor <;> nlinarith
    simp only [Lim.R0, Lim.dfun, hy1, and_self, ↓reduceIte]
    rw [mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_left_comm _ (5 : ℝ), hmin,
      mul_left_comm _ (5 : ℝ), hpos, hpos, mul_sub _ _ (Lim.pos _), hpos]
    push_cast
    rw [hN, ← hKy]
    ring_nf

/-! ## The outer range: `v_p(S_K)` against its limit -/

theorem vpS_sub_limit {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) :
    -(vpS K p : ℝ) - K * (-2 * Lim.lam * ⌊(K : ℝ) / p⌋ +
      ∑ j ∈ Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K))) =
      ((∑ j ∈ Icc (1 : ℕ) 5,
        (2 * ((hof K - (j * p + 1) / 2 : ℕ) : ℤ) - max (2 * (hof K : ℤ) - j * p) 0) : ℤ) : ℝ) := by
  have h' := h
  obtain ⟨h7, h2, h3, h4, h5, h6⟩ := h'
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hh : ((hof K : ℕ) : ℝ) = K * Lim.lam := by
    obtain ⟨m, rfl⟩ := hK
    simp only [hof, Lim.lam]
    rw [show 37 * (40 * m) / 40 = 37 * m by omega]; push_cast; ring
  have hfl : ⌊(K : ℝ) / p⌋ = ((K / p : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_natCast]; norm_cast
  have hterm : ∀ j : ℕ, (K : ℝ) * Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K)) =
      ((max (2 * (hof K : ℤ) - j * p) 0 : ℤ) : ℝ) := by
    intro j
    simp only [Lim.pos]
    rw [mul_max_of_nonneg _ _ hK0.le, mul_zero]
    push_cast
    rw [hh]; congr 1; field_simp
  rw [vpS_outer hK h,
    sum_floor_eq (by unfold hof; omega), hfl, mul_add, mul_sum, sum_congr rfl fun j _ => hterm j]
  push_cast
  rw [hh, sum_sub_distrib, ← mul_sum]
  ring

theorem vpS_sub_limit_abs {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) :
    |-(vpS K p : ℝ) - K * (-2 * Lim.lam * ⌊(K : ℝ) / p⌋ +
      ∑ j ∈ Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K)))| ≤ 5 := by
  rw [vpS_sub_limit hK h]
  have : |∑ j ∈ Icc (1 : ℕ) 5,
      (2 * ((hof K - (j * p + 1) / 2 : ℕ) : ℤ) - max (2 * (hof K : ℤ) - j * p) 0)| ≤ 5 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ j ∈ Icc (1 : ℕ) 5, (1 : ℤ) := sum_le_sum fun j _ => by
            rw [abs_le]; constructor <;> omega
      _ = 5 := by simp
  exact_mod_cast this

/-- `uniformity_outer` (§5.2), with `Cst = 7`. -/
theorem uniformity_outer' :
    ∃ Cst : ℝ, ∀ K p : ℕ, [Fact p.Prime] → 40 ∣ K → OuterHyp K p →
      |-(gammaOut K p : ℝ) - K * (Lim.R0 ((p : ℝ) / K) - Lim.dfun ((p : ℝ) / K))| ≤ Cst ∧
      |-(vpS K p : ℝ) - K * (-2 * Lim.lam * ⌊(K : ℝ) / p⌋ +
          ∑ j ∈ Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K)))| ≤ Cst := by
  refine ⟨7, fun K p _ hK h => ⟨?_, (vpS_sub_limit_abs hK h).trans (by norm_num)⟩⟩
  rw [K_mul_R0_sub_dfun hK h]
  exact_mod_cast gammaOut_sub_Eout hK h

/-- **(5.3)**, Legendre's formula for `v_p(S_K)` (for `K > 0`; false at `K = 0`, see
`vpS_legendre_false_zero`). -/
theorem vpS_legendre (K p : ℕ) [Fact p.Prime] (hK : 40 ∣ K) (hK0 : 0 < K) :
    let B := 2 * hof K + K + 1
    vpS K p = 2 * hof K * ∑ a ∈ Icc 1 B, (K / p ^ a : ℕ)
      - 12 * hof K * ∑ a ∈ Icc 1 B, (Nof K / p ^ a : ℕ)
      - 2 * ∑ i ∈ Icc 1 (hof K - 1), ∑ a ∈ Icc 1 B, (2 * i / p ^ a : ℕ)
      + (hof K - 1) * padicValNat p 4 := vpS_legendre' K p hK hK0

/-- §5.2, outer range: `-γ_p^out = K (R₀(p/K) - d(p/K)) + O(1)` and
`-v_p(S_K) = K(-2λ⌊1/y⌋ + ∑_{j ≤ 5} (2λ - jy)₊) + O(1)` with `y = p/K`. -/
theorem uniformity_outer :
    ∃ Cst : ℝ, ∀ K p : ℕ, [Fact p.Prime] → 40 ∣ K → OuterHyp K p →
      |-(gammaOut K p : ℝ) - K * (Lim.R0 ((p : ℝ) / K) - Lim.dfun ((p : ℝ) / K))| ≤ Cst ∧
      |-(vpS K p : ℝ) - K * (-2 * Lim.lam * ⌊(K : ℝ) / p⌋ +
          ∑ j ∈ Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - j * ((p : ℝ) / K)))| ≤ Cst :=
  uniformity_outer'

end Zeta5
