import Zeta5.Section7

/-!
# Theorem 1.1: `ζ(5)` is irrational

The deduction from Theorem 2.1 (§1.1 and §7 of the paper) is proved completely here. The
remaining gaps are exactly the `sorry`s in the files this one imports; run
`#print axioms Zeta5.zeta5_irrational` to see whether `sorryAx` is still used.
-/

open Polynomial Filter

namespace Zeta5

/-- The abstract top-level argument. If integer polynomials `Q_n` of degree at most `dn`
satisfy `0 < Q_n(x) < exp(-cn²)` for large `n`, then `x` is irrational. When `x = a/b`,
`b^{dn} Q_n(a/b)` is a positive integer that is eventually `< 1`. -/
theorem irrational_of_int_poly_approx {x c : ℝ} (hc : 0 < c) (d : ℕ) (Qs : ℕ → ℤ[X])
    (hdeg : ∀ n, (Qs n).natDegree ≤ d * n)
    (hQ : ∀ᶠ n : ℕ in atTop,
      0 < aeval x (Qs n) ∧ aeval x (Qs n) < Real.exp (-(c * (n : ℝ) ^ 2))) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  have hb0 : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hb1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast q.den_pos
  obtain ⟨n, ⟨hpos, hlt⟩, hn⟩ :=
    (hQ.and (eventually_ge_atTop ⌈(d : ℝ) * Real.log q.den / c⌉₊)).exists
  set v := aeval (q : ℝ) (Qs n) with hv
  -- `b^{deg} |Q(a/b)| ≥ 1`
  have hev : eval ((q.num : ℝ) / ((q.den : ℤ) : ℝ)) ((Qs n).map (algebraMap ℤ ℝ)) = v := by
    rw [hv, aeval_def, eval_map, Rat.cast_def]
    push_cast
    rfl
  have h1 := one_le_pow_mul_abs_eval_div (K := ℝ) (f := Qs n) (a := q.num) (b := (q.den : ℤ))
    (by exact_mod_cast q.den_pos) (by rw [hev]; exact hpos.ne')
  rw [hev, abs_of_pos hpos] at h1
  push_cast at h1
  have h2 : (1 : ℝ) ≤ (q.den : ℝ) ^ (d * n) * v :=
    h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb1 (hdeg n)) hpos.le)
  -- `b^{dn} exp(-cn²) ≤ 1` once `n ≥ d log b / c`
  have hn' : (d : ℝ) * Real.log q.den ≤ c * n := by
    have := (Nat.ceil_le.mp hn)
    rw [div_le_iff₀ hc] at this
    linarith [mul_comm (n : ℝ) c]
  have h3 : (q.den : ℝ) ^ (d * n) * Real.exp (-(c * (n : ℝ) ^ 2)) ≤ 1 := by
    rw [← Real.exp_log hb0, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_one_iff]
    push_cast
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hn' hn0]
  have h4 : (q.den : ℝ) ^ (d * n) * v < (q.den : ℝ) ^ (d * n) * Real.exp (-(c * (n : ℝ) ^ 2)) :=
    mul_lt_mul_of_pos_left hlt (pow_pos hb0 _)
  linarith

/-- `ζ(5)` is real: `riemannZeta 5 = ζ5`. -/
theorem riemannZeta_five_eq : riemannZeta 5 = (ζ5 : ℂ) := by
  have h := riemannZeta_im_eq_zero_of_one_lt (x := 5) (by norm_num)
  push_cast at h
  apply Complex.ext
  · simp [ζ5]
  · simpa using h

open scoped Classical in
/-- The integer polynomials `Q_{40n,200}` (and `0` for small `n`). -/
noncomputable def Qint (n : ℕ) : ℤ[X] :=
  if h : StdHyp (40 * n) 200 then (theorem_2_1 h).1.choose else 0

theorem Qint_spec {n : ℕ} (h : StdHyp (40 * n) 200) :
    (Qint n).map (algebraMap ℤ ℚ) = Q (40 * n) 200 := by
  simp only [Qint, h, ↓reduceDIte]
  exact (theorem_2_1 h).1.choose_spec

/-- **Theorem 1.1.** `ζ(5)` is irrational. -/
theorem zeta5_irrational : Irrational ζ5 := by
  refine irrational_of_int_poly_approx (c := 139 / 5) (by norm_num) 37 Qint ?_ ?_
  · intro n
    by_cases h : StdHyp (40 * n) 200
    · have := congrArg natDegree (Qint_spec h)
      rw [natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)),
        (theorem_2_1 h).2.1] at this
      rw [this, hof]
      omega
    · simp [Qint, h]
  · filter_upwards [theorem_2_1_decay_200, eventually_ge_atTop 200000] with n hQ hn
    have hstd : StdHyp (40 * n) 200 := ⟨by norm_num, Dvd.intro n rfl, by omega, by omega⟩
    have : aeval ζ5 (Qint n) = aeval ζ5 (Q (40 * n) 200) := by
      rw [← Qint_spec hstd, aeval_map_algebraMap]
    rw [this]
    exact hQ

/-- **Theorem 1.1**, stated for Mathlib's `riemannZeta`. -/
theorem riemannZeta_five_irrational : Irrational (riemannZeta 5).re := zeta5_irrational

theorem riemannZeta_five_im : (riemannZeta 5).im = 0 := by
  rw [riemannZeta_five_eq]; simp

end Zeta5
