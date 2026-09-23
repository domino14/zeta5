import Zeta5.Integrals5Base

/-!
# Exact integrals and bounds of §5 (fork VII)

Primed copies of theorems of `Section5.lean`.
-/

open MeasureTheory Set Finset

noncomputable section

namespace Zeta5

open I5

theorem integral_dfun' : ∫ y in (1 / 3 : ℝ)..(1 / 2), Lim.dfun y = 9 / 640 := by
  have hp : ∀ y : ℝ, 1 / 3 < y → y < 1 / 2 →
      Lim.dfun y = max ((1 + 4 * (3 / 40) - 3 * y) - max (1 + 3 / 40 - 3 * y) 0) 0 := by
    intro y h1 h2
    simp only [Lim.dfun, Lim.pos, Lim.α, h1, h2, and_self, ite_true]
  have e1 : ∀ y ∈ Ioo (1 / 3 : ℝ) (43 / 120), Lim.dfun y = 9 / 40 + 0 * y + 0 * y ^ 2 := by
    rintro y ⟨h1, h2⟩
    rw [hp y h1 (by linarith), max_eq_left (a := 1 + 3 / 40 - 3 * y) (by linarith),
      max_eq_left (by linarith)]; ring
  have e2 : ∀ y ∈ Ioo (43 / 120 : ℝ) (13 / 30), Lim.dfun y = 13 / 10 + (-3) * y + 0 * y ^ 2 := by
    rintro y ⟨h1, h2⟩
    rw [hp y (by linarith) (by linarith), max_eq_right (a := 1 + 3 / 40 - 3 * y) (by linarith),
      max_eq_left (by linarith)]; ring
  have e3 : ∀ y ∈ Ioo (13 / 30 : ℝ) (1 / 2), Lim.dfun y = 0 + 0 * y + 0 * y ^ 2 := by
    rintro y ⟨h1, h2⟩
    rw [hp y (by linarith) (by linarith), max_eq_right (a := 1 + 3 / 40 - 3 * y) (by linarith),
      max_eq_right (by linarith)]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 43 / 120)
      (piece_quad_int (by norm_num) _ _ _ e1)
      ((piece_quad_int (by norm_num) _ _ _ e2).trans (piece_quad_int (by norm_num) _ _ _ e3)),
    ← intervalIntegral.integral_add_adjacent_intervals (piece_quad_int (by norm_num) _ _ _ e2)
      (piece_quad_int (by norm_num) _ _ _ e3),
    piece_quad (by norm_num) _ _ _ e1, piece_quad (by norm_num) _ _ _ e2,
    piece_quad (by norm_num) _ _ _ e3]
  norm_num

lemma G0_abs_le (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) : |Lim.G0 v| ≤ 97 / 6000 := by
  have ht1 : -1 ≤ 2 * v - 1 := by linarith
  have ht2 : 2 * v - 1 ≤ 1 := by linarith
  set t := 2 * v - 1 with ht
  have hG : Lim.G0 v = (t - t ^ 3) / 24 := by simp only [Lim.G0, ht]; ring
  rw [hG, abs_le]
  have a1 := mul_nonneg (sq_nonneg (t - 5774 / 10000)) (by linarith : (0 : ℝ) ≤ t + 2 * (5774 / 10000))
  have a2 := mul_nonneg (sq_nonneg (t + 5774 / 10000)) (by linarith : (0 : ℝ) ≤ 2 * (5774 / 10000) - t)
  constructor <;> nlinarith

theorem Cper_bound' (x : ℝ) : |Lim.Cper x| < 16 := by
  have h1 := G0_abs_le (Int.fract (Lim.α * x)) (Int.fract_nonneg _) (Int.fract_lt_one _).le
  have h2 := G0_abs_le (Int.fract x) (Int.fract_nonneg _) (Int.fract_lt_one _).le
  simp only [Lim.Cper, Lim.α, Lim.lam] at *
  calc |74 / (3 / 40) * Lim.G0 (Int.fract (3 / 40 * x)) - 37 / 40 * Lim.G0 (Int.fract x)|
      ≤ |74 / (3 / 40) * Lim.G0 (Int.fract (3 / 40 * x))| + |37 / 40 * Lim.G0 (Int.fract x)| :=
        abs_sub _ _
    _ = 74 / (3 / 40) * |Lim.G0 (Int.fract (3 / 40 * x))| + 37 / 40 * |Lim.G0 (Int.fract x)| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_of_pos (by norm_num : (0:ℝ) < 37 / 40)]
    _ < 16 := by nlinarith

lemma fract_quad_piece (n : ℕ) : ∀ x ∈ Ioo (n : ℝ) (n + 1),
    Int.fract x * (1 - Int.fract x) = (-(n : ℝ) - n ^ 2) + (1 + 2 * n) * x + (-1) * x ^ 2 := by
  rintro x ⟨h1, h2⟩
  have : Int.fract x = x - n := by
    rw [Int.fract, show ⌊x⌋ = (n : ℤ) from Int.floor_eq_iff.2 ⟨by push_cast; linarith,
      by push_cast; linarith⟩]; push_cast; ring
  rw [this]; ring

lemma fract_quad_integral (n : ℕ) :
    IntervalIntegrable (fun x => Int.fract x * (1 - Int.fract x)) volume 0 n ∧
      ∫ x in (0 : ℝ)..n, Int.fract x * (1 - Int.fract x) = n / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := piece_quad_int (by linarith) _ _ _ (fract_quad_piece n)
    have hv := piece_quad (by linarith) _ _ _ (fract_quad_piece n)
    push_cast
    refine ⟨ih.1.trans hi, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih.1 hi, ih.2, hv]; ring

theorem Pper_mean' : (∫ x in (0 : ℝ)..40, Lim.Pper x) / 40 = 2923 / 240 := by
  have hA := fract_quad_integral 40
  have hB := fract_quad_integral 3
  push_cast at hA hB
  have hBc : IntervalIntegrable (fun x => Int.fract (3 / 40 * x) * (1 - Int.fract (3 / 40 * x)))
      volume 0 40 := by
    have := hB.1.comp_mul_left (c := 3 / 40) (by simp) (by simp)
    norm_num at this; exact this
  have hBv : ∫ x in (0 : ℝ)..40, Int.fract (3 / 40 * x) * (1 - Int.fract (3 / 40 * x)) = 20 / 3 := by
    rw [intervalIntegral.integral_comp_mul_left (fun u => Int.fract u * (1 - Int.fract u))
      (by norm_num : (3 / 40 : ℝ) ≠ 0)]
    norm_num [hB.2]
  have : (fun x => Lim.Pper x) = fun x =>
      74 * (Int.fract (3 / 40 * x) * (1 - Int.fract (3 / 40 * x))) -
        37 / 40 * (Int.fract x * (1 - Int.fract x)) := by
    ext x; simp only [Lim.Pper, Lim.α, Lim.lam]; ring
  rw [this, intervalIntegral.integral_sub (hBc.const_mul 74) (hA.1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hBv, hA.2]
  norm_num

end Zeta5
