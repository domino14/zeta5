import Zeta5.Section5

/-!
# Helpers for the exact integrals of §5 (fork VII)
-/

open MeasureTheory Set

noncomputable section

namespace Zeta5.I5

lemma ae_ne (b : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
  simp [ae_iff, measure_singleton]

/-- Replace the integrand on the open interval. -/
lemma integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioo a b, f x = g x) : ∫ x in a..b, f x = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae'
  · filter_upwards [ae_ne b] with x hxb hx
    exact h x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
  · exact Filter.Eventually.of_forall fun x hx => by
      exact absurd (hx.1.trans_le hx.2) (not_lt.2 hab)

/-- A quadratic piece. -/
lemma piece_quad {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (c0 c1 c2 : ℝ)
    (h : ∀ x ∈ Ioo a b, f x = c0 + c1 * x + c2 * x ^ 2) :
    ∫ x in a..b, f x = (c0 * b + c1 * b ^ 2 / 2 + c2 * b ^ 3 / 3) -
      (c0 * a + c1 * a ^ 2 / 2 + c2 * a ^ 3 / 3) := by
  rw [integral_congr_Ioo hab h]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have := (((hasDerivAt_id x).const_mul c0).add
      (((hasDerivAt_pow 2 x).div_const 2).const_mul c1)).add
      (((hasDerivAt_pow 3 x).div_const 3).const_mul c2)
    convert this using 1
    · ext y; simp; try ring
    · simp; try ring
  · apply Continuous.intervalIntegrable; fun_prop

/-- An `(A x + B)/x³` piece, `0 < a`. -/
lemma piece_rat {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (A B : ℝ)
    (h : ∀ x ∈ Ioo a b, f x = A * x + B) :
    ∫ x in a..b, f x / x ^ 3 = (-A / b - B / (2 * b ^ 2)) - (-A / a - B / (2 * a ^ 2)) := by
  rw [integral_congr_Ioo hab (g := fun x => (A * x + B) / x ^ 3)
    (fun x hx => by rw [h x hx])]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hx0 : 0 < x := by
      rw [uIcc_of_le hab] at hx; linarith [hx.1]
    have h1 := ((hasDerivAt_inv hx0.ne').const_mul (-A))
    have h2 := (((hasDerivAt_pow 2 x).inv (by positivity)).const_mul (-B / 2))
    convert h1.add h2 using 1
    · ext y; simp only [Pi.add_apply, Pi.inv_apply]
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · field_simp; ring
    · field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; rw [uIcc_of_le hab] at hx; have : 0 < x := by linarith [hx.1]
    positivity

lemma piece_quad_int {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (c0 c1 c2 : ℝ)
    (h : ∀ x ∈ Ioo a b, f x = c0 + c1 * x + c2 * x ^ 2) :
    IntervalIntegrable f volume a b := by
  have hc : IntervalIntegrable (fun x : ℝ => c0 + c1 * x + c2 * x ^ 2) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => c0 + c1 * x + c2 * x ^ 2).intervalIntegrable a b
  exact hc.congr_uIoo fun x hx => (h x (by rwa [uIoo_of_le hab] at hx)).symm

lemma piece_rat_int {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (A B : ℝ)
    (h : ∀ x ∈ Ioo a b, f x = A * x + B) :
    IntervalIntegrable (fun x => f x / x ^ 3) volume a b := by
  have hc : IntervalIntegrable (fun x : ℝ => (A * x + B) / x ^ 3) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; rw [uIcc_of_le hab] at hx; have : 0 < x := by linarith [hx.1]
    positivity
  exact hc.congr_uIoo fun x hx => by rw [h x (by rwa [uIoo_of_le hab] at hx)]

end Zeta5.I5

namespace Zeta5.I5

lemma chain {f : ℝ → ℝ} {a b c v w : ℝ}
    (h1 : IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = v)
    (h2 : IntervalIntegrable f volume b c ∧ ∫ x in b..c, f x = w) :
    IntervalIntegrable f volume a c ∧ ∫ x in a..c, f x = v + w :=
  ⟨h1.1.trans h2.1, by rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1, h1.2, h2.2]⟩

lemma piece_quad' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (c0 c1 c2 : ℝ)
    (h : ∀ x ∈ Ioo a b, f x = c0 + c1 * x + c2 * x ^ 2) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = (c0 * b + c1 * b ^ 2 / 2 + c2 * b ^ 3 / 3) -
      (c0 * a + c1 * a ^ 2 / 2 + c2 * a ^ 3 / 3) :=
  ⟨piece_quad_int hab c0 c1 c2 h, piece_quad hab c0 c1 c2 h⟩

lemma piece_rat' {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (A B : ℝ)
    (h : ∀ x ∈ Ioo a b, f x = A * x + B) :
    IntervalIntegrable (fun x => f x / x ^ 3) volume a b ∧
      ∫ x in a..b, f x / x ^ 3 = (-A / b - B / (2 * b ^ 2)) - (-A / a - B / (2 * a ^ 2)) :=
  ⟨piece_rat_int ha hab A B h, piece_rat ha hab A B h⟩

/-- `⌊1/y⌋ = k` from linear conditions. -/
lemma floor_inv_eq {y : ℝ} (k : ℤ) (hy : 0 < y) (h1 : (k : ℝ) * y ≤ 1) (h2 : 1 < ((k : ℝ) + 1) * y) :
    ((⌊1 / y⌋ : ℤ) : ℝ) = k := by
  rw [Int.floor_eq_iff.2 ⟨by rw [le_div_iff₀ hy]; linarith, by rw [div_lt_iff₀ hy]; linarith⟩]

lemma not_lt_of_le' {a b : ℝ} (h : b ≤ a) : ¬ a < b := not_lt.2 h
lemma not_le_of_lt' {a b : ℝ} (h : b < a) : ¬ a ≤ b := not_le.2 h

end Zeta5.I5

/-- Discharger: linear side conditions (works inside `simp (disch := dsch)`). -/
macro "dsch1" : tactic => `(tactic| (by_contra hh; (try push Not at hh); linarith))
macro "dsch" : tactic => `(tactic| first
  | dsch1
  | (constructor <;> dsch1)
  | (by_contra hh; obtain ⟨_, _⟩ := hh; linarith))
