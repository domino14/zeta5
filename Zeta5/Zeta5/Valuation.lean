import Zeta5.Defs

/-!
# Valuation toolkit

`vge p x b` means `x = 0 ∨ b ≤ v_p(x)` for `x ∈ ℚ` and a rational bound `b`. `vpGge p A b` from
`Defs.lean` is `∀ i, vge p (A.coeff i) b`. The lemmas below say that these bounds are closed
under sums, products and determinant terms, which is the Gauss lemma for the Gauss valuation.
-/

open Polynomial Finset

set_option linter.unusedSectionVars false

namespace Zeta5

/-- `x = 0` or `b ≤ v_p(x)`. -/
def vge (p : ℕ) (x b : ℚ) : Prop := x ≠ 0 → b ≤ (padicValRat p x : ℚ)

variable {p : ℕ} [hp : Fact p.Prime]

theorem vge_zero (b : ℚ) : vge p 0 b := fun h => absurd rfl h

theorem vge_mono {x b b' : ℚ} (h : vge p x b) (hb : b' ≤ b) : vge p x b' :=
  fun hx => hb.trans (h hx)

theorem vge_add {x y b : ℚ} (hx : vge p x b) (hy : vge p y b) : vge p (x + y) b := by
  intro hxy
  by_cases hx0 : x = 0
  · subst hx0; simpa using hy (by simpa using hxy)
  by_cases hy0 : y = 0
  · subst hy0; simpa using hx (by simpa using hxy)
  have := padicValRat.min_le_padicValRat_add (p := p) hxy
  have h' : (min (padicValRat p x) (padicValRat p y) : ℚ) ≤ padicValRat p (x + y) := by
    exact_mod_cast this
  exact le_trans (le_min (hx hx0) (hy hy0)) (by simpa using h')

theorem vge_neg {x b : ℚ} (h : vge p x b) : vge p (-x) b := by
  intro hx
  rw [padicValRat.neg]
  exact h (neg_ne_zero.mp hx)

theorem vge_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {b : ℚ} (h : ∀ i ∈ s, vge p (f i) b) :
    vge p (∑ i ∈ s, f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vge_zero (p := p) b
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact vge_add (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem vge_mul {x y a b : ℚ} (hx : vge p x a) (hy : vge p y b) : vge p (x * y) (a + b) := by
  intro hxy
  have hx0 : x ≠ 0 := left_ne_zero_of_mul hxy
  have hy0 : y ≠ 0 := right_ne_zero_of_mul hxy
  rw [padicValRat.mul hx0 hy0]
  push_cast
  exact add_le_add (hx hx0) (hy hy0)

theorem vge_one : vge p 1 0 := by
  intro _; simp

theorem vge_inv_p : vge p (p : ℚ)⁻¹ (-1) := by
  intro _
  rw [padicValRat.inv, padicValRat.self hp.out.one_lt]
  norm_num

/-! ## Polynomials -/

theorem vpGge_iff (A : ℚ[X]) (b : ℚ) : vpGge p A b ↔ ∀ i, vge p (A.coeff i) b := Iff.rfl

theorem vpGge_zero (b : ℚ) : vpGge p (0 : ℚ[X]) b := fun i h => by simp at h

theorem vpGge_mono {A : ℚ[X]} {b b' : ℚ} (h : vpGge p A b) (hb : b' ≤ b) : vpGge p A b' :=
  fun i => vge_mono (h i) hb

theorem vpGge_add {A B : ℚ[X]} {b : ℚ} (hA : vpGge p A b) (hB : vpGge p B b) :
    vpGge p (A + B) b := fun i => by rw [coeff_add]; exact vge_add (hA i) (hB i)

theorem vpGge_neg {A : ℚ[X]} {b : ℚ} (hA : vpGge p A b) : vpGge p (-A) b :=
  fun i => by rw [coeff_neg]; exact vge_neg (hA i)

theorem vpGge_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) {b : ℚ}
    (h : ∀ i ∈ s, vpGge p (f i) b) : vpGge p (∑ i ∈ s, f i) b := fun n => by
  rw [finsetSum_coeff]; exact vge_sum s _ fun i hi => h i hi n

theorem vpGge_C {c b : ℚ} (h : vge p c b) : vpGge p (C c) b := fun n => by
  rw [coeff_C]; split_ifs
  · exact h
  · exact vge_zero b

theorem vpGge_one : vpGge p (1 : ℚ[X]) 0 := by
  rw [← C_1]; exact vpGge_C vge_one

theorem vpGge_mul {A B : ℚ[X]} {a b : ℚ} (hA : vpGge p A a) (hB : vpGge p B b) :
    vpGge p (A * B) (a + b) := fun n => by
  rw [coeff_mul]
  exact vge_sum _ _ fun x _ => vge_mul (hA x.1) (hB x.2)

theorem vpGge_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (b : ι → ℚ)
    (h : ∀ i ∈ s, vpGge p (f i) (b i)) : vpGge p (∏ i ∈ s, f i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vpGge_one (p := p)
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact vpGge_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem vpGge_zsmul_unit {A : ℚ[X]} {b : ℚ} (u : ℤˣ) (hA : vpGge p A b) : vpGge p (u • A) b := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hA
  · simpa using vpGge_neg hA

/-- Determinant bound from entry bounds: if every term `∏ᵢ M (σ i) i` of the Leibniz expansion
has valuation at least `B`, so does `det M`. -/
theorem vpGge_det_of_terms {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X]) {B : ℚ}
    (h : ∀ σ : Equiv.Perm ι, vpGge p (∏ i, M (σ i) i) B) : vpGge p M.det B := by
  rw [Matrix.det_apply]
  exact vpGge_sum _ _ fun σ _ => vpGge_zsmul_unit _ (h σ)

end Zeta5
