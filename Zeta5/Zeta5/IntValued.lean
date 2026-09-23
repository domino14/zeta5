import Zeta5.Functionals
import Zeta5.Valuation

/-!
# Integer-valued polynomials and the bound (3.9)

A self-contained replacement for the `ℤ_p`-analytic arguments of §3.3, using only values at
integers:

* `tau_vge_of_values`: if `deg f ≤ D` and `f` is `p^{-a}`-integral at `D+1` consecutive integers,
  then `v_p(τ(f)) ≥ -a - 4⌊log_p(D+1)⌋`. This is (3.9) without the `-v_p(24)` term: `τ` of a
  binomial polynomial is the fourth Taylor coefficient of the next one (from `τ(Δf) = f⁗(0)/24`).
* `diffQuot_vge`: difference quotients of integer-valued polynomials of degree `≤ d` lose at most
  `⌊log_p max(1, d)⌋`, as in (3.8).
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-- `A` is integer-valued at `p` on `ℤ`: `A(x) ∈ ℤ_(p)` for every integer `x`. For `A ∈ ℚ[X]`
this is equivalent to `A(ℤ_p) ⊂ ℤ_p`, by density of `ℤ` in `ℤ_p`. -/
def IntValuedAt (p : ℕ) (A : ℚ[X]) : Prop :=
  ∀ x : ℤ, A.eval (x : ℚ) ≠ 0 → 0 ≤ padicValRat p (A.eval x)

theorem IntValuedAt.vge {p : ℕ} {A : ℚ[X]} (h : IntValuedAt p A) (x : ℤ) :
    vge p (A.eval (x : ℚ)) 0 := fun hx => by exact_mod_cast h x hx

/-! ## Binomial polynomials -/

/-- `binom(x, k) = x(x-1)⋯(x-k+1)/k!`. -/
def bp (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * ∏ i ∈ range k, (X - C (i : ℚ))

theorem bp_zero : bp 0 = 1 := by simp [bp]

theorem bp_succ (k : ℕ) : bp (k + 1) = C (((k : ℚ) + 1)⁻¹) * bp k * (X - C (k : ℚ)) := by
  unfold bp
  rw [prod_range_succ, Nat.factorial_succ]
  push_cast
  rw [mul_inv, C_mul]
  ring

theorem bp_natDegree_le (k : ℕ) : (bp k).natDegree ≤ k := by
  induction k with
  | zero => simp [bp_zero]
  | succ k ih =>
    rw [bp_succ]
    refine (natDegree_mul_le).trans ?_
    refine add_le_add ((natDegree_C_mul_le _ _).trans ih) ?_
    exact (natDegree_X_sub_C_le _)

theorem bp_eval_nat (k n : ℕ) : (bp k).eval (n : ℚ) = (n.choose k : ℚ) := by
  induction k with
  | zero => simp [bp_zero]
  | succ k ih =>
    rw [bp_succ, eval_mul, eval_mul, eval_C, ih, eval_sub, eval_X, eval_C]
    have h := Nat.choose_succ_right_eq n k
    rcases le_or_gt k n with hkn | hkn
    · have h' : (n.choose (k + 1) : ℚ) * (k + 1) = n.choose k * ((n : ℚ) - k) := by
        exact_mod_cast (show (n.choose (k + 1) * (k + 1) : ℤ) = n.choose k * ((n : ℤ) - k) by
          have := congrArg (fun x : ℕ => (x : ℤ)) h
          push_cast [Nat.cast_sub hkn] at this
          exact this)
      field_simp
      linarith
    · rw [Nat.choose_eq_zero_of_lt hkn, Nat.choose_eq_zero_of_lt (by omega)]
      simp

/-- `binom(-(t+1), k) = (-1)^k binom(t+k, k)`. -/
theorem bp_eval_neg (k t : ℕ) :
    (bp k).eval (-((t : ℚ) + 1)) = (-1) ^ k * ((t + k).choose k : ℚ) := by
  induction k with
  | zero => simp [bp_zero]
  | succ k ih =>
    rw [bp_succ, eval_mul, eval_mul, eval_C, ih, eval_sub, eval_X, eval_C]
    have h := Nat.add_one_mul_choose_eq (t + k) k
    have h' : ((t + k + 1 : ℕ) : ℚ) * ((t + k).choose k : ℚ) =
        ((t + k + 1).choose (k + 1) : ℚ) * (k + 1) := by exact_mod_cast h
    rw [show t + (k + 1) = t + k + 1 by ring]
    push_cast at h' ⊢
    field_simp
    linear_combination (-(-1) ^ k) * h'

/-- Binomial polynomials are integer-valued on `ℤ`. -/
theorem bp_eval_int (k : ℕ) (m : ℤ) : ∃ z : ℤ, (bp k).eval (m : ℚ) = z := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact ⟨n.choose k, by rw [Int.cast_natCast, bp_eval_nat]; norm_cast⟩
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, m = -((t : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    refine ⟨(-1) ^ k * (t + k).choose k, ?_⟩
    rw [ht]; push_cast; exact bp_eval_neg k t

theorem vge_int (p : ℕ) (z : ℤ) : vge p (z : ℚ) 0 := by
  intro hz
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

theorem eq_of_eval_nat_eq {P Q : ℚ[X]} (h : ∀ n : ℕ, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : ℚ)))
  · rintro _ ⟨n, rfl⟩; exact h n
  · exact Set.infinite_range_of_injective Nat.cast_injective

/-- Pascal: `Δ binom(x, k+1) = binom(x, k)`. -/
theorem bp_fwd (k : ℕ) : (bp (k + 1)).comp (X + 1) - bp (k + 1) = bp k := by
  apply eq_of_eval_nat_eq
  intro n
  rw [eval_sub, eval_comp, eval_add, eval_X, eval_one,
    show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by push_cast; ring, bp_eval_nat, bp_eval_nat, bp_eval_nat,
    Nat.choose_succ_succ]
  push_cast; ring

/-- `binom(x, k+1) = (x/(k+1)) binom(x-1, k)`. -/
theorem bp_shift (k : ℕ) : bp (k + 1) = C (((k : ℚ) + 1)⁻¹) * X * (bp k).comp (X - 1) := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℚ)))
  · rintro _ ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [bp_eval_nat, eval_mul, eval_mul, eval_C, eval_X, eval_comp, eval_sub, eval_X, eval_one,
      show ((n + 1 : ℕ) : ℚ) - 1 = (n : ℚ) by push_cast; ring, bp_eval_nat]
    have h := Nat.add_one_mul_choose_eq n k
    have h' : ((n + 1 : ℕ) : ℚ) * (n.choose k : ℚ) = ((n + 1).choose (k + 1) : ℚ) * (k + 1) := by
      exact_mod_cast h
    field_simp
    linarith
  · exact Set.infinite_range_of_injective fun a b h => by simpa using h

/-! ## `τ` of forward differences -/

theorem Lfun_sub (P Q : ℚ[X]) : Lfun (P - Q) = Lfun P - Lfun Q := by
  rw [sub_eq_add_neg, Lfun_add, neg_eq_neg_one_mul, ← C_1, ← C_neg, Lfun_C_mul]; ring

theorem Lfun_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    Lfun (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lfun]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, Lfun_add, ih]

theorem Lfun_X_pow (n : ℕ) : Lfun (X ^ n) = _root_.bernoulli n := by
  rw [X_pow_eq_monomial, Lfun_monomial, one_mul]

/-- `L(f(x+1) - f(x)) = f'(0)`: the defining recursion of the Bernoulli numbers. -/
theorem Lfun_fwd (f : ℚ[X]) : Lfun (f.comp (X + 1) - f) = f.derivative.eval 0 := by
  induction f using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, show P.comp (X + 1) + Q.comp (X + 1) - (P + Q) =
      (P.comp (X + 1) - P) + (Q.comp (X + 1) - Q) by ring, Lfun_add, hP, hQ, derivative_add,
      eval_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, ← mul_sub, Lfun_C_mul]
    have hexp : (X + 1 : ℚ[X]) ^ n - X ^ n = ∑ m ∈ range n, C (n.choose m : ℚ) * X ^ m := by
      rw [add_pow, sum_range_succ]
      simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, Nat.sub_self]
      rw [add_sub_cancel_right]
      exact sum_congr rfl fun m _ => by rw [← C_eq_natCast, mul_comm]
    rw [hexp, Lfun_sum]
    simp_rw [Lfun_C_mul, Lfun_X_pow]
    rw [_root_.sum_bernoulli, derivative_C_mul_X_pow]
    rcases n with _ | _ | n <;> simp

theorem derivative_comp_X_add_one (f : ℚ[X]) :
    derivative (f.comp (X + 1)) = (derivative f).comp (X + 1) := by
  rw [derivative_comp]; simp

/-- `τ(f(x+1) - f(x)) = f⁗(0)/24 = [x⁴] f`: the difference identity (3.3) for polynomials. -/
theorem tau_fwd (f : ℚ[X]) : tau (f.comp (X + 1) - f) = f.coeff 4 := by
  unfold tau
  rw [deriv3]
  simp only [derivative_sub, derivative_comp_X_add_one]
  rw [Lfun_fwd, ← coeff_zero_eq_eval_zero]
  have h := coeff_iterate_derivative (k := 4) f 0
  simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id] at h
  rw [h]
  simp [Nat.descFactorial]

/-- `τ(binom(x, k)) = [x⁴] binom(x, k+1)`. -/
theorem tau_bp (k : ℕ) : tau (bp k) = (bp (k + 1)).coeff 4 := by
  rw [← bp_fwd k, tau_fwd]

/-! ## The coefficients of `binom(x, n)` -/

variable {p : ℕ} [hp : Fact p.Prime]

theorem vge_inv_nat (j : ℕ) (_hj : 1 ≤ j) : vge p ((j : ℚ)⁻¹) (-(Nat.log p j : ℚ)) := by
  intro _
  rw [padicValRat.inv]
  have h2 : padicValRat p (j : ℚ) = padicValNat p j := padicValRat.of_nat
  have h3 : (padicValRat p (j : ℚ) : ℚ) ≤ Nat.log p j := by
    rw [h2]; exact_mod_cast padicValNat_le_nat_log (p := p) j
  push_cast
  linarith

/-- Weighted Gauss bound: `v_p(coeff_m P) ≥ -m c`. -/
def WB (p : ℕ) (c : ℚ) (P : ℚ[X]) : Prop := ∀ m, vge p (P.coeff m) (-(m : ℚ) * c)

theorem WB_mul {c : ℚ} {P Q : ℚ[X]} (hP : WB p c P) (hQ : WB p c Q) : WB p c (P * Q) := by
  intro m
  rw [coeff_mul]
  refine vge_sum _ _ fun x hx => ?_
  have hm : (x.1 : ℚ) + x.2 = m := by exact_mod_cast mem_antidiagonal.mp hx
  exact vge_mono (vge_mul (hP x.1) (hQ x.2)) (by rw [← hm]; ring_nf; rfl)

theorem WB_one (c : ℚ) : WB p c 1 := by
  intro m; rw [coeff_one]; split_ifs with h
  · subst h; simpa using vge_one (p := p)
  · exact vge_zero _

theorem WB_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) {c : ℚ} (h : ∀ i ∈ s, WB p c (f i)) :
    WB p c (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WB_one (p := p) c
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact WB_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

/-- `C u * X - C v` with `v_p(u) ≥ -c`, `v_p(v) ≥ 0`. -/
theorem WB_linear {c u v : ℚ} (hu : vge p u (-c)) (hv : vge p v 0) : WB p c (C u * X - C v) := by
  intro m
  rw [coeff_sub, coeff_C_mul, coeff_X, coeff_C]
  rcases m with _ | _ | m
  · simpa using vge_neg hv
  · simpa using hu
  · simpa using vge_zero (p := p) _

theorem bp_factor (m : ℕ) :
    bp (m + 1) = (C (((m : ℚ) + 1)⁻¹) * X - C 0) *
      ∏ i ∈ range m, (C (((i : ℚ) + 1)⁻¹) * X - C 1) := by
  induction m with
  | zero => simp [bp_succ, bp_zero]
  | succ m ih =>
    rw [bp_succ, ih, prod_range_succ]
    have hu : ((m : ℚ) + 1) ≠ 0 := by positivity
    have hinv : C (((m : ℚ) + 1)⁻¹) * C ((m : ℚ) + 1) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hu, C_1]
    push_cast
    simp only [C_0, sub_zero, C_1]
    linear_combination (-(C (((m : ℚ) + 1 + 1)⁻¹) * X) *
      ∏ i ∈ range m, (C (((i : ℚ) + 1)⁻¹) * X - 1)) * hinv

/-- `v_p([x⁴] binom(x, n)) ≥ -4⌊log_p n⌋`. -/
theorem bp_coeff4 (n : ℕ) : vge p ((bp n).coeff 4) (-4 * (Nat.log p n : ℚ)) := by
  rcases n with _ | m
  · norm_num [bp_zero, coeff_one]; exact vge_zero _
  · have hWB : WB p (Nat.log p (m + 1) : ℚ) (bp (m + 1)) := by
      rw [bp_factor]
      refine WB_mul (WB_linear ?_ (by simpa using vge_zero (p := p) 0)) (WB_prod _ _ fun i hi => ?_)
      · have := vge_inv_nat (p := p) (m + 1) (by omega); push_cast at this; exact this
      · refine WB_linear ?_ (by simpa using vge_one (p := p))
        have h := vge_inv_nat (p := p) (i + 1) (by omega)
        push_cast at h
        refine vge_mono h (neg_le_neg ?_)
        exact_mod_cast Nat.log_mono_right (by simp at hi; omega)
    have := hWB 4
    push_cast at this ⊢
    exact this

/-! ## Newton interpolation -/

/-- `Δ^k f(y)`, the `k`-th forward difference of the polynomial function `f` at `y`. -/
def fd (f : ℚ[X]) (y : ℚ) (k : ℕ) : ℚ := (fwdDiff (1 : ℚ))^[k] (fun x => f.eval x) y

theorem fd_vge (f : ℚ[X]) (y a : ℚ) (k : ℕ) (hv : ∀ i ≤ k, vge p (f.eval (y + i)) (-a)) :
    vge p (fd f y k) (-a) := by
  unfold fd
  rw [fwdDiff_iter_eq_sum_shift]
  refine vge_sum _ _ fun i hi => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  have h := vge_mul (vge_int p ((-1) ^ (k - i) * k.choose i)) (hv i (by simp at hi; omega))
  simpa using h

/-- Newton's forward-difference formula as a polynomial identity. -/
theorem newton (f : ℚ[X]) (D : ℕ) (hD : f.natDegree ≤ D) (y : ℚ) :
    f = ∑ k ∈ range (D + 1), C (fd f y k) * (bp k).comp (X - C y) := by
  set s := (range (D + 1)).image fun n : ℕ => y + n
  have hinj : Function.Injective fun n : ℕ => y + n := fun a b h => by
    simpa using h
  have hcard : s.card = D + 1 := by rw [card_image_of_injective _ hinj, card_range]
  apply eq_of_degree_sub_lt_of_eval_finset_eq s
  · rw [hcard]
    have h1 : (∑ k ∈ range (D + 1), C (fd f y k) * (bp k).comp (X - C y)).natDegree ≤ D := by
      refine natDegree_sum_le_of_forall_le _ _ fun k hk => (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_comp_le.trans ?_
      rw [natDegree_X_sub_C, mul_one]
      exact (bp_natDegree_le k).trans (by simp at hk; omega)
    have h2 := (natDegree_sub_le f _).trans (max_le hD h1)
    calc _ ≤ ((f - _).natDegree : WithBot ℕ) := degree_le_natDegree
      _ < _ := by exact_mod_cast Nat.lt_succ_of_le h2
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    have hn' : n + 1 ≤ D + 1 := by simp at hn; omega
    have hsh := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ)) (fun x => f.eval x) n y
    simp only [nsmul_eq_mul, mul_one] at hsh
    rw [hsh, eval_finsetSum]
    symm
    rw [← sum_subset (range_subset_range.mpr hn')]
    · refine sum_congr rfl fun k _ => ?_
      rw [eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_left,
        bp_eval_nat]
      unfold fd
      ring
    · intro k _ hk
      rw [eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_left, bp_eval_nat,
        Nat.choose_eq_zero_of_lt (by simp at hk; omega)]
      simp

/-- (3.9), in the form used here. -/
theorem tau_vge_of_values (p : ℕ) [Fact p.Prime] (f : ℚ[X]) (D : ℕ) (hD : f.natDegree ≤ D)
    (y : ℤ) (a : ℚ) (hv : ∀ i ≤ D, vge p (f.eval ((y : ℚ) + i)) (-a)) :
    vge p (tau f) (-a - 4 * Nat.log p (D + 1)) := by
  -- the bound spreads from `D + 1` consecutive integers to all integers
  have hall : ∀ m : ℤ, vge p (f.eval (m : ℚ)) (-a) := by
    intro m
    rw [newton f D hD (y : ℚ), eval_finsetSum]
    refine vge_sum _ _ fun k hk => ?_
    rw [eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C]
    obtain ⟨z, hz⟩ := bp_eval_int k (m - y)
    rw [show (m : ℚ) - y = ((m - y : ℤ) : ℚ) by push_cast; ring, hz]
    have h := vge_mul (fd_vge (p := p) f y a k fun i hi => hv i (by simp at hk; omega))
      (vge_int p z)
    simpa using h
  -- Newton at `0`, and `τ(binom(x, k)) = [x⁴] binom(x, k+1)`
  rw [newton f D hD 0]
  simp only [C_0, sub_zero, comp_X]
  rw [tau_sum]
  refine vge_sum _ _ fun k hk => ?_
  rw [tau_C_mul, tau_bp]
  have hfd := fd_vge (p := p) f 0 a k fun i _ => by simpa using hall i
  refine vge_mono (vge_mul hfd (bp_coeff4 (k + 1))) ?_
  have h1 : Nat.log p (k + 1) ≤ Nat.log p (D + 1) := Nat.log_mono_right (by simp at hk; omega)
  have h2 : (Nat.log p (k + 1) : ℚ) ≤ Nat.log p (D + 1) := by exact_mod_cast h1
  linarith

theorem bp_eval_succ (k : ℕ) (u : ℚ) :
    (bp (k + 1)).eval u = u * (((k : ℚ) + 1)⁻¹ * (bp k).eval (u - 1)) := by
  rw [bp_shift]; simp only [eval_mul, eval_C, eval_X, eval_comp, eval_sub, eval_one]; ring

/-- (3.8): difference quotients of integer-valued polynomials. -/
theorem diffQuot_vge (p : ℕ) [Fact p.Prime] (A : ℚ[X]) (hA : IntValuedAt p A) (d : ℕ)
    (hd : A.natDegree ≤ d) (n r : ℤ) (hnr : n ≠ r) :
    vge p ((A.eval (n : ℚ) - A.eval (r : ℚ)) / ((n : ℚ) - r)) (-(Nat.log p (max 1 d) : ℚ)) := by
  set A' := A.comp (X + C (r : ℚ)) with hA'
  have hdeg : A'.natDegree ≤ d :=
    natDegree_comp_le.trans (by rw [natDegree_X_add_C, mul_one]; exact hd)
  have hval : ∀ m : ℤ, vge p (A'.eval (m : ℚ)) 0 := fun m => by
    have h := hA.vge (m + r)
    simp only [hA', eval_comp, eval_add, eval_X, eval_C]
    push_cast at h
    exact h
  have hN := newton A' d hdeg 0
  set u : ℚ := (n : ℚ) - r with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnr)
  have hAn : A.eval (n : ℚ) = A'.eval u := by simp [hA', eval_comp, hu_def]
  have hAr : A.eval (r : ℚ) = A'.eval 0 := by simp [hA', eval_comp]
  rw [hAn, hAr, hN]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_comp, eval_X, sub_zero, C_0]
  rw [← sum_sub_distrib, sum_div]
  refine vge_sum _ _ fun k hk => ?_
  rcases k with _ | k
  · simp only [bp_zero, eval_one, sub_self, zero_div]; exact vge_zero _
  · rw [← mul_sub, bp_eval_succ, bp_eval_succ, zero_mul, sub_zero,
      show fd A' 0 (k + 1) * (u * (((k : ℚ) + 1)⁻¹ * (bp k).eval (u - 1))) / u =
        fd A' 0 (k + 1) * (((k : ℚ) + 1)⁻¹ * (bp k).eval (u - 1)) by field_simp]
    obtain ⟨z, hz⟩ := bp_eval_int k (n - r - 1)
    rw [show u - 1 = ((n - r - 1 : ℤ) : ℚ) by push_cast; ring, hz]
    have h1 := fd_vge (p := p) A' 0 0 (k + 1) fun i _ => by simpa using hval i
    have h2 := vge_inv_nat (p := p) (k + 1) (by omega)
    have h3 := vge_mul h1 (vge_mul h2 (vge_int p z))
    push_cast at h3
    refine vge_mono h3 ?_
    have h4 : Nat.log p (k + 1) ≤ Nat.log p (max 1 d) :=
      Nat.log_mono_right (by simp at hk; omega)
    have h5 : (Nat.log p (k + 1) : ℚ) ≤ Nat.log p (max 1 d) := by exact_mod_cast h4
    linarith

end Zeta5
