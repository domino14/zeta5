import Zeta5.Defs

/-!
# Algebra of the functionals `µ_X` and `τ_X`

Well-definedness (cancelling a common factor), linearity in the numerator, and the pullback
identity (3.1).
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-! ## Polynomial division -/

theorem mul_divByMonic_mul {P R Q : ℚ[X]} (hR : R.Monic) (hQ : Q.Monic) :
    (P * R) /ₘ (R * Q) = P /ₘ Q := by
  refine (div_modByMonic_unique (P /ₘ Q) (R * (P %ₘ Q)) (hR.mul hQ) ⟨?_, ?_⟩).1
  · have := modByMonic_add_div P Q
    linear_combination R * this
  · rw [degree_mul, degree_mul]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hR.ne_zero) (degree_modByMonic_lt _ hQ)

theorem sqPoleProd_monic (S : Finset ℕ) : (sqPoleProd S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem linPoleProd_monic (S : Finset ℤ) : (linPoleProd S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem sq_ne_sq_of_ne {j k : ℕ} (h : j ≠ k) : (k : ℚ) ^ 2 - (j : ℚ) ^ 2 ≠ 0 := by
  intro h0
  have : (k : ℚ) ^ 2 = (j : ℚ) ^ 2 := by linarith
  have := (pow_left_inj₀ (Nat.cast_nonneg k) (Nat.cast_nonneg j) two_ne_zero).mp this
  exact h (by exact_mod_cast this.symm)

/-! ## Cancelling a common factor -/

/-- `µ_X` depends only on the rational function: a common factor `t + j²` cancels. -/
theorem muX_mul_cancel (S : Finset ℕ) (P : ℚ[X]) {j : ℕ} (hj : j ∉ S) :
    muX (insert j S) (P * (X + C ((j : ℚ) ^ 2))) = muX S P := by
  unfold muX
  rw [sqPoleProd, prod_insert hj, ← sqPoleProd,
    mul_divByMonic_mul (monic_X_add_C _) (sqPoleProd_monic S), sum_insert hj]
  have hres_j : sqResidue (insert j S) (P * (X + C ((j : ℚ) ^ 2))) j = 0 := by
    simp [sqResidue]
  have hres : ∀ k ∈ S, sqResidue (insert j S) (P * (X + C ((j : ℚ) ^ 2))) k = sqResidue S P k := by
    intro k hk
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    have hne := sq_ne_sq_of_ne hjk.symm
    unfold sqResidue
    rw [Finset.erase_insert_of_ne hjk, prod_insert (fun h => hj (Finset.mem_of_mem_erase h))]
    simp only [eval_mul, eval_add, eval_X, eval_C]
    have : -(k : ℚ) ^ 2 + (j : ℚ) ^ 2 = (j : ℚ) ^ 2 - (k : ℚ) ^ 2 := by ring
    rw [this, mul_comm (eval _ P), mul_div_mul_left _ _ hne]
  rw [hres_j, C_0, zero_mul, zero_add, sum_congr rfl fun k hk => by rw [hres k hk]]

/-- Cancelling `∏_{j ∈ T} (t + j²)` for `T` disjoint from `S`. -/
theorem muX_mul_cancel_set (T S : Finset ℕ) (hd : Disjoint T S) (P : ℚ[X]) :
    muX (T ∪ S) (P * sqPoleProd T) = muX S P := by
  induction T using Finset.induction_on generalizing P with
  | empty => simp [sqPoleProd]
  | insert a T ha ih =>
    have haS : a ∉ S := Finset.disjoint_left.mp hd (mem_insert_self a T)
    have hd' : Disjoint T S := Finset.disjoint_of_subset_left (subset_insert a T) hd
    rw [insert_union, sqPoleProd, prod_insert ha, ← sqPoleProd,
      show P * ((X + C ((a : ℚ) ^ 2)) * sqPoleProd T) = P * sqPoleProd T * (X + C ((a : ℚ) ^ 2))
        by ring,
      muX_mul_cancel _ _ (by simp [ha, haS]), ih hd']

/-- `τ_X` depends only on the rational function: a common factor `x - r` cancels. -/
theorem tauX_mul_cancel (S : Finset ℤ) (P : ℚ[X]) {r : ℤ} (hr : r ∉ S) :
    tauX (insert r S) (P * (X - C (r : ℚ))) = tauX S P := by
  unfold tauX
  rw [linPoleProd, prod_insert hr, ← linPoleProd,
    mul_divByMonic_mul (monic_X_sub_C _) (linPoleProd_monic S), sum_insert hr]
  have hres_r : linResidue (insert r S) (P * (X - C (r : ℚ))) r = 0 := by
    simp [linResidue]
  have hres : ∀ k ∈ S, linResidue (insert r S) (P * (X - C (r : ℚ))) k = linResidue S P k := by
    intro k hk
    have hrk : r ≠ k := fun h => hr (h ▸ hk)
    have hne : (k : ℚ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hrk.symm)
    unfold linResidue
    rw [Finset.erase_insert_of_ne hrk, prod_insert (fun h => hr (Finset.mem_of_mem_erase h))]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    rw [mul_comm (eval _ P), mul_div_mul_left _ _ hne]
  rw [hres_r, C_0, zero_mul, zero_add, sum_congr rfl fun k hk => by rw [hres k hk]]

theorem tauX_mul_cancel_set (T S : Finset ℤ) (hd : Disjoint T S) (P : ℚ[X]) :
    tauX (T ∪ S) (P * linPoleProd T) = tauX S P := by
  induction T using Finset.induction_on generalizing P with
  | empty => simp [linPoleProd]
  | insert a T ha ih =>
    have haS : a ∉ S := Finset.disjoint_left.mp hd (mem_insert_self a T)
    have hd' : Disjoint T S := Finset.disjoint_of_subset_left (subset_insert a T) hd
    rw [insert_union, linPoleProd, prod_insert ha, ← linPoleProd,
      show P * ((X - C (a : ℚ)) * linPoleProd T) = P * linPoleProd T * (X - C (a : ℚ)) by ring,
      tauX_mul_cancel _ _ (by simp [ha, haS]), ih hd']

theorem tauX_empty (P : ℚ[X]) : tauX ∅ P = C (tau P) := by
  simp [tauX, linPoleProd]

theorem muX_empty (P : ℚ[X]) : muX ∅ P = C (muPoly P) := by
  simp [muX, sqPoleProd]

/-! ## Linearity -/

theorem Lfun_add (P Q : ℚ[X]) : Lfun (P + Q) = Lfun P + Lfun Q := by
  unfold Lfun
  exact sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

theorem Lfun_C_mul (c : ℚ) (P : ℚ[X]) : Lfun (C c * P) = c * Lfun P := by
  unfold Lfun
  rw [← smul_eq_C_mul, sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum, Polynomial.sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Lfun_monomial (n : ℕ) (c : ℚ) : Lfun (monomial n c) = c * _root_.bernoulli n := by
  unfold Lfun
  exact sum_monomial_index _ _ (by simp)

theorem Lfun_C (c : ℚ) : Lfun (C c) = c := by
  rw [← monomial_zero_left, Lfun_monomial]; simp

theorem deriv3 (P : ℚ[X]) : derivative^[3] P = derivative (derivative (derivative P)) := rfl

theorem tau_add (P Q : ℚ[X]) : tau (P + Q) = tau P + tau Q := by
  unfold tau; rw [deriv3, deriv3, deriv3]; simp only [derivative_add, Lfun_add]; ring

theorem tau_C_mul (c : ℚ) (P : ℚ[X]) : tau (C c * P) = c * tau P := by
  unfold tau; rw [deriv3, deriv3]; simp only [derivative_C_mul, Lfun_C_mul]; ring

theorem tau_neg (P : ℚ[X]) : tau (-P) = -tau P := by
  rw [neg_eq_neg_one_mul, ← C_1, ← C_neg, tau_C_mul]; ring

theorem tau_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tau, Lfun]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, tau_add, ih]

/-- `τ(xⁿ) = κ_n = n(n-1)(n-2) B_{n-3}/24`. -/
theorem tau_X_pow (n : ℕ) :
    tau (X ^ n) = (n.descFactorial 3 : ℚ) * _root_.bernoulli (n - 3) / 24 := by
  unfold tau
  rw [iterate_derivative_X_pow_eq_C_mul, C_mul_X_pow_eq_monomial, Lfun_monomial]

theorem tauX_add (S : Finset ℤ) (P Q : ℚ[X]) : tauX S (P + Q) = tauX S P + tauX S Q := by
  unfold tauX linResidue
  rw [add_divByMonic, tau_add, C_add]
  simp only [eval_add, add_div, C_add, add_mul, sum_add_distrib]
  ring

theorem tauX_C_mul (S : Finset ℤ) (c : ℚ) (P : ℚ[X]) : tauX S (C c * P) = C c * tauX S P := by
  unfold tauX linResidue
  rw [← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul, tau_C_mul, C_mul, mul_add, Finset.mul_sum]
  simp only [eval_smul, smul_eq_mul, C_mul, mul_div_assoc]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem tauX_sum (S : Finset ℤ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    tauX S (∑ i ∈ s, f i) = ∑ i ∈ s, tauX S (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := tauX_C_mul S 0 0
    simpa using this
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, tauX_add, ih]

/-! ## The monomial part of the pullback -/

/-- `τ(x⁵ (-x²)ᵉ) = µ(tᵉ)`: three differentiations. -/
theorem tau_pullback_mono (e : ℕ) : tau (X ^ 5 * (-X ^ 2) ^ e) = muMono e := by
  have : (X ^ 5 * (-X ^ 2) ^ e : ℚ[X]) = C ((-1) ^ e) * X ^ (2 * e + 5) := by
    rw [neg_pow, C_pow, C_neg, C_1, ← pow_mul]; ring
  rw [this, tau_C_mul, tau_X_pow, muMono]
  have h3 : (2 * e + 5).descFactorial 3 = (2 * e + 5) * (2 * e + 4) * (2 * e + 3) := by
    simp [Nat.descFactorial]; ring
  rw [h3, show 2 * e + 5 - 3 = 2 * e + 2 by omega]
  push_cast
  ring

theorem muPoly_add (P Q : ℚ[X]) : muPoly (P + Q) = muPoly P + muPoly Q := by
  unfold muPoly
  exact sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

theorem muPoly_monomial (n : ℕ) (c : ℚ) : muPoly (monomial n c) = c * muMono n := by
  unfold muPoly
  exact sum_monomial_index _ _ (by simp)

/-- `τ(x⁵ A(-x²)) = µ(A)` for every polynomial `A`. -/
theorem tau_pullback_poly (A : ℚ[X]) : tau (X ^ 5 * A.comp (-X ^ 2)) = muPoly A := by
  induction A using Polynomial.induction_on' with
  | add P Q hP hQ => rw [add_comp, mul_add, tau_add, hP, hQ, muPoly_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp,
      show (X ^ 5 * (C c * (-X ^ 2) ^ n) : ℚ[X]) = C c * (X ^ 5 * (-X ^ 2) ^ n) by ring,
      tau_C_mul, tau_pullback_mono, C_mul_X_pow_eq_monomial, muPoly_monomial]

/-! ## The pole structure of the pullback -/

/-- The integer poles `±j`, `j ∈ S`, of `x⁵ R(-x²)`. -/
def signedPoles (S : Finset ℕ) : Finset ℤ :=
  S.image (fun j : ℕ => (j : ℤ)) ∪ S.image (fun j : ℕ => -(j : ℤ))

theorem signedPoles_insert (S : Finset ℕ) (j : ℕ) :
    signedPoles (insert j S) = insert (j : ℤ) (insert (-(j : ℤ)) (signedPoles S)) := by
  ext x; simp only [signedPoles, image_insert, mem_union, mem_insert]; tauto

theorem not_mem_signedPoles {S : Finset ℕ} {j : ℕ} (hj : j ∉ S) (hS : 0 ∉ S) (_h0 : j ≠ 0) :
    (j : ℤ) ∉ signedPoles S ∧ -(j : ℤ) ∉ signedPoles S := by
  simp only [signedPoles, mem_union, mem_image]
  constructor
  · rintro (⟨k, hk, hkj⟩ | ⟨k, hk, hkj⟩)
    · have : k = j := by exact_mod_cast hkj
      exact hj (this ▸ hk)
    · have : k = 0 := by omega
      exact hS (this ▸ hk)
  · rintro (⟨k, hk, hkj⟩ | ⟨k, hk, hkj⟩)
    · have : k = 0 := by omega
      exact hS (this ▸ hk)
    · have : k = j := by omega
      exact hj (this ▸ hk)

theorem sqPoleProd_insert {S : Finset ℕ} {j : ℕ} (hj : j ∉ S) :
    sqPoleProd (insert j S) = (X + C ((j : ℚ) ^ 2)) * sqPoleProd S := prod_insert hj

/-- `∏_{r = ±j} (x - r) = (-1)^{|S|} ∏_{j ∈ S} (j² - x²)`. -/
theorem linPoleProd_signedPoles (S : Finset ℕ) (hS : 0 ∉ S) :
    linPoleProd (signedPoles S) = C ((-1) ^ S.card) * (sqPoleProd S).comp (-X ^ 2) := by
  induction S using Finset.induction_on with
  | empty => simp [signedPoles, linPoleProd, sqPoleProd]
  | insert j S hj ih =>
    have hS' : 0 ∉ S := fun h => hS (mem_insert_of_mem h)
    have h0 : j ≠ 0 := fun h => hS (h ▸ mem_insert_self j S)
    obtain ⟨h1, h2⟩ := not_mem_signedPoles hj hS' h0
    have h3 : (j : ℤ) ∉ insert (-(j : ℤ)) (signedPoles S) := by
      simp only [mem_insert, not_or]; exact ⟨by omega, h1⟩
    rw [signedPoles_insert, linPoleProd, prod_insert h3, prod_insert h2, ← linPoleProd, ih hS',
      sqPoleProd_insert hj, card_insert_of_notMem hj, mul_comp, add_comp, X_comp, C_comp]
    simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_pow, map_mul, map_one, pow_succ]
    ring

theorem sqPoleProd_natDegree (S : Finset ℕ) : (sqPoleProd S).natDegree = S.card := by
  rw [sqPoleProd, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  exact (sum_congr rfl fun j _ => natDegree_X_add_C _).trans (by simp)

/-- Lagrange: `P mod ∏(t + j²) = ∑_j res_j ∏_{k ≠ j} (t + k²)`. -/
theorem modByMonic_sqPoleProd (S : Finset ℕ) (P : ℚ[X]) :
    P %ₘ sqPoleProd S = ∑ j ∈ S, C (sqResidue S P j) * sqPoleProd (S.erase j) := by
  classical
  set nodes := S.image fun j : ℕ => -((j : ℚ) ^ 2)
  have hinj : Set.InjOn (fun j : ℕ => -((j : ℚ) ^ 2)) S := by
    intro j _ k _ h
    by_contra hjk
    exact sq_ne_sq_of_ne hjk (by simp only at h; linarith)
  have hcard : nodes.card = S.card := card_image_of_injOn hinj
  apply eq_of_degrees_lt_of_eval_finset_eq nodes
  · rw [hcard]
    calc _ < degree (sqPoleProd S) := degree_modByMonic_lt _ (sqPoleProd_monic S)
      _ = S.card := by rw [degree_eq_natDegree (sqPoleProd_monic S).ne_zero, sqPoleProd_natDegree]
  · rw [hcard, ← mem_degreeLT]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_degreeLT, degree_eq_natDegree (sqPoleProd_monic _).ne_zero, sqPoleProd_natDegree,
      card_erase_of_mem hj]
    have : 0 < S.card := card_pos.mpr ⟨j, hj⟩
    exact_mod_cast Nat.sub_lt this one_pos
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    have hQ : (sqPoleProd S).eval (-((k : ℚ) ^ 2)) = 0 := by
      rw [sqPoleProd, eval_prod]
      exact prod_eq_zero hk (by simp)
    have hmod := modByMonic_add_div P (sqPoleProd S)
    have hl : (P %ₘ sqPoleProd S).eval (-((k : ℚ) ^ 2)) = P.eval (-((k : ℚ) ^ 2)) := by
      conv_rhs => rw [← hmod]
      simp [hQ]
    rw [hl, eval_finsetSum, sum_eq_single k]
    · rw [eval_mul, eval_C, sqResidue, sqPoleProd, eval_prod]
      have hne : ∏ l ∈ S.erase k, ((l : ℚ) ^ 2 - (k : ℚ) ^ 2) ≠ 0 :=
        prod_ne_zero_iff.mpr fun l hl => sq_ne_sq_of_ne (ne_of_mem_erase hl).symm
      have : ∏ l ∈ S.erase k, eval (-((k : ℚ) ^ 2)) (X + C ((l : ℚ) ^ 2)) =
          ∏ l ∈ S.erase k, ((l : ℚ) ^ 2 - (k : ℚ) ^ 2) :=
        prod_congr rfl fun l _ => by simp; ring
      rw [this, div_mul_cancel₀ _ hne]
    · intro j hj hjk
      rw [eval_mul, sqPoleProd, eval_prod,
        prod_eq_zero (mem_erase.mpr ⟨fun h => hjk h.symm, hk⟩) (by simp), mul_zero]
    · intro h; exact absurd hk h

/-! ## The single pole and the pullback identity (3.1) -/

theorem H5_succ (m : ℕ) : H5 (m + 1) = H5 m + 1 / ((m + 1 : ℕ) : ℚ) ^ 5 := by
  unfold H5
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- `τ_X(x⁵/(j² - x²)) = µ_X(1/(t + j²))`: the pole case of (3.1). -/
theorem tauX_single_pole (j : ℕ) (hj : j ≠ 0) :
    tauX {(j : ℤ), -(j : ℤ)} (-X ^ 5) = muPole j := by
  have hj' : (j : ℤ) ≠ -(j : ℤ) := by omega
  have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj
  have hprod : linPoleProd {(j : ℤ), -(j : ℤ)} = X ^ 2 - C ((j : ℚ) ^ 2) := by
    rw [linPoleProd, prod_insert (by simpa using hj'), prod_singleton]
    simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_pow]
    ring
  have hmonic : (X ^ 2 - C ((j : ℚ) ^ 2)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hdiv : (-X ^ 5 : ℚ[X]) /ₘ (X ^ 2 - C ((j : ℚ) ^ 2)) = -X ^ 3 - C ((j : ℚ) ^ 2) * X := by
    refine (div_modByMonic_unique _ (-C ((j : ℚ) ^ 4) * X) hmonic ⟨?_, ?_⟩).1
    · simp only [map_pow]; ring
    · rw [degree_X_pow_sub_C (by norm_num : 0 < 2)]
      calc degree (-C ((j : ℚ) ^ 4) * X) ≤ 1 := by
            rw [← C_neg]; exact degree_C_mul_X_le _
        _ < 2 := by norm_num
  have htau : tau (-X ^ 3 - C ((j : ℚ) ^ 2) * X) = -1 / 4 := by
    have hX : tau (X : ℚ[X]) = 0 := by
      unfold tau; rw [iterate_derivative_X (by norm_num)]; simp [Lfun]
    rw [sub_eq_add_neg, tau_add, tau_neg, ← neg_mul, ← C_neg, tau_C_mul, hX, tau_X_pow]
    simp [Nat.descFactorial]
    norm_num
  have e1 : ({(j : ℤ), -(j : ℤ)} : Finset ℤ).erase (j : ℤ) = {-(j : ℤ)} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega
  have e2 : ({(j : ℤ), -(j : ℤ)} : Finset ℤ).erase (-(j : ℤ)) = {(j : ℤ)} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hd1 : dIdx ((m + 1 : ℕ) : ℤ) = m + 1 := by
    unfold dIdx; split_ifs <;> omega
  have hd2 : dIdx (-((m + 1 : ℕ) : ℤ)) = m := by
    unfold dIdx; split_ifs <;> omega
  unfold tauX linResidue
  rw [hprod, hdiv, htau, sum_insert (by simpa using hj'), sum_singleton, e1, e2, prod_singleton,
    prod_singleton]
  simp only [tauPole, hd1, hd2, H5_succ, muPole]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_neg, eval_pow]
  push_cast
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem sum_comp' {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (q : ℚ[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  simp only [comp, eval₂_finsetSum]

/-- **(3.1)**, the pullback identity `µ_X(R) = τ_X(x⁵ R(-x²))`. Since
`∏_{j ∈ S} (j² - x²) = (-1)^{|S|} ∏_{r = ±j} (x - r)`, the numerator picks up `(-1)^{|S|}`. -/
theorem pullback (S : Finset ℕ) (hS : 0 ∉ S) (P : ℚ[X]) :
    muX S P = tauX (signedPoles S) (C ((-1) ^ S.card) * X ^ 5 * P.comp (-X ^ 2)) := by
  set Q := sqPoleProd S with hQ
  set A := P /ₘ Q with hA
  have hP : P = Q * A + ∑ j ∈ S, C (sqResidue S P j) * sqPoleProd (S.erase j) := by
    rw [← modByMonic_sqPoleProd, hA, add_comm]; exact (modByMonic_add_div P Q).symm
  -- the polynomial part
  have h1 : tauX (signedPoles S) (C ((-1) ^ S.card) * X ^ 5 * (Q * A).comp (-X ^ 2)) =
      C (muPoly A) := by
    have := tauX_mul_cancel_set (signedPoles S) ∅ (disjoint_empty_right _) (X ^ 5 * A.comp (-X ^ 2))
    rw [union_empty, tauX_empty, tau_pullback_poly, linPoleProd_signedPoles S hS] at this
    rw [← this, mul_comp]
    congr 1
    ring
  -- the pole parts
  have h2 : ∀ j ∈ S, tauX (signedPoles S)
      (C ((-1) ^ S.card) * X ^ 5 * (sqPoleProd (S.erase j)).comp (-X ^ 2)) = muPole j := by
    intro j hj
    have hj0 : j ≠ 0 := fun h => hS (h ▸ hj)
    have hS' : 0 ∉ S.erase j := fun h => hS (mem_of_mem_erase h)
    have hsplit : signedPoles S = signedPoles (S.erase j) ∪ {(j : ℤ), -(j : ℤ)} := by
      conv_lhs => rw [← insert_erase hj]
      rw [signedPoles_insert]; ext x; simp only [mem_insert, mem_union, mem_singleton]; tauto
    have hdisj : Disjoint (signedPoles (S.erase j)) {(j : ℤ), -(j : ℤ)} := by
      obtain ⟨h1, h2⟩ := not_mem_signedPoles (notMem_erase j S) hS' hj0
      rw [disjoint_right]; intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [h1, h2]
    have hcard : S.card = (S.erase j).card + 1 := (card_erase_add_one hj).symm
    have := tauX_mul_cancel_set (signedPoles (S.erase j)) {(j : ℤ), -(j : ℤ)} hdisj (-X ^ 5)
    rw [tauX_single_pole j hj0, ← hsplit, linPoleProd_signedPoles _ hS'] at this
    rw [← this, hcard, pow_succ]
    congr 1
    simp only [map_mul, map_neg, map_one]
    ring
  conv_rhs => rw [hP]
  rw [add_comp, mul_add, tauX_add, h1, sum_comp', Finset.mul_sum, tauX_sum]
  unfold muX
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_comp, C_comp,
    show C ((-1) ^ S.card) * X ^ 5 * (C (sqResidue S P j) * (sqPoleProd (S.erase j)).comp (-X ^ 2))
      = C (sqResidue S P j) * (C ((-1) ^ S.card) * X ^ 5 * (sqPoleProd (S.erase j)).comp (-X ^ 2))
      by ring, tauX_C_mul, h2 j hj]

/-! ## Linearity of `µ_X` -/

theorem muPoly_C_mul (c : ℚ) (P : ℚ[X]) : muPoly (C c * P) = c * muPoly P := by
  unfold muPoly
  rw [← smul_eq_C_mul, sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum, Polynomial.sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem muX_add (S : Finset ℕ) (P Q : ℚ[X]) : muX S (P + Q) = muX S P + muX S Q := by
  unfold muX sqResidue
  rw [add_divByMonic, muPoly_add, C_add]
  simp only [eval_add, add_div, C_add, add_mul, sum_add_distrib]
  ring

theorem muX_C_mul (S : Finset ℕ) (c : ℚ) (P : ℚ[X]) : muX S (C c * P) = C c * muX S P := by
  unfold muX sqResidue
  rw [← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul, muPoly_C_mul, C_mul, mul_add, Finset.mul_sum]
  simp only [eval_smul, smul_eq_mul, C_mul, mul_div_assoc]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem muX_sum (S : Finset ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    muX S (∑ i ∈ s, f i) = ∑ i ∈ s, muX S (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := muX_C_mul S 0 0
    simpa using this
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, muX_add, ih]

end Zeta5