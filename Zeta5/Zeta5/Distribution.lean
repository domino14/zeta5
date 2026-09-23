import Zeta5.PadicTau
import Zeta5.Lemma33

/-!
# Lemma 3.2: the distribution formula (3.7)

`τ_X(g) = p⁻⁴ ∑_{a<p} τ_Y^{ext}(g(a + p x))` with `Y = p⁵ X + C_p`.

* Poles: `∑_{a<p} τ_Y^{ext}(1/(r - a)/p-pole) = p⁵ (H_{d(r)} - X)`, by induction on `r` using the
  far-pole difference identity `tauAnPole_sub`.
* Polynomials: Raabe's multiplication formula `∑_{a<p} τ(Q(a + p x)) = p⁴ τ(Q)`.
* Partial fractions are compatible with the substitution `x = a + p z`.
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ## Harmonic increments -/

theorem H5_dIdx_sub (n : ℤ) :
    H5 (dIdx n) - H5 (dIdx (n - 1)) = if n = 0 then 0 else 1 / (n : ℚ) ^ 5 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    have h1 : dIdx n = m := by unfold dIdx; split_ifs <;> omega
    have h2 : dIdx (n - 1) = m + 1 := by unfold dIdx; split_ifs <;> omega
    rw [h1, h2, H5_succ, if_neg (by omega), hm]
    push_cast
    have : ((m : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · simp [dIdx]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    have h1 : dIdx n = m + 1 := by unfold dIdx; split_ifs <;> omega
    have h2 : dIdx (n - 1) = m := by unfold dIdx; split_ifs <;> omega
    rw [h1, h2, H5_succ, if_neg (by omega), hm]
    push_cast
    ring

section Poles

variable (p : ℕ) [hp : Fact p.Prime]

/-- The scalar part of `τ_Y^{ext}(1/(z - n/p))`. -/
def phi (n : ℤ) : ℚ_[p] :=
  if (p : ℤ) ∣ n then ((H5 (dIdx (n / p)) : ℚ) : ℚ_[p]) - Cp p else tauAnPole p ((n : ℚ) / p)

theorem p_ne_zero_q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

theorem phi_sub (n : ℤ) :
    phi p n - phi p (n - p) =
      (p : ℚ_[p]) ^ 5 * (((H5 (dIdx n) - H5 (dIdx (n - 1)) : ℚ)) : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [H5_dIdx_sub]
  unfold phi
  by_cases hd : (p : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hd' : (p : ℤ) ∣ (p : ℤ) * m - p := ⟨m - 1, by ring⟩
    rw [if_pos ⟨m, rfl⟩, if_pos hd']
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [Int.mul_ediv_cancel_left _ hpz, show (p : ℤ) * m - p = p * (m - 1) by ring,
      Int.mul_ediv_cancel_left _ hpz]
    have := H5_dIdx_sub m
    by_cases hm : m = 0
    · subst hm; simp [dIdx]
    · rw [if_neg (mul_ne_zero hpz hm)]
      rw [if_neg hm] at this
      rw [sub_sub_sub_cancel_right, ← Rat.cast_sub, this]
      push_cast
      field_simp
  · have hd' : ¬ (p : ℤ) ∣ n - p := fun h => hd (by simpa using dvd_add h (dvd_refl (p : ℤ)))
    rw [if_neg hd, if_neg hd']
    have hn0 : n ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
    rw [if_neg hn0]
    have hs : padicValRat p ((n : ℚ) / p) < 0 := by
      rw [padicValRat.div (by exact_mod_cast hn0) (p_ne_zero_q p), padicValRat.of_int,
        padicValInt.eq_zero_of_not_dvd hd, padicValRat.self hp.out.one_lt]
      norm_num
    have e : ((n - p : ℤ) : ℚ) / p = (n : ℚ) / p - 1 := by
      rw [Int.cast_sub, Int.cast_natCast, sub_div, div_self (p_ne_zero_q p)]
    rw [e, tauAnPole_sub p _ hs (div_ne_zero (by exact_mod_cast hn0) (p_ne_zero_q p))]
    push_cast
    rw [zpow_neg]
    field_simp

/-- `G(r) = ∑_{a<p} φ(r - a)`. -/
def Gsum (r : ℤ) : ℚ_[p] := ∑ a ∈ range p, phi p (r - a)

theorem Gsum_step (n : ℤ) : Gsum p n - Gsum p (n - 1) = phi p n - phi p (n - p) := by
  unfold Gsum
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hr : range p = range (q + 1) := by rw [hq]
  have hpq : (p : ℤ) = q + 1 := by exact_mod_cast hq
  rw [hr, sum_range_succ', sum_range_succ, hpq]
  simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, sub_zero]
  have : ∀ i ∈ range q, phi p (n - ((i : ℤ) + 1)) = phi p (n - 1 - i) := fun i _ => by
    congr 1; ring
  rw [sum_congr rfl this]
  have e : n - 1 - (q : ℤ) = n - ((q : ℤ) + 1) := by ring
  rw [e]
  ring

theorem Gsum_zero : Gsum p 0 = 0 := by
  unfold Gsum
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hsplit : ∑ a ∈ range p, phi p ((0 : ℤ) - a) = phi p 0 + ∑ a ∈ Ico 1 p, phi p (-(a : ℤ)) := by
    have hr : range p = range (q + 1) := by rw [hq]
    have hI : Ico 1 p = Ico 1 (q + 1) := by rw [hq]
    rw [hr, hI, sum_range_succ', sum_Ico_eq_sum_range]
    simp only [Nat.sub_zero, zero_sub, Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, sub_zero]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i _ => by push_cast; ring_nf
  rw [hsplit]
  have h0 : phi p 0 = -Cp p := by simp [phi, dIdx, H5]
  have h1 : ∀ a ∈ Ico 1 p, phi p (-(a : ℤ)) = tauAnPole p (-(a : ℚ) / p) := by
    intro a ha
    rw [mem_Ico] at ha
    have hnd : ¬ (p : ℤ) ∣ -(a : ℤ) := by
      rw [dvd_neg]; intro h
      have := Int.le_of_dvd (by omega) h
      omega
    simp only [phi, if_neg hnd]; push_cast; rfl
  rw [h0, sum_congr rfl h1, Cp]
  ring

theorem Gsum_eq (r : ℤ) : Gsum p r = (p : ℚ_[p]) ^ 5 * ((H5 (dIdx r) : ℚ) : ℚ_[p]) := by
  induction r using Int.induction_on with
  | zero => rw [Gsum_zero]; simp [dIdx, H5]
  | succ i ih =>
    have h := Gsum_step p ((i : ℤ) + 1)
    rw [phi_sub, show (i : ℤ) + 1 - 1 = i by ring] at h
    rw [show Gsum p ((i : ℤ) + 1) = Gsum p i + _ from eq_add_of_sub_eq' h, ih]
    push_cast; ring
  | pred i ih =>
    have h := Gsum_step p (-(i : ℤ))
    rw [phi_sub, show -(i : ℤ) - 1 = -(i : ℤ) - 1 by ring] at h
    have h2 : Gsum p (-(i : ℤ) - 1) = Gsum p (-(i : ℤ)) - (p : ℚ_[p]) ^ 5 *
        ((H5 (dIdx (-(i : ℤ))) - H5 (dIdx (-(i : ℤ) - 1)) : ℚ) : ℚ_[p]) := by rw [← h]; ring
    rw [h2, ih]; push_cast; ring

theorem tauPoleP_eq (n : ℤ) :
    tauPoleP p (Yp p) ((n : ℚ) / p) =
      C (phi p n) - (if (p : ℤ) ∣ n then C ((p : ℚ_[p]) ^ 5) * X else 0) := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold tauPoleP phi
  by_cases hd : (p : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have e : (((p : ℤ) * m : ℤ) : ℚ) / p = (m : ℚ) := by
      push_cast; field_simp [p_ne_zero_q p]
    rw [e, if_pos (Rat.den_intCast m), if_pos ⟨m, rfl⟩, if_pos ⟨m, rfl⟩,
      Int.mul_ediv_cancel_left _ hpz, Rat.num_intCast, Yp]
    simp only [map_sub]
    ring
  · have hden : ((n : ℚ) / p).den ≠ 1 := by
      intro h1
      have h2 := Rat.coe_int_num_of_den_eq_one h1
      have : (n : ℚ) = p * ((n : ℚ) / p).num := by
        rw [h2]; field_simp [p_ne_zero_q p]
      exact hd ⟨_, by exact_mod_cast this⟩
    rw [if_neg hden, if_neg hd, if_neg hd, sub_zero]

theorem sum_tauPoleP (r : ℤ) :
    ∑ a ∈ range p, tauPoleP p (Yp p) (((r : ℚ) - a) / p) =
      C ((p : ℚ_[p]) ^ 5) * (C (((H5 (dIdx r) : ℚ)) : ℚ_[p]) - X) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have e : ∀ a ∈ range p, tauPoleP p (Yp p) (((r : ℚ) - a) / p) =
      C (phi p (r - a)) - (if a = (r % p).toNat then C ((p : ℚ_[p]) ^ 5) * X else 0) := by
    intro a ha
    have ha' : (a : ℤ) < p := by exact_mod_cast mem_range.mp ha
    rw [show ((r : ℚ) - a) = ((r - a : ℤ) : ℚ) by push_cast; ring, tauPoleP_eq]
    congr 2
    have hiff : (p : ℤ) ∣ r - a ↔ a = (r % p).toNat := by
      rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd r (dvd_refl (p : ℤ)),
        ← Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_emod_of_dvd r (dvd_refl (p : ℤ)),
        Int.emod_eq_of_lt (by omega) ha']
      have h1 := Int.emod_nonneg r (ne_of_gt hp0)
      omega
    simp only [hiff]
  rw [sum_congr rfl e, sum_sub_distrib, ← map_sum, sum_ite_eq' (range p), if_pos]
  · change C (Gsum p r) - _ = _
    rw [Gsum_eq, C_mul]; ring
  · rw [mem_range]
    have h1 := Int.emod_lt_of_pos r hp0
    have h2 := Int.emod_nonneg r (ne_of_gt hp0)
    omega

end Poles

/-! ## Partial fractions for `τ^ext` -/

section Decomp

variable {p : ℕ} [hp : Fact p.Prime]

theorem natDegree_prod_X_sub_C {K : Type*} [Field K] (T : Finset ℤ) (g : ℤ → K) :
    (∏ r ∈ T, (X - C (g r))).natDegree = T.card := by
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  exact (sum_congr rfl fun j _ => natDegree_X_sub_C _).trans (by simp)

/-- `τ^ext` of a rational function given by an explicit partial fraction decomposition. -/
theorem tauExtP_decomp (Y : ℚ_[p][X]) (S : Finset ℤ) (f : ℤ → ℚ) (hf : Function.Injective f)
    (Q' : ℚ_[p][X]) (ρ : ℤ → ℚ_[p]) (U : ℚ_[p][X])
    (hU : U = Q' * ∏ r ∈ S, (X - C ((f r : ℚ) : ℚ_[p])) +
      ∑ r ∈ S, C (ρ r) * ∏ r' ∈ S.erase r, (X - C ((f r' : ℚ) : ℚ_[p]))) :
    tauExtP p Y U (S.image f) = C (tauP p Q') + ∑ r ∈ S, C (ρ r) * tauPoleP p Y (f r) := by
  classical
  set g : ℤ → ℚ_[p] := fun r => ((f r : ℚ) : ℚ_[p])
  have hg : Function.Injective g := fun a b h => hf (Rat.cast_injective h)
  have hPi : ∏ s ∈ S.image f, (X - C (s : ℚ_[p])) = ∏ r ∈ S, (X - C (g r)) :=
    prod_image fun a _ b _ h => hf h
  have hmon : (∏ r ∈ S, (X - C (g r))).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  set R := ∑ r ∈ S, C (ρ r) * ∏ r' ∈ S.erase r, (X - C (g r'))
  have hRdeg : R.degree < (∏ r ∈ S, (X - C (g r))).degree := by
    rw [degree_eq_natDegree hmon.ne_zero, natDegree_prod_X_sub_C, ← mem_degreeLT]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_degreeLT, degree_eq_natDegree (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).ne_zero,
      natDegree_prod_X_sub_C, card_erase_of_mem hj]
    have : 0 < S.card := card_pos.mpr ⟨j, hj⟩
    exact_mod_cast Nat.sub_lt this one_pos
  have hdiv : U /ₘ ∏ r ∈ S, (X - C (g r)) = Q' :=
    (div_modByMonic_unique Q' R hmon ⟨by rw [hU]; ring, hRdeg⟩).1
  have hres : ∀ r ∈ S, U.eval (g r) / ∏ r' ∈ S.erase r, (g r - g r') = ρ r := by
    intro r hr
    have hne : ∏ r' ∈ S.erase r, (g r - g r') ≠ 0 :=
      prod_ne_zero_iff.mpr fun r' hr' => sub_ne_zero.mpr fun h => (ne_of_mem_erase hr') (hg h).symm
    have hev : U.eval (g r) = ρ r * ∏ r' ∈ S.erase r, (g r - g r') := by
      rw [hU, eval_add, eval_mul, eval_prod, prod_eq_zero hr (by simp [g]), mul_zero, zero_add,
        eval_finsetSum, sum_eq_single r]
      · rw [eval_mul, eval_C, eval_prod]; simp [g]
      · intro b hb hbr
        rw [eval_mul, eval_prod, prod_eq_zero (mem_erase.mpr ⟨fun h => hbr h.symm, hr⟩) (by simp [g]),
          mul_zero]
      · intro h; exact absurd hr h
    rw [hev, mul_div_cancel_right₀ _ hne]
  unfold tauExtP
  rw [hPi, hdiv, sum_image fun a _ b _ h => hf h]
  congr 1
  refine sum_congr rfl fun r hr => ?_
  have herase : (S.image f).erase (f r) = (S.erase r).image f := (image_erase hf _ _).symm
  rw [herase, prod_image fun a _ b _ h => hf h]
  exact congrArg (fun c => C c * tauPoleP p Y (f r)) (hres r hr)

end Decomp

/-! ## Raabe's multiplication formula -/

/-- Every polynomial is a forward difference. -/
theorem exists_antidiff (f : ℚ[X]) : ∃ g : ℚ[X], g.comp (X + 1) - g = f := by
  have hN := newton f f.natDegree le_rfl 0
  simp only [C_0, sub_zero, comp_X] at hN
  refine ⟨∑ k ∈ range (f.natDegree + 1), C (fd f 0 k) * bp (k + 1), ?_⟩
  rw [sum_comp', ← sum_sub_distrib]
  conv_rhs => rw [hN]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_comp, C_comp, ← mul_sub, bp_fwd]

theorem Lfun_raabe (p : ℕ) (f : ℚ[X]) :
    ∑ a ∈ range p, Lfun (f.comp (C (a : ℚ) + C (p : ℚ) * X)) = p * Lfun f := by
  obtain ⟨g, rfl⟩ := exists_antidiff f
  have e : ∀ a : ℕ, (g.comp (X + 1) - g).comp (C (a : ℚ) + C (p : ℚ) * X) =
      g.comp (C ((a + 1 : ℕ) : ℚ) + C (p : ℚ) * X) - g.comp (C (a : ℚ) + C (p : ℚ) * X) := by
    intro a
    rw [sub_comp, comp_assoc]
    congr 2
    simp only [add_comp, X_comp, one_comp]
    push_cast; simp only [map_add, map_one]; ring
  simp only [e, Lfun_sub]
  rw [sum_range_sub (fun a => Lfun (g.comp (C (a : ℚ) + C (p : ℚ) * X)))]
  set G := g.comp (C (p : ℚ) * X)
  have h1 : g.comp (C ((p : ℕ) : ℚ) + C (p : ℚ) * X) = G.comp (X + 1) := by
    simp only [G, comp_assoc, mul_comp, C_comp, add_comp, X_comp, one_comp]
    congr 1; ring
  have h2 : g.comp (C ((0 : ℕ) : ℚ) + C (p : ℚ) * X) = G := by simp [G]
  rw [h1, h2, ← Lfun_sub, ← Lfun_sub, Lfun_fwd, Lfun_fwd]
  simp only [G, derivative_comp, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
    mul_one, eval_mul, eval_C, eval_comp, eval_X, mul_zero]

theorem derivative_comp_affine (Q : ℚ[X]) (a c : ℚ) :
    derivative (Q.comp (C a + C c * X)) = C c * (derivative Q).comp (C a + C c * X) := by
  rw [derivative_comp]; simp

theorem tau_raabe (p : ℕ) (Q : ℚ[X]) :
    ∑ a ∈ range p, tau (Q.comp (C (a : ℚ) + C (p : ℚ) * X)) = (p : ℚ) ^ 4 * tau Q := by
  have e : ∀ a : ℕ, tau (Q.comp (C (a : ℚ) + C (p : ℚ) * X)) =
      (p : ℚ) ^ 3 * Lfun ((derivative^[3] Q).comp (C (a : ℚ) + C (p : ℚ) * X)) / 24 := by
    intro a
    unfold tau
    simp only [deriv3, derivative_comp_affine, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, Lfun_C_mul]
    ring
  simp only [e]
  rw [← sum_div, ← mul_sum, Lfun_raabe]
  unfold tau
  ring

theorem tau_eq_sum_kappa (f : ℚ[X]) : tau f = f.sum fun n c => c * kappa n := by
  induction f using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [tau_add, hP, hQ, sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)]
  | monomial n c =>
    rw [sum_monomial_index _ _ (by simp), ← C_mul_X_pow_eq_monomial, tau_C_mul, tau_X_pow]
    congr 1
    unfold kappa
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp [Nat.descFactorial]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      simp only [Nat.descFactorial, Nat.add_sub_cancel]
      push_cast
      ring

theorem tauP_map_dist {p : ℕ} [Fact p.Prime] (f : ℚ[X]) :
    tauP p (f.map (algebraMap ℚ ℚ_[p])) = ((tau f : ℚ) : ℚ_[p]) := by
  rw [tau_eq_sum_kappa]
  induction f using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.map_add, tauP, sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring),
      ← tauP, ← tauP, hP, hQ, sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)]
    push_cast; ring
  | monomial n c =>
    rw [Polynomial.map_monomial, tauP, sum_monomial_index _ _ (by simp),
      sum_monomial_index _ _ (by simp)]
    push_cast; rfl

/-! ## Assembly -/

theorem sum_comp_gen {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (q : R[X]) : (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  simp only [comp, eval₂_finsetSum]

section Assembly

variable (p : ℕ) [hp : Fact p.Prime]

/-- `(∏_{r ∈ T}(x - r))(a + p z) = p^{|T|} ∏_{r ∈ T}(z - (r - a)/p)`. -/
theorem linPoleProd_distrib (a : ℕ) (T : Finset ℤ) :
    ((linPoleProd T).map (algebraMap ℚ ℚ_[p])).comp (C (a : ℚ_[p]) + C (p : ℚ_[p]) * X) =
      C ((p : ℚ_[p]) ^ T.card) *
        ∏ r ∈ T, (X - C (((((r : ℚ) - a) / p : ℚ)) : ℚ_[p])) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [linPoleProd, Polynomial.map_prod, Polynomial.prod_comp, C_pow, ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun r _ => ?_
  simp only [Polynomial.map_sub, map_X, Polynomial.map_C, sub_comp, X_comp, C_comp]
  rw [mul_sub, ← C_mul]
  have : (p : ℚ_[p]) * ((((r : ℚ) - a) / p : ℚ) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) r - a := by
    push_cast; field_simp; simp [eq_ratCast]
  rw [this, C_sub]
  ring

theorem distrib_inj (a : ℕ) : Function.Injective fun r : ℤ => ((r : ℚ) - a) / p := by
  intro x y h
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero_q p
  simp only at h
  have := (div_left_inj' hp0).mp h
  exact_mod_cast sub_left_injective this

theorem summand_eq (S : Finset ℤ) (P : ℚ[X]) (a : ℕ) :
    tauExtP p (Yp p) (distribNum p S P a) (distribPoles p S a) =
      C (((tau ((P /ₘ linPoleProd S).comp (C (a : ℚ) + C (p : ℚ) * X)) : ℚ) : ℚ_[p])) +
        ∑ r ∈ S, C (((linResidue S P r : ℚ) : ℚ_[p]) * (p : ℚ_[p])⁻¹) *
          tauPoleP p (Yp p) (((r : ℚ) - a) / p) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set ι := algebraMap ℚ ℚ_[p]
  set Q := P /ₘ linPoleProd S
  have hP : P = Q * linPoleProd S +
      ∑ r ∈ S, C (linResidue S P r) * linPoleProd (S.erase r) := by
    calc P = P %ₘ linPoleProd S + linPoleProd S * Q := (modByMonic_add_div P _).symm
      _ = _ := by rw [modByMonic_linPoleProd]; ring
  have hmapcomp : (Q.comp (C (a : ℚ) + C (p : ℚ) * X)).map ι =
      (Q.map ι).comp (C (a : ℚ_[p]) + C (p : ℚ_[p]) * X) := by
    rw [Polynomial.map_comp]; simp [ι]
  have hU : distribNum p S P a =
      (Q.comp (C (a : ℚ) + C (p : ℚ) * X)).map ι *
        ∏ r ∈ S, (X - C (((((r : ℚ) - a) / p : ℚ)) : ℚ_[p])) +
      ∑ r ∈ S, C ((ι (linResidue S P r)) * (p : ℚ_[p])⁻¹) *
        ∏ r' ∈ S.erase r, (X - C (((((r' : ℚ) - a) / p : ℚ)) : ℚ_[p])) := by
    unfold distribNum
    conv_lhs => rw [hP]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sum, add_comp, mul_comp,
      linPoleProd_distrib, sum_comp_gen, mul_add, hmapcomp, Finset.mul_sum]
    have k1 : C ((p : ℚ_[p]) ^ (-(S.card : ℤ))) * C ((p : ℚ_[p]) ^ S.card) = 1 := by
      rw [← C_mul, ← zpow_natCast, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, C_1]
    have k2 : ∀ r ∈ S, C ((p : ℚ_[p]) ^ (-(S.card : ℤ))) * C ((p : ℚ_[p]) ^ (S.card - 1)) =
        C ((p : ℚ_[p])⁻¹) := by
      intro r hr
      have hn : 1 ≤ S.card := card_pos.mpr ⟨r, hr⟩
      rw [← C_mul, ← zpow_natCast, ← zpow_add₀ hp0, Nat.cast_sub hn, ← zpow_neg_one]
      congr 2; push_cast; ring
    congr 1
    · linear_combination ((Polynomial.map ι Q).comp (C (a : ℚ_[p]) + C (p : ℚ_[p]) * X) *
        ∏ r ∈ S, (X - C (((((r : ℚ) - a) / p : ℚ)) : ℚ_[p]))) * k1
    · refine sum_congr rfl fun r hr => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, mul_comp, C_comp, linPoleProd_distrib,
        card_erase_of_mem hr, C_mul]
      linear_combination (C (ι (linResidue S P r)) *
        ∏ r' ∈ S.erase r, (X - C (((((r' : ℚ) - a) / p : ℚ)) : ℚ_[p]))) * k2 r hr
  rw [hU]
  unfold distribPoles
  rw [tauExtP_decomp (p := p) (Yp p) S _ (distrib_inj p a) _ _ _ rfl, tauP_map_dist]
  simp only [ι, eq_ratCast]

theorem lemma_3_2_proof (S : Finset ℤ) (P : ℚ[X]) :
    (tauX S P).map (algebraMap ℚ ℚ_[p]) =
      C ((p : ℚ_[p]) ^ (-4 : ℤ)) *
        ∑ a ∈ range p, tauExtP p (Yp p) (distribNum p S P a) (distribPoles p S a) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [summand_eq]
  rw [sum_add_distrib, sum_comm, ← map_sum]
  have hR : ∑ x ∈ range p, (((tau ((P /ₘ linPoleProd S).comp (C (x : ℚ) + C (p : ℚ) * X)) : ℚ)) :
      ℚ_[p]) = (p : ℚ_[p]) ^ 4 * ((tau (P /ₘ linPoleProd S) : ℚ) : ℚ_[p]) := by
    rw [← Rat.cast_sum, tau_raabe]; push_cast; ring
  have hpoles : ∀ r ∈ S, ∑ x ∈ range p, C (((linResidue S P r : ℚ) : ℚ_[p]) * (p : ℚ_[p])⁻¹) *
      tauPoleP p (Yp p) (((r : ℚ) - x) / p) =
      C (((linResidue S P r : ℚ) : ℚ_[p]) * (p : ℚ_[p]) ^ 4) *
        (C (((H5 (dIdx r) : ℚ)) : ℚ_[p]) - X) := by
    intro r _
    rw [← mul_sum, sum_tauPoleP, ← mul_assoc, ← C_mul]
    congr 2
    field_simp
  rw [hR, sum_congr rfl hpoles]
  unfold tauX tauPole
  simp only [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, map_X, mul_add, Finset.mul_sum]
  congr 1
  · rw [← C_mul]; congr 1
    simp only [eq_ratCast, zpow_neg]
    field_simp
  · refine sum_congr rfl fun r _ => ?_
    rw [← mul_assoc, ← C_mul, zpow_neg]
    congr 2
    rw [show ((p : ℚ_[p]) ^ (4 : ℤ)) = (p : ℚ_[p]) ^ 4 by norm_cast]
    field_simp
    rfl

end Assembly

/-- **Lemma 3.2**, the distribution formula (3.7). -/
theorem lemma_3_2' (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (S : Finset ℤ) (P : ℚ[X]) :
    (tauX S P).map (algebraMap ℚ ℚ_[p]) =
      C ((p : ℚ_[p]) ^ (-4 : ℤ)) *
        ∑ a ∈ range p, tauExtP p (Yp p) (distribNum p S P a) (distribPoles p S a) :=
  lemma_3_2_proof p S P

end Zeta5