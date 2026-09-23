import Zeta5.Section5

/-!
# Proposition 5.1: `Q_{K,M} ∈ ℤ[X]`

At each prime, the exponent `L_p(K, M)` of (5.1) is covered by (3.12), Proposition 4.1 or
Proposition 4.3.
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-- A rational number that is `p`-integral at every prime is an integer. -/
theorem den_eq_one_of_vge {q : ℚ} (h : ∀ p : ℕ, p.Prime → vge p q 0) : q.den = 1 := by
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  haveI := Fact.mk hp
  have hq : q ≠ 0 := by rintro rfl; simp at hd
  have hv := h p hp hq
  rw [padicValRat_def] at hv
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have hc : Nat.Coprime p q.den := Nat.Coprime.coprime_dvd_left h1 q.reduced
    exact hp.one_lt.ne' (hc.eq_one_of_dvd hpd)
  rw [padicValInt.eq_zero_of_not_dvd hnum] at hv
  have h1 := one_le_padicValNat_of_dvd q.den_nz hpd
  have hv' : (0 : ℤ) ≤ 0 - (padicValNat p q.den : ℤ) := by exact_mod_cast hv
  omega

/-- A rational polynomial that is `p`-integral at every prime has integer coefficients. -/
theorem intPoly_of_vge (Q : ℚ[X]) (h : ∀ p : ℕ, p.Prime → vpGge p Q 0) :
    ∃ P : ℤ[X], P.map (algebraMap ℤ ℚ) = Q := by
  have hl : Q ∈ lifts (algebraMap ℤ ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨(Q.coeff n).num, ?_⟩
    have hd := den_eq_one_of_vge (q := Q.coeff n) fun p hp => by haveI := Fact.mk hp; exact h p hp n
    simpa using Rat.coe_int_num_of_den_eq_one hd
  exact hl

variable {p : ℕ} [hp : Fact p.Prime]

theorem vpGge_C_mul_val {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} {b : ℚ} (h : vpGge p P b) :
    vpGge p (C a * P) (padicValRat p a + b) :=
  vpGge_mul (vpGge_C fun _ => le_refl _) h

theorem S_pos (K : ℕ) : 0 < S K := by
  unfold S
  positivity

theorem padicValRat_mKM (K M : ℕ) :
    padicValRat p (mKM K M) = if p ≤ 2 * hof K then -Lp K M p else 0 := by
  unfold mKM
  have hne : ∀ q ∈ (range (2 * hof K + 1)).filter Nat.Prime, ((q : ℚ) ^ (-Lp K M q)) ≠ 0 :=
    fun q hq => zpow_ne_zero _ (by exact_mod_cast (mem_filter.mp hq).2.ne_zero)
  rw [padicValRat_prod _ _ hne]
  have hval : ∀ q ∈ (range (2 * hof K + 1)).filter Nat.Prime,
      padicValRat p ((q : ℚ) ^ (-Lp K M q)) = if q = p then -Lp K M p else 0 := by
    intro q hq
    rw [padicValRat.zpow, padicValRat.of_nat]
    have hqp := (mem_filter.mp hq).2
    split_ifs with hqp'
    · subst hqp'; rw [padicValNat_self]; simp
    · haveI := Fact.mk hqp; rw [padicValNat_primes (Ne.symm hqp')]; simp
  rw [sum_congr rfl hval, sum_ite_eq']
  simp only [mem_filter, mem_range, hp.out, and_true]
  split_ifs <;> first | rfl | omega

theorem S_vge_large (K : ℕ) (hp2h : 2 * hof K < p) : (0 : ℚ) ≤ padicValRat p (S K) := by
  have hN : Nof K < p := by unfold Nof hof at *; omega
  set A : ℕ := K.factorial ^ (2 * hof K) * 4 ^ (hof K - 1)
  set B : ℕ := (Nof K).factorial ^ (12 * hof K) * ∏ i ∈ Icc 1 (hof K - 1), (2 * i).factorial ^ 2
  have hS : S K = (A : ℚ) / B := by unfold S; simp only [A, B]; push_cast; ring
  have hA : (A : ℚ) ≠ 0 := by positivity
  have hB : (B : ℚ) ≠ 0 := by positivity
  have hBp : ¬ p ∣ B := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · have := (Nat.Prime.dvd_factorial hp.out).mp (hp.out.dvd_of_dvd_pow h1); omega
    · obtain ⟨i, hi, h2⟩ := (Prime.dvd_finset_prod_iff hp.out.prime _).mp h1
      have := (Nat.Prime.dvd_factorial hp.out).mp (hp.out.dvd_of_dvd_pow h2)
      rw [mem_Icc] at hi; omega
  rw [hS, padicValRat.div hA hB, padicValRat.of_nat, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hBp]
  simp

/-- **Proposition 5.1**: `Q_{K,M} ∈ ℤ[X]`. -/
theorem prop_5_1 {K M : ℕ} (h : StdHyp K M) : ∃ P : ℤ[X], P.map (algebraMap ℤ ℚ) = Q K M := by
  apply intPoly_of_vge
  intro p hpp
  haveI := Fact.mk hpp
  obtain ⟨hM, hK40, hK0, hKM⟩ := h
  have hm0 : mKM K M ≠ 0 := (mKM_pos K M).ne'
  have hS0 : S K ≠ 0 := (S_pos K).ne'
  have hvm := padicValRat_mKM (p := p) K M
  unfold Q
  by_cases hp2h : p ≤ 2 * hof K
  · rw [if_pos hp2h] at hvm
    unfold Lp at hvm
    split_ifs at hvm with h1 h2 h3
    · -- small primes: (3.12)
      have hF := vpG_F_ge p K hK40
      refine vpGge_mono (vpGge_C_mul_val hm0 hF) (le_of_eq ?_)
      have h24 : (padicValRat p 24 : ℚ) = (padicValNat p 24 : ℚ) := by
        rw [show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, Int.cast_natCast]
      rw [hvm]; push_cast; rw [h24]; ring
    · -- inner range: Proposition 4.1
      have hΔ := prop_4_1 (p := p) ⟨hM, hK40, hK0, hKM, by push Not at h1; exact h1, h2⟩
      unfold F
      refine vpGge_mono (vpGge_C_mul_val hm0 (vpGge_C_mul_val hS0 hΔ)) ?_
      rw [hvm]; unfold vpS; push_cast
      have := Int.floor_le (gammaIn K M p)
      linarith
    · -- outer range: Proposition 4.3
      push Not at h1 h2
      have hΔ := prop_4_3 (p := p) hK40 (outer_hyp_of_range hM hK40 hKM hpp h2 h3)
      unfold F
      refine vpGge_mono (vpGge_C_mul_val hm0 (vpGge_C_mul_val hS0 hΔ)) (le_of_eq ?_)
      rw [hvm]; unfold vpS; push_cast; ring
    · -- `p > K`
      push Not at h3
      have hΔ := prop_4_3_large (p := p) hK40 h3
      unfold F
      refine vpGge_mono (vpGge_C_mul_val hm0 (vpGge_C_mul_val hS0 hΔ)) (le_of_eq ?_)
      rw [hvm]; unfold vpS; push_cast; ring
  · -- `p > 2h`: no normalisation, `S_K` a unit, `Δ_K` integral
    push Not at hp2h
    rw [if_neg (by omega)] at hvm
    have hKp : K < p := by unfold hof at hp2h; omega
    have hΔ := prop_4_3_large (p := p) hK40 hKp
    unfold F
    refine vpGge_mono (vpGge_C_mul_val hm0 (vpGge_C_mul_val hS0 hΔ)) ?_
    rw [hvm]
    have := S_vge_large (p := p) K hp2h
    push_cast; linarith

end Zeta5