import Zeta5.SmallPrimes
import Zeta5.MuMod
import Zeta5.Distribution

/-!
# §3 The local rational functional

The pullback (3.1), reflection (3.2) and difference (3.3) identities; Lemmas 3.1–3.3; the
small-prime bound (3.12).

Rational functions in `x` are given as `P / ∏_{r ∈ S} (x - r)` (see `tauX`).
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

-- (3.1), the pullback identity, is `pullback` in `Functionals.lean` (proved).

/-- (3.2), reflection: `τ_X(g(-1-x)) = -τ_X(g(x))`. Writing `g = P/∏(x - r)`, one has
`g(-1-x) = (-1)^{|S|} P(-1-x) / ∏ (x - (-1-r))`. -/
theorem tauX_reflect (S : Finset ℤ) (P : ℚ[X]) :
    tauX (S.image fun r => -1 - r) (C ((-1) ^ S.card) * P.comp (-1 - X)) = -tauX S P := by
  sorry

/-- (3.3), difference: `τ_X(g(x+1) - g(x)) = g⁽⁴⁾(0)/24` when `g` is regular at `0`. -/
theorem tauX_difference (S : Finset ℤ) (hS : 0 ∉ S) (P : ℚ[X]) :
    tauX (S.image fun r => r - 1) (P.comp (X + 1)) - tauX S P =
      C (taylor4 P (linPoleProd S)) := by
  sorry

/-- The von Staudt–Clausen consequence used in §3.1: `v_p(κ_d) ≥ -1`, for odd `p`.
(False for `p = 2`: `κ₃ = 1/4`. The paper only uses `p ≥ 7`.) -/
theorem kappa_padicVal_ge (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (d : ℕ) (hd : kappa d ≠ 0) :
    -1 ≤ padicValRat p (kappa d) := by
  exact kappa_padicVal_ge' p hp2 d hd

/-- §3.1: `κ_d ∈ ℤ_p` for `d ≤ p + 1` (with `p ≥ 7`). -/
theorem kappa_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (d : ℕ) (hd : d ≤ p + 1)
    (hk : kappa d ≠ 0) : 0 ≤ padicValRat p (kappa d) := by
  exact kappa_integral' p hp d hd hk

/-- Lemma 3.1, for finite sums. The paper states it for convergent series `∑_{j ≥ 0}`; that
follows from this by continuity, since `‖τ‖ ≤ p`.
Hypotheses: `p ≥ 7`; the poles `r_ν` are distinct integers whose differences are `p`-adic units
and with `d(r_ν) < p`; `Y ∈ ℤ_p[X]`; `U_j ∈ ℤ_p[z]` with `deg U₀ ≤ p + 1`.
Conclusion: `τ_Y^{ext}(∑_j p^j U_j / T) ∈ ℤ_p[X]`. -/
theorem lemma_3_1 (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (T : Finset ℤ)
    (hT : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → ¬ (p : ℤ) ∣ r - s) (hd : ∀ r ∈ T, dIdx r < p)
    (Y : ℚ_[p][X]) (hY : ∀ i, ‖Y.coeff i‖ ≤ 1)
    (J : ℕ) (Uf : ℕ → ℚ_[p][X]) (hU : ∀ j i, ‖(Uf j).coeff i‖ ≤ 1)
    (hU0 : (Uf 0).natDegree ≤ p + 1) :
    ∀ i, ‖(tauExtP p Y (∑ j ∈ range (J + 1), C ((p : ℚ_[p]) ^ j) * Uf j)
        (T.image fun r : ℤ => (r : ℚ))).coeff i‖ ≤ 1 := by
  sorry

/-- §3.2: `C_p ∈ p⁵ ℤ_p`. -/
theorem Cp_norm_le (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : ‖Cp p‖ ≤ (p : ℝ) ^ (-5 : ℤ) := by
  exact Cp_norm_le' p hp

/-- Lemma 3.2, the distribution formula (3.7):
`τ_X(g) = p⁻⁴ ∑_{a=0}^{p-1} τ_Y^{ext}(g(a + p x))`, with `Y = p⁵X + C_p`. -/
theorem lemma_3_2 (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (S : Finset ℤ) (P : ℚ[X]) :
    (tauX S P).map (algebraMap ℚ ℚ_[p]) =
      C ((p : ℚ_[p]) ^ (-4 : ℤ)) *
        ∑ a ∈ range p, tauExtP p (Yp p) (distribNum p S P a) (distribPoles p S a) := by
  exact lemma_3_2' p hp S P

-- `IntValuedAt` is defined in `IntValued.lean`.

/-- The poles `-K ≤ r ≤ K`, `r ≠ 0`, of Lemma 3.3. -/
def symPoles (K : ℕ) : Finset ℤ := (Icc (-(K : ℤ)) K).erase 0

/-- Lemma 3.3, (3.10): if `A` is integer-valued with `deg A ≤ d` and
`g = (K!)² A(x) / ∏_{0 < |r| ≤ K} (x - r)`, then
`v_p^G(τ_X(g)) ≥ -6 ⌊log_p max(2K, d+1)⌋ - v_p(24)`. -/
theorem lemma_3_3 (p : ℕ) [Fact p.Prime] (K d : ℕ) (A : ℚ[X]) (hA : IntValuedAt p A)
    (hd : A.natDegree ≤ d) :
    vpGge p (tauX (symPoles K) (C ((K.factorial : ℚ) ^ 2) * A))
      (-6 * Nat.log p (max (2 * K) (d + 1)) - padicValNat p 24) := by
  exact lemma_3_3' p K d A hA hd

/-- §3.3: `f_i(-x²)` is integer-valued. -/
theorem fBasis_intValued (p : ℕ) [Fact p.Prime] (K i : ℕ) :
    IntValuedAt p ((fBasis K i).comp (-X ^ 2)) := by
  exact fBasis_intValued' p K i

/-- (3.11): `F_K = det[(K!)² µ_X(f_i f_j / D_K)]`. -/
theorem F_eq_det_fBasis (K : ℕ) (hK : 40 ∣ K) :
    F K = (Matrix.of fun i j : Fin (hof K) =>
      C ((K.factorial : ℚ) ^ 2) * muX (Icc 1 K) (fBasis K i * fBasis K j)).det := by
  exact F_eq_det_fBasis' K

/-- (3.12): `v_p^G(F_K) ≥ -6h ⌊log_p(5K)⌋ - h v_p(24)` for every prime `p`. -/
theorem vpG_F_ge (p : ℕ) [Fact p.Prime] (K : ℕ) (hK : 40 ∣ K) :
    vpGge p (F K) (-6 * hof K * Nat.log p (5 * K) - hof K * padicValNat p 24) := by
  exact vpG_F_ge' p K hK

end Zeta5
