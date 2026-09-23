import Zeta5.Section5
import Zeta5.Legendre5
import Zeta5.Uniform57
import Zeta5.Integrals5
import Zeta5.Integrals5Gam
import Zeta5.Integrals5Outer
import Zeta5.Integrals5Inner
import Zeta5.Integrals5Tail
import Zeta5.PNT

/-!
# §5, analytic part: uniformity, exact integrals, tails, Proposition 5.2, (5.21)
-/

open Polynomial Finset MeasureTheory Filter Topology

noncomputable section

namespace Zeta5

/-- (5.7), inner range: `γ_p^in = pΓ(K/p) + O_M(1)` and `v_p(S_K) = pN(K/p) + O_M(1)`,
uniformly in `K/M < p ≤ K/3`. -/
theorem uniformity_5_7 (M : ℕ) (hM : 40 ≤ M) :
    ∃ Cst : ℝ, ∀ K p : ℕ, [Fact p.Prime] → InnerHyp K M p →
      |(gammaIn K M p : ℝ) - p * Lim.Gam ((K : ℝ) / p)| ≤ Cst ∧
      |(vpS K p : ℝ) - p * Lim.Nfun ((K : ℝ) / p)| ≤ Cst := by
  exact uniformity_5_7' M hM

/-- `∫_{1/3}^{1/2} d(y) dy = 9/640`. -/
theorem integral_dfun : ∫ y in (1 / 3 : ℝ)..(1 / 2), Lim.dfun y = 9 / 640 := by
  exact integral_dfun'

/-- (5.10): `I_out = 127751/96000`. -/
theorem integral_5_10 :
    ∫ y in (1 / 3 : ℝ)..(2 * Lim.lam), Lim.outerIntegrand y = (Iout : ℝ) := by
  exact integral_5_10'


/-- (5.12)–(5.13): `R(x) = x F(x) + Q(x)`, and (5.14): `-1/2 ≤ Q(x) ≤ 13/8`. -/
theorem R_decomp_bound (x : ℝ) (hx : 3 ≤ x) :
    -1 / 2 ≤ Lim.R x - x * (4 * Lim.lam + 2 * Lim.lam * Int.fract x - 12 * Lim.lam * Int.fract (Lim.α * x)) ∧
    Lim.R x - x * (4 * Lim.lam + 2 * Lim.lam * Int.fract x - 12 * Lim.lam * Int.fract (Lim.α * x)) ≤ 13 / 8 := by
  exact R_decomp_bound' x hx

/-- The mean of `P` over a period is `2923/240`. -/
theorem Pper_mean : (∫ x in (0 : ℝ)..40, Lim.Pper x) / 40 = 2923 / 240 := by
  exact Pper_mean'

/-- `|C(x)| ≤ 118511/(4320√3) < 16`. -/
theorem Cper_bound (x : ℝ) : |Lim.Cper x| < 16 := by
  exact Cper_bound' x

/-- `R(x)/x³` is integrable on `[3, ∞)`. -/
theorem R_integrableOn : IntegrableOn (fun x => Lim.R x / x ^ 3) (Set.Ici 3) := by
  exact R_integrableOn'

/-- (5.16): `∫_{20}^∞ R(x)/x³ dx ≤ -2689/48000`. -/
theorem tail_5_16 : ∫ x in Set.Ioi (20 : ℝ), Lim.R x / x ^ 3 ≤ -2689 / 48000 := by
  exact tail_5_16'

/-- (5.17): for `40 ∣ M`, `∫_M^∞ R(x)/x³ dx ≥ -λ/M + (2923/240 - 1/4)/M² - 32/M³`. -/
theorem tail_5_17 (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) :
    -Lim.lam / M + (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 - 32 / (M : ℝ) ^ 3 ≤
      ∫ x in Set.Ioi (M : ℝ), Lim.R x / x ^ 3 := by
  exact tail_5_17' M hM hM0

/-- (5.18): `∫₃^{20} R(x)/x³ dx = 322437603634266857629/7535670527041937280000`.
Checked in exact arithmetic by `checks/check_constants.py`. -/
theorem integral_5_18 :
    ∫ x in (3 : ℝ)..20, Lim.R x / x ^ 3 = 322437603634266857629 / 7535670527041937280000 := by
  exact integral_5_18'


-- Proposition 5.2 and (5.21) are in `Prop52.lean`.

end Zeta5
