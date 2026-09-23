import Zeta5.Defs

/-!
# Appendix B: exact arithmetic

The purely rational facts of §5–§7 and Appendix B, proved by `norm_num`. The piecewise-affine
integrals (5.10) and (5.18) are stated in `Section5.lean`. They are checked in exact
arithmetic by `checks/check_constants.py` but not yet proved in Lean.
-/

namespace Zeta5

theorem Hc_eq : Hc = 23 / 20 := by norm_num [Hc, α]

/-- The cancellation of the quadratic coefficient of `R` (Appendix B.1). -/
theorem quadratic_cancellation :
    2 * lam - 12 * lam * α + 2 * (Hc ^ 2 - Hc - lam ^ 2) - 18 * α ^ 2 + 6 * α = 0 := by
  norm_num [lam, α, Hc]

theorem lam_M0 : lam * M0 = -49173 / 8000 := by norm_num [lam, M0]

/-- (5.19): `A* = I_out + ∫₃^{20} R/x³ - 2689/48000`. -/
theorem Astar_eq :
    Astar = Iout + 322437603634266857629 / 7535670527041937280000 - 2689 / 48000 := by
  norm_num [Astar, Iout]

theorem A200_eq : AM 200 = 127125602969131786927559 / 94195881588024216000000 := by
  norm_num [AM, Astar, lam]

theorem A100000_eq :
    AM 100000 = 7756864096839411316755964319057 / 5887242599251513500000000000000 := by
  norm_num [AM, Astar, lam]

/-- (7.2), `M = 200`: `-1600(A₂₀₀ + U) > 139/5`, with the exact margin of Appendix B. -/
theorem margin_200 :
    -1600 * (AM 200 + U) - 139 / 5 = 3089837638249482469 / 58872425992515135000 ∧
      (139 / 5 : ℚ) < -1600 * (AM 200 + U) := by
  norm_num [AM, Astar, lam, U]

/-- (7.2), `M = 100000`: `-1600(A₁₀₀₀₀₀ + U) > 7907/100`. -/
theorem margin_100000 :
    -1600 * (AM 100000 + U) - 7907 / 100 =
        29873543950273155160680943 / 3679526624532195937500000000 ∧
      (7907 / 100 : ℚ) < -1600 * (AM 100000 + U) := by
  norm_num [AM, Astar, lam, U]

/-- (6.4): `U < -136699/100000`. -/
theorem U_lt : U < -136699 / 100000 := by norm_num [U]

end Zeta5
