import Zeta5.Section3
import Zeta5.Section4
import Zeta5.InnerFinal

/-!
# §5 Normalisation and the prime sum

Legendre's formula (5.3), Proposition 5.1 (integrality), the uniformity estimates (5.7) and
their outer analogues, Proposition 5.2, the exact integrals (5.10), (5.18) and the tail
bounds (5.14)–(5.17), and (5.21).
-/

open Polynomial Finset MeasureTheory Filter Topology

noncomputable section

namespace Zeta5

-- (5.3) `vpS_legendre` (with `0 < K`) is in `Legendre5.lean`.


/-- The standing hypotheses of Theorem 2.1. -/
def StdHyp (K M : ℕ) : Prop := 40 ≤ M ∧ 40 ∣ K ∧ 0 < K ∧ 200 * M ^ 2 ≤ K

/-- `m_{K,M} > 0`. -/
theorem mKM_pos (K M : ℕ) : 0 < mKM K M :=
  Finset.prod_pos fun p hp => zpow_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos) _

-- Proposition 5.1 (`prop_5_1`) is in `Prop51.lean`; the analytic results of §5 are in
-- `Section5Final.lean`.


-- The outer uniformity `uniformity_outer` is in `Legendre5.lean`.













end Zeta5
