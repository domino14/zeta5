import Zeta5.PNTPort.Consequences

/-!
# The prime number theorem, in the form used by §5

`Zeta5.PNTPort.chebyshev_asymptotic` (`θ ~ id`) is ported from PrimeNumberTheoremAnd
(A. Kontorovich, T. Tao, et al.), https://github.com/AlexKontorovich/PrimeNumberTheoremAnd,
commit a5154676af9aa3095150ee410cdda80555aa0642, Apache License 2.0 (see `LICENSE`).
-/

open Filter Topology

namespace Zeta5

/-- **The prime number theorem**, in Chebyshev's form `θ(x)/x → 1`. -/
theorem prime_number_theorem' : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have h := (Asymptotics.isEquivalent_iff_tendsto_one
    (eventually_ne_atTop (0 : ℝ))).mp PNTPort.chebyshev_asymptotic
  exact h

end Zeta5
