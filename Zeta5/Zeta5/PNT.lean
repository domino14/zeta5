import Zeta5.PNTPort.Final

/-!
# The prime number theorem

The paper uses only the asymptotic form of the prime number theorem [9, §27.12]:
`θ(x) ~ x`. The proof is ported from the PrimeNumberTheoremAnd project
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit a5154676, Apache-2.0; see
`PNTPort/`), trimmed to the Wiener–Ikehara route to `chebyshev_asymptotic` and adapted to this
project's toolchain.
-/

open Filter Topology

namespace Zeta5

/-- **The prime number theorem**, in Chebyshev's form `θ(x)/x → 1`. -/
theorem prime_number_theorem : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  prime_number_theorem'

end Zeta5
