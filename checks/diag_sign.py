"""Resolve the sign of Delta_40(zeta(5)) rigorously-ish: several independent methods, rising precision."""
import mpmath
from flint import fmpq, arb, arb_mat, ctx
from check_determinant import build, det_poly

K = 40
N, h, A, B, DN = build(K)
delta = det_poly(A, B, h)
coeffs = [delta[d] for d in range(delta.degree() + 1)]
print("max coeff digits:", max(len(str(abs(c.p))) - len(str(c.q)) for c in coeffs if c != 0))

for prec_digits in [3000, 8000, 20000]:
    ctx.prec = int(prec_digits * 3.33)
    z = arb(5).zeta()
    # Horner with arb (ball arithmetic: the result's radius is a rigorous error bound)
    acc = arb(0)
    for c in reversed(coeffs):
        acc = acc * z + arb(c)
    # direct determinant of G(zeta5) in ball arithmetic
    G = arb_mat(h, h, [arb(A[i, j]) + z * arb(B[i, j]) for i in range(h) for j in range(h)])
    d = G.det()
    print(f"digits={prec_digits}: Horner Delta(z5) = {acc.str(6)} | det G(z5) = {d.str(6)}")
