"""Phases 1.3 and 1.5: build G_K(X) exactly for small K and test the paper's claims on it.

Checked, for K in 40Z (N = 3K/40, h = 37K/40):
  * leading coefficient formula (2.9);
  * positivity of G_K(zeta(5)) (Prop 2.2), via high-precision Cholesky;
  * small-prime bound (3.12):   v_p^G(F_K) >= -6h floor(log_p 5K) - h v_p(24), every p;
  * outer range (Prop 4.3):     v_p^G(Delta_K) >= gamma_p^out whenever (4.9) holds,
                                v_p^G(Delta_K) >= 0 for p > K.
G_K(X) = A + X B with exact rational matrices; Delta_K(X) = det(A + X B) by interpolation.
"""
import sys
from math import comb

import flint
from flint import fmpq, fmpq_mat, fmpq_poly
import mpmath

def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p**0.5) + 1))]

def vp_int(n, p):
    n = abs(int(n))
    if n == 0:
        return 10**9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def vp_q(x, p):
    x = fmpq(x)
    if x == 0:
        return 10**9
    return vp_int(x.p, p) - vp_int(x.q, p)

def gauss_v(poly_coeffs, p):
    return min(vp_q(c, p) for c in poly_coeffs)

def mu_mono(e):
    return (-1)**e * fmpq.bernoulli(2*e + 2) * (2*e + 3) * (2*e + 4) * (2*e + 5) / 24

def build(K):
    N, h = 3 * K // 40, 37 * K // 40
    t = fmpq_poly([0, 1])
    DN = fmpq_poly([1])
    for j in range(1, N + 1):
        DN *= (t + j * j)
    Dtail = fmpq_poly([1])
    for k in range(N + 1, K + 1):
        Dtail *= (t + k * k)
    H5 = [fmpq(0)]
    for v in range(1, K + 1):
        H5.append(H5[-1] + fmpq(1, v**5))
    poles = list(range(N + 1, K + 1))
    dprime = {k: fmpq(1) for k in poles}
    for k in poles:
        prod = fmpq(1)
        for l in poles:
            if l != k:
                prod *= (l * l - k * k)
        dprime[k] = prod
    DN5 = DN**5
    DN5_at = {k: DN5(fmpq(-k * k)) for k in poles}
    maxdeg = 2 * h - 2 + 5 * N
    mu_cache = [mu_mono(e) for e in range(maxdeg + 1)]
    Avals, Bvals = [], []
    for e in range(2 * h - 1):
        num = DN5 * t**e
        quo = num // Dtail
        a = sum((quo[d] * mu_cache[d] for d in range(quo.degree() + 1)), fmpq(0))
        b = fmpq(0)
        for k in poles:
            c = DN5_at[k] * fmpq((-k * k)**e) / dprime[k]
            a += c * (-fmpq(k**4) * H5[k] - fmpq(1, 4) + fmpq(1, 2 * k))
            b += c * k**4
        Avals.append(a)
        Bvals.append(b)
    A = fmpq_mat(h, h, [Avals[i + j] for i in range(h) for j in range(h)])
    B = fmpq_mat(h, h, [Bvals[i + j] for i in range(h) for j in range(h)])
    return N, h, A, B, DN

def det_poly(A, B, h):
    xs = list(range(h + 1))
    ys = [(A + B * x).det() for x in xs]
    # Newton interpolation over Q
    coef = list(ys)
    for lvl in range(1, h + 1):
        for i in range(h, lvl - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - lvl])
    X = fmpq_poly([0, 1])
    poly = fmpq_poly([coef[h]])
    for i in range(h - 1, -1, -1):
        poly = poly * (X - xs[i]) + coef[i]
    return poly

def S_K(K, N, h):
    from math import factorial
    num = factorial(K)**(2 * h) * 4**(h - 1)
    den = factorial(N)**(12 * h)
    for i in range(1, h):
        den *= factorial(2 * i)**2
    return fmpq(num, den)

def gamma_out(K, N, p):
    v = K - p * (K // p)
    u = max(0, N + v - p + 1)
    tp = min(N, v) + u
    rp = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * tp - 1 - min(rp, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * tp - min(rp, p + u)

def cond_49(K, N, p):
    return p >= 7 and p <= K < 3 * p and p * p > 2 * K and 2 * N < p and 5 * N <= 2 * p - 2

def floor_log(p, n):
    k = 0
    while p**(k + 1) <= n:
        k += 1
    return k

def main(K, check_pos=True):
    N, h, A, B, DN = build(K)
    print(f"== K={K}, N={N}, h={h}")
    delta = det_poly(A, B, h)
    coeffs = [delta[d] for d in range(delta.degree() + 1)]
    ok_deg = delta.degree() == h
    lead_pred = fmpq((-1)**(h * (h - 1) // 2))
    for j in range(N + 1, K + 1):
        lead_pred *= fmpq(j**4) * DN(fmpq(-j * j))**5
    print(f"  (2.9) degree == h: {ok_deg}; leading coeff matches: {delta[h] == lead_pred}")
    S = S_K(K, N, h)
    fails = 0
    for p in primes_upto(2 * h + 20):
        vD = gauss_v(coeffs, p)
        vF = vD + vp_q(S, p)
        b312 = -6 * h * floor_log(p, 5 * K) - h * vp_int(24, p)
        line = f"  p={p:>3}: v(Delta)={vD:>6} v(F)={vF:>6}  (3.12) bound {b312:>6} {'ok' if vF >= b312 else 'FAIL'}"
        if vF < b312:
            fails += 1
        if cond_49(K, N, p):
            g = gamma_out(K, N, p)
            line += f" | Prop4.3 gamma_out {g:>5} {'ok' if vD >= g else 'FAIL'} (slack {vD - g})"
            if vD < g:
                fails += 1
        if p > K:
            line += f" | p>K: v(Delta)>=0 {'ok' if vD >= 0 else 'FAIL'}"
            if vD < 0:
                fails += 1
        print(line)
    if check_pos:
        mpmath.mp.dps = 60 * h
        z5 = mpmath.zeta(5)
        G = mpmath.matrix(h, h)
        for i in range(h):
            for j in range(h):
                a, b = A[i, j], B[i, j]
                G[i, j] = mpmath.mpf(int(a.p)) / int(a.q) + z5 * mpmath.mpf(int(b.p)) / int(b.q)
        try:
            mpmath.cholesky(G)
            pd = True
        except ValueError:
            pd = False
        # Rigorous sign of Delta_K(zeta5) via arb ball arithmetic (mpmath Horner loses the sign to cancellation).
        from flint import arb, ctx
        ctx.prec = 40000
        z = arb(5).zeta()
        acc = arb(0)
        for c in reversed(coeffs):
            acc = acc * z + arb(c)
        print(f"  Prop 2.2: G_K(zeta5) positive definite (Cholesky): {pd}; Delta_K(zeta5) = {acc.str(6)}, positive: {acc > 0}")
    print(f"  failures: {fails}")
    return fails

if __name__ == "__main__":
    Ks = [int(a) for a in sys.argv[1:]] or [40]
    for K in Ks:
        main(K)
