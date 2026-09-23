"""Exact Python mirrors of the Lean definitions in Zeta5/Zeta5/Defs.lean.

Values in Q[X] that are affine in X are returned as pairs (c0, c1) meaning c0 + c1*X.
Rational functions are (numerator polynomial, list of simple poles), as in the Lean `muX`/`tauX`.
"""
from functools import lru_cache
from math import comb

from flint import fmpq, fmpq_poly

T = fmpq_poly([0, 1])  # the variable t (or x)


@lru_cache(maxsize=None)
def bern(k):
    return fmpq.bernoulli(k)  # B_1 = -1/2, as in Mathlib and the paper


@lru_cache(maxsize=None)
def H5(j):
    return sum((fmpq(1, v**5) for v in range(1, j + 1)), fmpq(0))


def vp(x, p):
    x = fmpq(x)
    if x == 0:
        return 10**9
    def v(n):
        n = abs(int(n)); c = 0
        while n % p == 0:
            n //= p; c += 1
        return c
    return v(x.p) - v(x.q)


def vpG(pair_or_list, p):
    return min(vp(c, p) for c in pair_or_list)


def add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def scale(c, u):
    return (c * u[0], c * u[1])


# ---------- mu_X (2.2), (2.3) ----------
@lru_cache(maxsize=None)
def muMono(e):
    return (-1)**e * bern(2*e + 2) * fmpq((2*e + 3) * (2*e + 4) * (2*e + 5), 24)


def muPoly(P):
    return sum((P[d] * muMono(d) for d in range(P.degree() + 1)), fmpq(0))


@lru_cache(maxsize=None)
def muPole(j):
    return (-fmpq(j**4) * H5(j) - fmpq(1, 4) + fmpq(1, 2 * j), fmpq(j**4))


def sqPoleProd(S):
    Q = fmpq_poly([1])
    for j in S:
        Q *= T + j * j
    return Q


@lru_cache(maxsize=64)
def _sq_data(S):
    dens = {}
    for j in S:
        den = fmpq(1)
        for k in S:
            if k != j:
                den *= k * k - j * j
        dens[j] = den
    return sqPoleProd(S), dens


def muX(S, P, mono=muMono):
    """mu_X(P / prod_{j in S}(t + j^2)). `mono` lets (4.10) swap in the modified moments."""
    S = tuple(S)
    Q, dens = _sq_data(S)
    quo = P // Q if S else P
    c0 = sum((quo[d] * mono(d) for d in range(quo.degree() + 1)), fmpq(0))
    c1 = fmpq(0)
    for j in S:
        res = P(fmpq(-j * j)) / dens[j]
        pole = muPole(j)
        c0 += res * pole[0]
        c1 += res * pole[1]
    return (c0, c1)


# ---------- tau_X (§3) ----------
def tau(P):
    D3 = P.derivative().derivative().derivative()
    return sum((D3[k] * bern(k) for k in range(D3.degree() + 1)), fmpq(0)) / 24


def dIdx(r):
    return r if r >= 0 else -r - 1


def tauPole(r):
    return (H5(dIdx(r)), fmpq(-1))


def linPoleProd(S):
    Q = fmpq_poly([1])
    for r in S:
        Q *= T - fmpq(r)
    return Q


def tauX(S, P):
    S = list(S)
    quo = P // linPoleProd(S) if S else P
    val = (tau(quo), fmpq(0))
    for r in S:
        den = fmpq(1)
        for s in S:
            if s != r:
                den *= fmpq(r) - s
        val = add(val, scale(P(fmpq(r)) / den, tauPole(r)))
    return val


def taylor_coeff(P, Q, n):
    """[x^n] of the power series P/Q at 0 (Q(0) != 0)."""
    q0 = Q[0]
    inv = [fmpq(1) / q0]
    for m in range(1, n + 1):
        s = sum((Q[i] * inv[m - i] for i in range(1, m + 1)), fmpq(0))
        inv.append(-s / q0)
    return sum((P[i] * inv[n - i] for i in range(0, n + 1)), fmpq(0))


# ---------- p-adic extension (3.5), (3.6) ----------
def tauAnPole(p, s, kmax):
    """Truncation of (3.5) at k <= kmax; the error has v_p >= kmax + 4 + (kmax+1)*(-v_p(s)-1)."""
    s = fmpq(s)
    return -fmpq(1, 4) * sum((comb(k + 3, 3) * bern(k) * s**(-(k + 4)) for k in range(kmax + 1)), fmpq(0))


def Cp(p, kmax):
    return sum((tauAnPole(p, fmpq(-a, p), kmax) for a in range(1, p)), fmpq(0))


def tauExt(p, Y, U, poles, kmax):
    """tau_Y^ext(U / prod_{s in poles}(z - s)); Y = (y0, y1) means y0 + y1*X."""
    poles = [fmpq(s) for s in poles]
    Q = fmpq_poly([1])
    for s in poles:
        Q *= T - s
    quo = U // Q
    val = (tau(quo), fmpq(0))
    for s in poles:
        den = fmpq(1)
        for s2 in poles:
            if s2 != s:
                den *= s - s2
        res = U(s) / den
        if s.q == 1:
            pv = (H5(dIdx(int(s.p))) - Y[0], -Y[1])
        else:
            pv = (tauAnPole(p, s, kmax), fmpq(0))
        val = add(val, scale(res, pv))
    return val


def compose_affine(P, a, b):
    """P(a + b x)."""
    return P(fmpq_poly([a, b]))
