"""Phase 1.3 (remaining part): Proposition 2.2 numerically.

  mu_{zeta(5)}(R) = int_0^inf R(y^2) w(y) dy,   w(y) = (2pi)^4 y^5/12 sum_l l^4 e^{-2 pi l y}

tested on monomials t^e, simple poles 1/(t + j^2), random rational functions, and actual
entries of G_40(zeta(5)). Also checks the elementary bound (6.11) w(y) <= 8192 (1+y)^5 e^{-2 pi y}
and the limit w(0+) = 1/pi.
"""
import random

import mpmath as mp
from flint import fmpq, fmpq_poly

from functionals import T, muX, muMono, muPole, sqPoleProd

mp.mp.dps = 60
Z5 = mp.zeta(5)
fails = 0


def report(name, ok, detail=""):
    global fails
    if not ok:
        fails += 1
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))


def w(y):
    q = mp.exp(-2 * mp.pi * y)
    # sum_{l>=1} l^4 q^l = q(1 + 11q + 11q^2 + q^3)/(1-q)^5 ; (1-q) = -expm1(-2 pi y) avoids cancellation
    one_minus_q = -mp.expm1(-2 * mp.pi * y)
    return (2 * mp.pi)**4 * y**5 / 12 * q * (1 + 11*q + 11*q**2 + q**3) / one_minus_q**5


def q2mp(c):
    return mp.mpf(int(c.p)) / int(c.q)


def at_z5(pair):
    return q2mp(pair[0]) + Z5 * q2mp(pair[1])


def integral(f):
    return mp.quad(lambda y: f(y) * w(y), [0, 1, 4, 10, 25, 60, mp.inf])


def reldiff(a, b):
    return abs(a - b) / max(abs(a), abs(b), mp.mpf(10)**-40)


# weight sanity
report("w(0+) = 1/pi", abs(w(mp.mpf(10)**-20) - 1 / mp.pi) < mp.mpf(10)**-15)
ys = [mp.mpf(k) / 50 for k in range(1, 2000)]
report("(6.11) w(y) <= 8192 (1+y)^5 e^{-2 pi y} on (0, 40)",
       all(w(y) <= 8192 * (1 + y)**5 * mp.exp(-2 * mp.pi * y) for y in ys),
       f"max ratio {mp.nstr(max(w(y) / ((1 + y)**5 * mp.exp(-2 * mp.pi * y)) for y in ys), 6)} (bound 8192)")

worst = mp.mpf(0)
for e in range(0, 16):
    worst = max(worst, reldiff(q2mp(muMono(e)), integral(lambda y: y**(2 * e))))
report("mu(t^e) = int y^{2e} w, e = 0..15", worst < mp.mpf(10)**-30, f"max rel err {mp.nstr(worst, 3)}")

worst = mp.mpf(0)
for j in range(1, 31):
    worst = max(worst, reldiff(at_z5(muPole(j)), integral(lambda y: 1 / (y**2 + j**2))))
report("mu_zeta5(1/(t+j^2)) = int w/(y^2+j^2), j = 1..30", worst < mp.mpf(10)**-30,
       f"max rel err {mp.nstr(worst, 3)}")

random.seed(2)
worst = mp.mpf(0)
for trial in range(40):
    S = random.sample(range(1, 15), random.randint(1, 5))
    P = fmpq_poly([random.randint(1, 9) for _ in range(random.randint(1, 10))])
    Q = sqPoleProd(S)
    pc = [q2mp(c) for c in reversed(P.coeffs())]
    qc = [q2mp(c) for c in reversed(Q.coeffs())]
    lhs = at_z5(muX(S, P))
    rhs = integral(lambda y: mp.polyval(pc, y**2) / mp.polyval(qc, y**2))
    worst = max(worst, reldiff(lhs, rhs))
report("mu_zeta5(P/prod(t+j^2)) = integral, 40 random", worst < mp.mpf(10)**-25, f"max rel err {mp.nstr(worst, 3)}")

# actual G_40 entries (these are tiny numbers with big cancellation on the left-hand side)
K, N = 40, 3
DN6 = sqPoleProd(range(1, N + 1))**6
DK = sqPoleProd(range(1, K + 1))
mp.mp.dps = 400
Z5 = mp.zeta(5)
worst = mp.mpf(0)
for (i, j) in [(0, 0), (0, 5), (3, 7), (10, 10), (0, 36), (20, 30), (36, 36)]:
    P = DN6 * T**(i + j)
    lhs = at_z5(muX(range(1, K + 1), P))
    pc = [q2mp(c) for c in reversed(P.coeffs())]
    qc = [q2mp(c) for c in reversed(DK.coeffs())]
    rhs = mp.quad(lambda y: mp.polyval(pc, y**2) / mp.polyval(qc, y**2) * w(y),
                  [0, 0.5, 1, 2, 4, 8, 16, 32, 64, mp.inf])
    worst = max(worst, reldiff(lhs, rhs))
report("G_40(zeta5)[i,j] = integral, 7 entries", worst < mp.mpf(10)**-20, f"max rel err {mp.nstr(worst, 3)}")

print(f"\nfailures: {fails}")
