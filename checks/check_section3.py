"""Phase 1.4: the §3 identities and lemmas, on random inputs, in exact arithmetic.

  (3.1) pullback      mu_X(R) = tau_X(x^5 R(-x^2))
  (3.2) reflection    tau_X(g(-1-x)) = -tau_X(g)
  (3.3) difference    tau_X(g(x+1) - g(x)) = g''''(0)/24   (g regular at 0)
  (3.6) C_p in p^5 Z_p
  (3.7) distribution  tau_X(g) = p^-4 sum_a tau_Y^ext(g(a + p x)),  Y = p^5 X + C_p   (p-adically)
  Lemma 3.1           integrality of tau_Y^ext(sum_j p^j U_j / T), and what breaks without deg U_0 <= p+1
  Lemma 3.3 (3.10)    v_p^G(tau_X(g)) >= -6 floor(log_p max(2K, d+1)) - v_p(24)
  §3.1 / §4.2 facts   v_p(kappa_d) >= -1, kappa_d in Z_p for d <= p+1; v_p(mu(t^e)) >= -1, integral for e < 2p-3
  (3.11)              F_K = det[(K!)^2 mu_X(f_i f_j / D_K)]  at K = 40
"""
import random
from math import factorial

from flint import fmpq, fmpq_poly, fmpq_mat

from functionals import (T, add, bern, compose_affine, Cp, dIdx, linPoleProd, muMono, muX, tau,
                         tauExt, tauX, taylor_coeff, vp, vpG)

random.seed(1)
fails = 0


def report(name, ok, detail=""):
    global fails
    if not ok:
        fails += 1
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))


def rand_poly(deg, lo=-9, hi=9):
    return fmpq_poly([random.randint(lo, hi) for _ in range(deg + 1)])


def primes(lo, hi):
    return [p for p in range(max(lo, 2), hi + 1) if all(p % q for q in range(2, int(p**0.5) + 1))]


# ---------- (3.1) ----------
bad = 0
for trial in range(300):
    S = random.sample(range(1, 12), random.randint(0, 5))
    P = rand_poly(random.randint(0, 14))
    lhs = muX(S, P)
    num = (-1)**len(S) * T**5 * P(-T**2)
    rhs = tauX(sorted(set(S) | {-j for j in S}), num)
    bad += lhs != rhs
report("(3.1) pullback, 300 random (P, S)", bad == 0, f"{bad} mismatches")

# ---------- (3.2), (3.3) ----------
bad2 = bad3 = 0
for trial in range(300):
    S = random.sample([r for r in range(-10, 11) if r != 0], random.randint(0, 5))
    P = rand_poly(random.randint(0, 12))
    base = tauX(S, P)
    refl = tauX([-1 - r for r in S], (-1)**len(S) * compose_affine(P, -1, -1))
    bad2 += refl != (-base[0], -base[1])
    diff = tauX([r - 1 for r in S], compose_affine(P, 1, 1))
    got = (diff[0] - base[0], diff[1] - base[1])
    bad3 += got != (taylor_coeff(P, linPoleProd(S), 4), fmpq(0))
report("(3.2) reflection, 300 random", bad2 == 0, f"{bad2} mismatches")
report("(3.3) difference, 300 random (0 not a pole)", bad3 == 0, f"{bad3} mismatches")

# ---------- kappa and mu(t^e) valuations ----------
worst_k = worst_mu = 0
for p in primes(7, 101):
    for d in range(3, 6 * p):
        k = fmpq(d * (d - 1) * (d - 2)) * bern(d - 3) / 24
        if k != 0:
            v = vp(k, p)
            if v < -1 or (d <= p + 1 and v < 0):
                worst_k += 1
    for e in range(0, 4 * p):
        m = muMono(e)
        if m != 0:
            v = vp(m, p)
            if v < -1 or (e < 2 * p - 3 and v < 0):
                worst_mu += 1
first_bad = {}
for p in primes(7, 101):
    for d in range(3, 6 * p):
        k = fmpq(d * (d - 1) * (d - 2)) * bern(d - 3) / 24
        if k != 0 and vp(k, p) < 0:
            first_bad[p] = d
            break
print("       first d with v_p(kappa_d) < 0 is 4p-1 for every p in 7..101:",
      all(d == 4 * p - 1 for p, d in first_bad.items()))
report("v_p(kappa_d) >= -1, integral for d <= p+1 (p in 7..101, d < 6p)", worst_k == 0, f"{worst_k} violations")
report("v_p(mu(t^e)) >= -1, integral for e < 2p-3 (p in 7..101, e < 4p)", worst_mu == 0, f"{worst_mu} violations")

# ---------- (3.6) and (3.7) ----------
for p in [7, 11, 13]:
    for kmax in [30, 60]:
        c = Cp(p, kmax)
        report(f"(3.6) v_p(C_p) >= 5, p={p}, kmax={kmax}", vp(c, p) >= 5, f"v_p = {vp(c, p)}")
for p in [7, 11, 13]:
    worst = {}
    for kmax in [25, 50]:
        c = Cp(p, kmax)
        Y = (c, fmpq(p**5))
        mins = []
        for trial in range(25):
            S = random.sample(range(-3 * p, 3 * p), random.randint(0, 4))
            P = rand_poly(random.randint(0, 9))
            lhs = tauX(S, P)
            rhs = (fmpq(0), fmpq(0))
            for a in range(p):
                U = fmpq(p)**(-len(S)) * compose_affine(P, a, p)
                rhs = add(rhs, tauExt(p, Y, U, [fmpq(r - a, p) for r in S], kmax))
            rhs = (rhs[0] / p**4, rhs[1] / p**4)
            mins.append(min(vp(lhs[0] - rhs[0], p), vp(lhs[1] - rhs[1], p)))
        worst[kmax] = min(mins)
    # exact agreement shows up as a p-adic error that grows with the truncation order
    report(f"(3.7) distribution, p={p}: min v_p(LHS-RHS) over 25 random g",
           worst[50] > worst[25] >= 15, f"kmax=25: {worst[25]}, kmax=50: {worst[50]}")

# ---------- Lemma 3.1 ----------
for p in [7, 11, 13]:
    viol = 0
    viol_deg = 0
    for trial in range(200):
        # distinct integer poles, pairwise differences p-adic units, d(r) < p
        cand = list(range(-p, p))
        random.shuffle(cand)
        Tp = []
        for r in cand:
            if all((r - s) % p for s in Tp):
                Tp.append(r)
            if len(Tp) >= random.randint(1, 5):
                break
        Y = (fmpq(random.randint(-50, 50)), fmpq(random.randint(-50, 50)))
        for deg0, counter in [(p + 1, "ok"), (4 * p - 1 + random.randint(0, 3), "deg")]:
            U = rand_poly(deg0)
            for j in range(1, 4):
                U += fmpq(p**j) * rand_poly(random.randint(0, 3 * p))
            val = tauExt(p, Y, U, Tp, 0)
            if vpG(val, p) < 0:
                if counter == "ok":
                    viol += 1
                else:
                    viol_deg += 1
    report(f"Lemma 3.1, p={p}: 200 random instances", viol == 0, f"{viol} violations")
    print(f"       control: with deg U_0 >= 4p-1, {viol_deg}/200 instances lose integrality "
          "(kappa_d is p-integral for all d <= 4p-2, so deg U_0 <= p+1 is conservative)")

# ---------- Lemma 3.3 ----------
def binom_poly(k):
    P = fmpq_poly([1])
    for i in range(k):
        P *= (T - i)
    return P / factorial(k)

def floor_log(p, n):
    k = 0
    while p**(k + 1) <= n:
        k += 1
    return k

viol = 0
tight = []
for trial in range(150):
    K = random.randint(2, 14)
    d = random.randint(0, 4 * K + 10)
    A = sum((random.randint(-20, 20) * binom_poly(k) for k in range(d + 1)), fmpq_poly([0]))
    poles = [r for r in range(-K, K + 1) if r != 0]
    val = tauX(poles, factorial(K)**2 * A)
    for p in primes(2, 2 * K + d + 10):
        bound = -6 * floor_log(p, max(2 * K, d + 1)) - vp(fmpq(24), p)
        v = vpG(val, p)
        if v < bound:
            viol += 1
        tight.append(v - bound)
report("Lemma 3.3 (3.10): 150 random (K, A), all primes", viol == 0,
       f"{viol} violations; min slack {min(tight)}")

# ---------- (3.11) at K = 40 ----------
from check_determinant import build, det_poly, S_K  # noqa: E402
from functionals import sqPoleProd  # noqa: E402

K, N, h = 40, 3, 37
_, _, A, B, DN = build(K)
F_direct = S_K(K, N, h) * det_poly(A, B, h)
def qb(i):
    if i == 0:
        return fmpq_poly([1])
    P = fmpq_poly([1])
    for j in range(1, i):
        P *= T + j * j
    return fmpq((-1)**i * 2, factorial(2 * i)) * T * P
DNp = sqPoleProd(range(1, N + 1))
f = [(DNp / factorial(N)**2)**3 * qb(i) for i in range(h)]
Kf2 = fmpq(factorial(K)**2)
E = [[muX(range(1, K + 1), f[i] * f[j]) for j in range(h)] for i in range(h)]
EA = fmpq_mat(h, h, [Kf2 * E[i][j][0] for i in range(h) for j in range(h)])
EB = fmpq_mat(h, h, [Kf2 * E[i][j][1] for i in range(h) for j in range(h)])
F_basis = det_poly(EA, EB, h)
report("(3.11) F_K = det[(K!)^2 mu_X(f_i f_j / D_K)] at K=40", F_basis == F_direct)

print(f"\nfailures: {fails}")
