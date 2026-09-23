"""Phase 1.6: test the uniformity claim (5.7).

gamma_p^in is computed exactly from the discrete definitions (4.4)-(4.8), and v_p(S_K)
from Legendre (5.3). Both are compared with p*Gamma(K/p) and p*N(K/p). The paper claims
the differences are O_M(1), uniformly in the inner range K/M < p <= K/3.
Classes a are grouped by (l_N(a), l_K(a)), so the cost is O(1) per prime.
"""
import random
import sys
from fractions import Fraction as Fr
from math import floor

from check_constants import Gamma, Nfun  # exact limiting functions

def primes_in(lo, hi):
    sieve = bytearray([1]) * (hi + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(hi**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(range(i*i, hi + 1, i)))
    return [i for i in range(max(lo, 2), hi + 1) if sieve[i]]

def count_res(A, r, p):
    """#{1 <= j <= A : j = r mod p}, for 1 <= r <= p-1."""
    return 0 if A < r else (A - r) // p + 1

def class_groups(A_list, p):
    """Group a in 1..(p-1)/2 by the tuple (l_A(a) for A in A_list); return {tuple: count}."""
    m = (p - 1) // 2
    cuts = {1, m + 1}
    for A in A_list:
        r = A % p
        for c in (r, r + 1, p - r, p - r + 1):
            if 1 <= c <= m + 1:
                cuts.add(c)
    cuts = sorted(cuts)
    groups = {}
    for lo, hi in zip(cuts, cuts[1:]):
        key = tuple(count_res(A, lo, p) + count_res(A, p - lo, p) for A in A_list)
        for a in (lo, hi - 1):  # sanity: constant on the block
            assert key == tuple(count_res(A, a, p) + count_res(A, p - a, p) for A in A_list)
        groups[key] = groups.get(key, 0) + (hi - lo)
    return groups

def gamma_in(K, p, M):
    N, h = 3 * K // 40, 37 * K // 40
    m = (p - 1) // 2
    mN, mK = N // p, K // p
    L0 = 4 * M + 10
    rhs = h - L0 + 3 * (N - mN)
    T, E = divmod(rhs, m)
    groups = class_groups([N, K], p)  # (lN, lK) -> count
    # extras go to the first E classes in decreasing order of l_K
    rows = []  # (count, b, lK, eps)
    left = E
    for (lN, lK), cnt in sorted(groups.items(), key=lambda kv: -kv[0][1]):
        take = min(left, cnt)
        left -= take
        if take:
            rows.append((take, 3 * lN, lK, 1))
        if cnt - take:
            rows.append((cnt - take, 3 * lN, lK, 0))
    total = Fr(0)
    zmin = None
    for cnt, b, lK, eps in rows:
        L = T - b + eps
        assert L >= 0, (K, p, L)
        # sum_{i<L} (i + b - (lK+4)/2)
        total += cnt * (Fr(L * (L - 1), 2) + L * (b - Fr(lK + 4, 2)))
        zc = T + eps - Fr(lK + 4, 2)
        zmin = zc if zmin is None else min(zmin, zc)
    for i in range(L0):
        total += min(2 * i + 6 * mN - mK + Fr(1, 2), zmin)
    g = 2 * total
    assert g.denominator == 1, "gamma_in not an integer"
    return g

def vp_fact(n, p):
    s = 0
    while n:
        n //= p
        s += n
    return s

def vp_SK_fast(K, p):
    """Legendre (5.3); valid for p >= 5 (vp(4)=0) and p^2 > 2h."""
    N, h = 3 * K // 40, 37 * K // 40
    s = 2 * h * vp_fact(K, p) - 12 * h * vp_fact(N, p)
    # sum_{i=1}^{h-1} floor(2i/p): number of pairs (i, j>=1) with j*p <= 2i
    tot = 0
    j = 1
    while j * p <= 2 * (h - 1):
        tot += (h - 1) - ((j * p + 1) // 2) + 1
        j += 1
    return s - 2 * tot

def run(K, M, samples):
    ps = primes_in(K // M + 1, K // 3)
    ps = [p for p in ps if p * M > K and 3 * p <= K]
    if samples and len(ps) > samples:
        random.seed(K)
        ps = sorted(random.sample(ps, samples))
    worst_g, worst_s = (0, None), (0, None)
    for p in ps:
        x = Fr(K, p)
        dg = gamma_in(K, p, M) - p * Gamma(x)
        ds = vp_SK_fast(K, p) - p * Nfun(x)
        if abs(dg) > worst_g[0]:
            worst_g = (abs(dg), p)
        if abs(ds) > worst_s[0]:
            worst_s = (abs(ds), p)
    print(f"K={K:>10} M={M}: {len(ps)} primes, max|gamma_in - p*Gamma| = {float(worst_g[0]):.2f} (p={worst_g[1]}), "
          f"max|v_p(S_K) - p*N| = {float(worst_s[0]):.2f} (p={worst_s[1]})")
    sys.stdout.flush()

if __name__ == "__main__":
    M = 40
    for K in [320000, 1280000, 5120000, 20480000]:
        run(K, M, samples=400)
