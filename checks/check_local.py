"""Phase 1.5 (remaining part): the local valuation bounds of §4, entry by entry.

Part 1  Lemma 4.2 on random matrices.
Part 2  Inner-range combinatorics at realistic sizes (K >= 200 M^2): (4.4), L_a >= 0,
        sum L_a = h, independence of tie-breaking. (gamma_in = 2 sum w is an integer
        trivially, since every weight is a half-integer.)
Part 3  Inner-range entry bounds: every entry of G in the basis (4.5) has
        v_p^G >= w_x + w_y. The real hypothesis K >= 200 M^2 is out of reach, so this uses
        small M with the degree side conditions of the proof of Prop 4.1 reported explicitly.
Part 4  Outer range at K = 40, 80, 120 for every p satisfying (4.9): the decomposition (4.10)
        (L integral, rank <= r_p), unimodularity of the basis (4.11), the entry bounds (4.12)
        with the zero-class weights, and gamma_out = 2 sum w - min(r_p, z).

The definitions mirror Zeta5/Zeta5/Defs.lean. Usage: check_local.py [part ...]
"""
import random
import sys
import time
from fractions import Fraction as Fr

from flint import fmpq, fmpq_mat, fmpq_poly, fmpz_mat, nmod_mat

from functionals import T, muMono, muX, sqPoleProd, vp, vpG

fails = 0


def report(name, ok, detail=""):
    global fails
    if not ok:
        fails += 1
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    sys.stdout.flush()


def primes(lo, hi):
    return [p for p in range(max(lo, 2), hi + 1) if all(p % q for q in range(2, int(p**0.5) + 1))]


def ceil_half(x2):
    """ceil(x2 / 2) for an integer x2."""
    return -((-x2) // 2)


# ======================= Part 1: Lemma 4.2 =======================
def part1():
    random.seed(4)
    viol = 0
    slacks = []
    trials = 0
    for p in [2, 3, 5]:
        for _ in range(1500):
            h = random.randint(2, 7)
            w2 = [0 if random.random() < 0.35 else -random.randint(1, 5) for _ in range(h)]  # 2*w_i
            r = random.randint(0, h)
            z = w2.count(0)
            # A_ij with v(A_ij) >= w_i + w_j, often exactly equal
            A = [[fmpq(p) ** ceil_half(w2[i] + w2[j]) * random.choice([1, -1, 2, p - 1, random.randint(-p * p, p * p)])
                  for j in range(h)] for i in range(h)]
            for i in range(h):
                for j in range(i):
                    A[i][j] = A[j][i] if random.random() < 0.5 else A[i][j]
            U = [[random.randint(-p, p) for _ in range(r)] for _ in range(h)]
            V = [[random.randint(-p, p) for _ in range(h)] for _ in range(r)]
            L = [[sum(U[i][k] * V[k][j] for k in range(r)) for j in range(h)] for i in range(h)]
            M = fmpq_mat(h, h, [A[i][j] + fmpq(L[i][j], p) for i in range(h) for j in range(h)])
            d = M.det()
            bound = sum(w2) - min(r, z)
            trials += 1
            if d != 0:
                slack = vp(d, p) - bound
                slacks.append(slack)
                viol += slack < 0
    report(f"Lemma 4.2: {trials} random (A, L, w), p in 2,3,5", viol == 0,
           f"{viol} violations; bound attained with equality in {slacks.count(0)} cases")


# ======================= inner-range definitions =======================
class Inner:
    """gamma_in and friends for (K, M, p), mirroring Defs.lean. All weights are doubled (w2 = 2w)."""

    def __init__(self, K, M, p, pos=None):
        self.K, self.M, self.p = K, M, p
        self.N, self.h = 3 * K // 40, 37 * K // 40
        self.m = (p - 1) // 2
        self.L0 = 4 * M + 10
        self.rhs = self.h - self.L0 + 3 * (self.N - self.N // p)
        self.T, self.E = divmod(self.rhs, self.m)
        m = self.m
        self.lK = [None] + [self.ell(K, a) for a in range(1, m + 1)]
        self.lN = [None] + [self.ell(self.N, a) for a in range(1, m + 1)]
        if pos is None:  # defaultPos: ties broken by increasing a
            order = sorted(range(1, m + 1), key=lambda a: (-self.lK[a], a))
        else:
            order = sorted(range(1, m + 1), key=lambda a: pos[a])
        self.eps = [0] * (m + 1)
        for rank, a in enumerate(order):
            self.eps[a] = 1 if rank < self.E else 0
        self.La = [self.L0] + [self.T - 3 * self.lN[a] + self.eps[a] for a in range(1, m + 1)]
        self.Z = [None] + [self.T + self.eps[a] for a in range(1, m + 1)]
        self.zmin2 = min(2 * self.Z[c] - (self.lK[c] + 4) for c in range(1, m + 1))

    def ell(self, A, a):
        p = self.p
        def cnt(r):
            return 0 if A < r else (A - r) // p + 1
        if a == 0:
            return A // p
        return cnt(a) + cnt(p - a)

    def w2(self, a, i):
        if a == 0:
            return min(2 * (2 * i + 6 * (self.N // self.p) - self.K // self.p) + 1, self.zmin2)
        return 2 * (i + 3 * self.lN[a]) - (self.lK[a] + 4)

    def gamma(self):
        """gamma_in = 2 sum w = sum w2; an integer because every w is a half-integer."""
        return sum(self.w2(a, i) for a in range(self.m + 1) for i in range(max(self.La[a], 0)))


# ======================= Part 2: inner combinatorics at scale =======================
def part2():
    random.seed(5)
    for K, M in [(320000, 40), (1280000, 40), (2000000, 100)]:
        ps = [p for p in primes(K // M + 1, K // 3) if p * M > K]
        ps = sorted(random.sample(ps, min(25, len(ps))))
        bad_TE = bad_nonneg = bad_sum = bad_tie = 0
        min_Tb = None
        for p in ps:
            I = Inner(K, M, p)
            bad_TE += not (0 <= I.E < I.m and I.m * I.T + I.E == I.rhs)
            bad_nonneg += min(I.La) < 0
            bad_sum += sum(I.La) != I.h
            g = I.gamma()
            mt = min(I.T - 3 * I.lN[a] for a in range(1, I.m + 1))
            min_Tb = mt if min_Tb is None else min(min_Tb, mt)
            for _ in range(3):
                noise = {a: (-I.lK[a], random.random()) for a in range(1, I.m + 1)}
                order = sorted(noise, key=lambda a: noise[a])
                pos = {a: k for k, a in enumerate(order)}
                bad_tie += Inner(K, M, p, pos).gamma() != g
        report(f"(4.4) 0 <= E < m, mT + E = rhs; K={K}, M={M}, {len(ps)} primes", bad_TE == 0)
        report(f"L_a >= 0 (min T - b_a = {min_Tb} > 3/2 claimed)", bad_nonneg == 0 and min_Tb > 1.5)
        report(f"L_0 + sum L_a = h", bad_sum == 0)
        report(f"gamma_in independent of tie-breaking (3 random orders per prime)", bad_tie == 0)


# ======================= Part 3: inner entry bounds =======================
def part3(configs, samples):
    random.seed(6)
    for K, M, p in configs:
        I = Inner(K, M, p)
        N, h, m = I.N, I.h, I.m
        x = K / p
        # side conditions used in the proof of Prop 4.1
        deg_ord = max(2 * (I.Z[c]) + 6 * I.lN[c] for c in range(1, m + 1))  # nu_i+nu_j+6 l_N <= 2(T+1)
        deg_zero = 5 + 4 * I.L0 + 12 * (N // p)
        print(f"== inner K={K} M={M} p={p}: x=K/p={x:.3f}, N={N}, h={h}, m={m}, T={I.T}, E={I.E}, L0={I.L0}")
        print(f"   hypotheses: K>=200M^2 {K >= 200*M*M}, 3<=x<M {3 <= x < M}, p>200M {p > 200*M}, "
              f"p^2>5K {p*p > 5*K}, ordinary degree {deg_ord}<=p+1 {deg_ord <= p+1}, "
              f"zero degree {deg_zero}<=p+1 {deg_zero <= p+1}, min L_a {min(I.La)}")
        if min(I.La) < 0 or sum(I.La) != h:
            print("   skipped: basis not defined")
            continue
        idx = [(a, i) for a in range(m + 1) for i in range(I.La[a])]
        # unimodularity: coefficient matrix mod p has full rank
        facs = [T + c * c for c in range(m + 1)]
        Pall = fmpq_poly([1])
        for c in range(m + 1):
            Pall *= facs[c] ** I.La[c]
        basis = {}
        for a, i in idx:
            basis[(a, i)] = Pall // facs[a] ** (I.La[a] - i)
        rows = []
        for key in idx:
            b = basis[key]
            rows.extend(int(b[d]) % p for d in range(h))
        rk = nmod_mat(h, h, rows, p).rank()
        report(f"   (4.5) basis is Z_p-unimodular (rank mod p = {rk}/{h})", rk == h)
        # sample entries: all zero-block pairs with small i, plus random pairs
        DN5 = sqPoleProd(range(1, N + 1)) ** 5
        S = tuple(range(N + 1, K + 1))
        pairs = [((0, i), (0, j)) for i in range(0, I.L0, 5) for j in range(i, I.L0, 5)]
        pairs += [((0, i), random.choice(idx)) for i in range(0, I.L0, 3)]
        while len(pairs) < samples:
            pairs.append((random.choice(idx), random.choice(idx)))
        viol = 0
        slack_min = None
        worst = None
        t0 = time.time()
        for x_, y_ in pairs:
            val = muX(S, DN5 * basis[x_] * basis[y_])
            v = vpG(val, p)
            b2 = I.w2(*x_) + I.w2(*y_)  # 2 * (w_x + w_y)
            slack2 = 2 * v - b2
            if slack2 < 0:
                viol += 1
                worst = (x_, y_, v, Fr(b2, 2))
            if slack_min is None or slack2 < slack_min:
                slack_min = slack2
        report(f"   (4.2)/(4.3) entry bounds on {len(pairs)} entries", viol == 0,
               f"{viol} violations; min slack {Fr(slack_min, 2)}; {time.time()-t0:.0f}s"
               + (f"; e.g. entry {worst[0]},{worst[1]}: v={worst[2]} < {worst[3]}" if worst else ""))


# ======================= Part 4: outer range =======================
def outer_hyp(K, p):
    N = 3 * K // 40
    return 7 <= p <= K < 3 * p and 2 * K < p * p and 2 * N < p and 5 * N <= 2 * p - 2


def gamma_out(K, p):
    N = 3 * K // 40
    v = K % p
    u = max(0, N + v - p + 1)
    tp = min(N, v) + u
    rp = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * tp - 1 - min(rp, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * tp - min(rp, p + u)


def ell_nat(p, A, a):
    return sum(1 for j in range(1, A + 1) if j % p == a % p or (j + a) % p == 0)


def rat_mod_p(r, p):
    r = fmpq(r)
    return (int(r.p) * pow(int(r.q), -1, p)) % p


def part4(Ks):
    for K in Ks:
        N, h = 3 * K // 40, 37 * K // 40
        S = tuple(range(N + 1, K + 1))
        DN5 = sqPoleProd(range(1, N + 1)) ** 5
        for p in [p for p in primes(7, K) if outer_hyp(K, p)]:
            t0 = time.time()
            m = (p - 1) // 2
            rp = max(0, K + 4 * N - 2 * p + 2)
            def mono_mod(e, p=p):
                if e < 2 * p - 3:
                    return muMono(e)
                return muMono(e) - fmpq(rat_mod_p(p * muMono(e), p), p)
            # (4.10): G = A + L/p, L constant, integral, rank <= r_p (Hankel in i+j)
            Gs = [muX(S, DN5 * T**e) for e in range(2 * h - 1)]
            As = [muX(S, DN5 * T**e, mono_mod) for e in range(2 * h - 1)]
            Ls = [(p * (g[0] - a[0]), p * (g[1] - a[1])) for g, a in zip(Gs, As)]
            L_const = all(l[1] == 0 for l in Ls)
            L_int = all(vp(l[0], p) >= 0 for l in Ls)
            Lm = fmpq_mat(h, h, [Ls[i + j][0] for i in range(h) for j in range(h)])
            rk = Lm.rank()
            ok410 = L_const and L_int and rk <= rp
            # outer basis (4.11), zero class read as P_0 (t+p^2)^i
            classes = {}
            for a in range(m + 1):
                classes[a] = [j for j in S if j % p == a % p or (j + a) % p == 0]
            idx = []
            basis = {}
            w2 = {}
            for a in range(m + 1):
                Pa = sqPoleProd([j for j in S if j not in classes[a]])
                cnt = len(classes[a])
                if a == 0:
                    for i in range(cnt):
                        idx.append((0, i))
                        basis[(0, i)] = Pa * (T + p * p) ** i
                        w2[(0, i)] = -1 if cnt == 1 else (-4 if i == 0 else 0)
                    continue
                l = ell_nat(p, K, a)
                delta = 1 if a <= N else 0
                assert cnt == l - delta, (K, p, a)
                Ea = sqPoleProd([j for j in classes[a] if j > p])
                for i in range(cnt):
                    idx.append((a, i))
                    if i < l - 2:
                        basis[(a, i)] = Pa * (T + a * a) ** i
                        w2[(a, i)] = min(0, 2 * (i + 3 * delta) - (l + 4))
                    else:
                        basis[(a, i)] = Pa * Ea * (T + a * a) ** (i - (l - 2))
                        w2[(a, i)] = 0
            ok_count = len(idx) == h
            rows = []
            for key in idx:
                b = basis[key]
                rows.extend(rat_mod_p(b[d], p) for d in range(h))
            unimod = nmod_mat(h, h, rows, p).rank() == h
            # entry bounds (4.12)
            viol = {"ord": 0, "zero": 0}
            slack_min = None
            worst = None
            for ai, x_ in enumerate(idx):
                for y_ in idx[ai:]:
                    val = muX(S, DN5 * basis[x_] * basis[y_], mono_mod)
                    v = vpG(val, p)
                    s2 = 2 * v - (w2[x_] + w2[y_])
                    if s2 < 0:
                        kind = "zero" if 0 in (x_[0], y_[0]) else "ord"
                        viol[kind] += 1
                        worst = (x_, y_, v, Fr(w2[x_] + w2[y_], 2))
                    slack_min = s2 if slack_min is None else min(slack_min, s2)
            z = sum(1 for k in idx if w2[k] == 0)
            g_sum2 = 2 * sum(w2.values()) - 2 * min(rp, z)  # doubled
            ok_sum = g_sum2 == 2 * gamma_out(K, p)
            ok = ok410 and ok_count and unimod and viol["ord"] == 0 and viol["zero"] == 0 and ok_sum
            report(f"outer K={K:>3} p={p:>3}: (4.10) {'ok' if ok410 else 'FAIL'} (rank L={rk} <= r_p={rp}), "
                   f"basis size {len(idx)}/{h}, unimodular {unimod}, (4.12) violations "
                   f"ord={viol['ord']} zero={viol['zero']} (min slack {Fr(slack_min, 2)}), "
                   f"2sum w - min(r,z) = gamma_out {ok_sum} ({Fr(g_sum2, 2)} vs {gamma_out(K, p)})",
                   ok, (f"e.g. {worst}" if worst else "") + f" [{time.time()-t0:.0f}s]")


if __name__ == "__main__":
    parts = sys.argv[1:] or ["1", "2", "3", "4"]
    if "1" in parts:
        part1()
    if "2" in parts:
        part2()
    if "4" in parts:
        part4([40, 80, 120])
    if "3" in parts:
        part3([(360, 4, 109), (400, 4, 109), (400, 5, 127), (440, 4, 113)], samples=150)
    print(f"\nfailures: {fails}")
