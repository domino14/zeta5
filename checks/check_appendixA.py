"""Phase 1.2: Appendix A. The comparison measure rho, the potential bound (A.9)/(6.2),
the energy formula (A.2), the enclosures (A.10), and kappa in (A.11)/(C.6).

Rigorous checks use flint `arb` ball arithmetic: a comparison is reported OK only if it
holds for the whole ball. The quadratures and dense scans are independent floating-point
cross-checks.
"""
import math
import time
from fractions import Fraction as Fr

import mpmath
from flint import arb, ctx

ctx.prec = 200
T0 = time.time()

def ok(name, cond, detail=""):
    print(f"[{'OK ' if cond else 'MISMATCH'}] {name}" + (f": {detail}" if detail else ""))
    return cond

# ---------------------------------------------------------------- data
TABLE1 = [(3906748086, 8992695531, 10515596180), (2312248264, 15340997855, 29471737793),
          (1402286665, 25730180724, 42934365099), (881725356, 41909578246, 58204231966),
          (578197906, 65851089563, 69037621310), (396324613, 99481037884, 78873099189),
          (283911191, 144325727458, 84856120711), (212206188, 201105762729, 88396082127),
          (165097686, 269345996903, 88303382125), (133347132, 347089554156, 85472321255),
          (111522114, 430806704415, 78899184238), (96349355, 515561896511, 70353471918),
          (85815639, 595448778546, 58838976615), (78667711, 664241383483, 44421321106),
          (74129565, 716160577112, 30462865791), (71741310, 746637295669, 5959622577)]
S12 = 10**12
A = [Fr(a, S12) for a, _, _ in TABLE1]
B = [Fr(b, S12) for _, b, _ in TABLE1]
Cw = [Fr(c, S12) for _, _, c in TABLE1]
alpha, lam = Fr(3, 40), Fr(37, 40)
M0 = Fr(-1329, 200)
U = Fr(-2733991, 2000000)
BOUND_A9 = Fr(-6645002, 10**6)
qm, qp = Fr(59205077, 10**10), Fr(59205079, 10**10)

def ab(x):
    return arb(x.numerator) / x.denominator if isinstance(x, Fr) else arb(x)

PI = arb.pi()

# ---------------------------------------------------------------- potentials
def U_unit_arb(a, b, t):
    """(A.1) for exact rationals a < b, t."""
    if a <= t <= b:
        return ab((b - a) / 4).log()
    m = (a + b) / 2
    return ((ab(abs(t - m)) + ab((t - a) * (t - b)).sqrt()) / 2).log()

def Urho_arb(t):
    return sum((ab(c) * U_unit_arb(a, b, t) for a, b, c in zip(A, B, Cw)), arb(0))

def V_arb(t, sq_lo=None, sq_hi=None):
    """(A.5) at exact rational t > 0; V(0) = -12 alpha log alpha - 2 + 12 alpha."""
    if t == 0:
        return -12 * ab(alpha) * ab(alpha).log() - 2 + 12 * ab(alpha)
    st = ab(t).sqrt()
    return ((1 + ab(t)).log() - 6 * ab(alpha) * (ab(t) + ab(alpha**2)).log() - 2 + 12 * ab(alpha)
            + 2 * st * (PI + (1 / st).atan() - 6 * (ab(alpha) / st).atan()))

Af = [float(x) for x in A]; Bf = [float(x) for x in B]; Cf = [float(x) for x in Cw]
alf = 3 / 40

def U_unit_f(a, b, t):
    if a <= t <= b:
        return math.log((b - a) / 4)
    return math.log((abs(t - (a + b) / 2) + math.sqrt((t - a) * (t - b))) / 2)

def Urho_f(t):
    return sum(c * U_unit_f(a, b, t) for a, b, c in zip(Af, Bf, Cf))

def V_f(t):
    if t == 0:
        return -12 * alf * math.log(alf) - 2 + 12 * alf
    st = math.sqrt(t)
    return (math.log(1 + t) - 6 * alf * math.log(t + alf**2) - 2 + 12 * alf
            + 2 * st * (math.pi + math.atan(1 / st) - 6 * math.atan(alf / st)))

# ================================================================ 0. Table 1 sanity
print("== Table 1")
ok("sum c_j = 37/40", sum(Cw) == lam)
ok("nesting 0 < a16 < ... < a1 < b1 < ... < b16 < 2",
   0 < A[15] and all(A[j + 1] < A[j] for j in range(15)) and A[0] < B[0]
   and all(B[j] < B[j + 1] for j in range(15)) and B[15] < 2)
ok("b_j - a_j > 1/225", all(b - a > Fr(1, 225) for a, b in zip(A, B)),
   f"min length {float(min(b - a for a, b in zip(A, B))):.6f}")

# ================================================================ 1. (A.1)
print("== 1. (A.1) arcsine potential vs quadrature")
mpmath.mp.dps = 30
def U_unit_quad(a, b, t):
    m, r = (a + b) / 2, (b - a) / 2
    f = lambda th: mpmath.log(abs(t - m - r * mpmath.cos(th)))
    if a < t < b:
        th0 = mpmath.acos((t - m) / r)
        return (mpmath.quad(f, [0, th0]) + mpmath.quad(f, [th0, mpmath.pi])) / mpmath.pi
    return mpmath.quad(f, [0, mpmath.pi]) / mpmath.pi
for (a, b, t) in [(Fr(1, 5), Fr(9, 10), Fr(1, 2)), (Fr(1, 5), Fr(9, 10), Fr(0)),
                  (Fr(1, 5), Fr(9, 10), Fr(3, 2)), (A[3], B[3], Fr(1, 100))]:
    got = U_unit_arb(a, b, t)
    q = U_unit_quad(mpmath.mpf(a.numerator) / a.denominator, mpmath.mpf(b.numerator) / b.denominator,
                    mpmath.mpf(t.numerator) / t.denominator)
    ok(f"U_[{float(a):.4f},{float(b):.4f}]({float(t)})", abs(float(got.mid()) - float(q)) < 1e-12,
       f"formula {float(got.mid()):.15f}, quadrature {float(q):.15f}")

# continuity at the endpoints: the outside branch at t = a, b equals log((b-a)/4) exactly
ok("(A.1) branches agree at the endpoints (exact: (|b-m| + 0)/2 = (b-a)/4)",
   all(abs(Fr(b) - (a + b) / 2) / 2 == (b - a) / 4 and abs(a - (a + b) / 2) / 2 == (b - a) / 4
       for a, b in zip(A, B)))

# ================================================================ 2. (A.5)
print("== 2. (A.5) closed form of V vs definition (6.1)")
def V_def(t):
    t = mpmath.mpf(t)
    return (2 * mpmath.pi * mpmath.sqrt(t) + mpmath.quad(lambda u: mpmath.log(t + u * u), [0, 1])
            - 6 * mpmath.quad(lambda u: mpmath.log(t + u * u), [0, mpmath.mpf(3) / 40]))
for t in [Fr(1, 100), Fr(3, 10), Fr(1), Fr(17, 10), Fr(5)]:
    got = float(V_arb(t).mid())
    want = float(V_def(float(t)))
    ok(f"V({float(t)})", abs(got - want) < 1e-12, f"(A.5) {got:.15f}, (6.1) {want:.15f}")
v0 = float(V_def(0)) if False else float(2 * 0 + mpmath.quad(lambda u: 2 * mpmath.log(u), [0, 1])
                                          - 6 * mpmath.quad(lambda u: 2 * mpmath.log(u), [0, mpmath.mpf(3) / 40]))
ok("V(0) = -12 a log a - 2 + 12 a", abs(float(V_arb(Fr(0)).mid()) - v0) < 1e-12,
   f"{float(V_arb(Fr(0)).mid()):.15f} vs {v0:.15f}")
ok("V continuous at 0 (V(1e-12) ~ V(0))", abs(V_f(1e-12) - V_f(0)) < 1e-4)

# ================================================================ 3. Phi
print("== 3. Phi(y) = V(y^2): minimum location")
ystar2 = (6 * alpha - alpha**2) / (1 - 6 * alpha)
ok("Phi'' = 0 at y^2 = 711/880", ystar2 == Fr(711, 880))
def dPhi(y):  # y an arb
    return 2 * (PI + (1 / y).atan() - 6 * (ab(alpha) / y).atan())
dm, dp = dPhi(ab(qm).sqrt()), dPhi(ab(qp).sqrt())
ok("Phi'(sqrt q-) < 0 (rigorous)", dm < 0, dm.str(5))
ok("Phi'(sqrt q+) > 0 (rigorous)", dp > 0, dp.str(5))
ok("Phi'(0+) = -3 pi, Phi'(inf) = 2 pi", abs(float(dPhi(arb("1e-30")).mid()) + 3 * math.pi) < 1e-12
   and abs(float(dPhi(arb("1e30")).mid()) - 2 * math.pi) < 1e-12)
# Phi''(y) = 12a(1+y^2) - 2(a^2+y^2) over positive denominators: > 0 for y^2 < 711/880, < 0 after.
# So Phi' increases from -3pi to Phi'(y*), then decreases to 2pi > 0. Hence Phi' has exactly one
# zero, and it lies before y*, iff Phi'(y*) > 0; after y*, Phi' > 2pi > 0.
ok("Phi''(0) > 0 (Phi' increasing first)", -2 + 12 / alpha > 0)
ok("Phi'(y*) > 0 at the inflection point (so V has exactly one critical point)",
   dPhi(ab(ystar2).sqrt()) > 0, dPhi(ab(ystar2).sqrt()).str(5))
ok("q+ < 711/880 (the bracket lies in the increasing branch)", qp < ystar2)

# ================================================================ 4. energy
print("== 4. I(rho): (A.2), quadrature, (A.10)")
Spart = [Fr(0)]
for c in Cw:
    Spart.append(Spart[-1] + c)
I_arb = sum(((ab(Spart[j + 1]**2 - Spart[j]**2)) * ab((B[j] - A[j]) / 4).log() for j in range(16)), arb(0))
print(f"  I(rho) via (A.2) = {I_arb.str(15)}")
nq = 20000
Iq = 0.0
for a, b, c in zip(Af, Bf, Cf):
    m, r = (a + b) / 2, (b - a) / 2
    s = 0.0
    for k in range(1, nq + 1):
        s += Urho_f(m + r * math.cos((2 * k - 1) * math.pi / (2 * nq)))
    Iq += c * s / nq
ok("(A.2) vs Gauss-Chebyshev quadrature of U^rho d rho", abs(Iq - float(I_arb.mid())) < 1e-6,
   f"quadrature {Iq:.10f}, (A.2) {float(I_arb.mid()):.10f}, diff {Iq - float(I_arb.mid()):.2e}")
ok("(A.10) -2126593445148e-12 < I(rho) < -2126593445147e-12 (rigorous)",
   (I_arb > ab(Fr(-2126593445148, S12))) and (I_arb < ab(Fr(-2126593445147, S12))), I_arb.str(15))
Cstar = (-2 * ab(lam) + 12 * ab(alpha) * ab(lam) * (1 - ab(alpha).log()) + 3 * ab(lam)**2
         - 2 * ab(lam)**2 * (2 * ab(lam)).log())
ok("(A.10) 2653035990340e-12 < C* < 2653035990341e-12 (rigorous)",
   (Cstar > ab(Fr(2653035990340, S12))) and (Cstar < ab(Fr(2653035990341, S12))), Cstar.str(15))
tot = ab(lam * M0) - I_arb + Cstar
ok("(6.4) lambda M0 - I(rho) + C* < U (rigorous)", tot < ab(U),
   f"{tot.str(12)} vs U = {float(U)}; slack {float((ab(U) - tot).mid()):.3e}")
ok("  ... and < -1366995564511e-12 (rigorous)", tot < ab(Fr(-1366995564511, S12)))

# ================================================================ 5. Table 2
print("== 5. Table 2 partition and B(l, r) (A.7)-(A.9)")
def rng(a, b):
    return list(range(a, b + 1))
TABLE2 = [(0, 1, [0]), (0, 2, [2, 3])] + [(j, 0, [0]) for j in range(1, 9)] + [
    (9, 1, [0, 1]), (10, 1, [0, 1]), (11, 1, [0, 1]), (12, 1, [0]), (12, 2, [2, 3]),
    (13, 2, rng(0, 3)), (14, 2, rng(0, 3)), (15, 1, [0]), (15, 2, [2, 3]),
    (16, 0, [0]), (17, 0, [0]), (18, 0, [0]),
    (19, 1, [1]), (19, 3, [0, 2, 3]), (19, 4, [2, 3]),
    (20, 2, [3]), (20, 3, [4, 5]), (20, 4, [0, 1, 6, 7]), (20, 5, rng(4, 11)),
    (21, 2, [3]), (21, 3, [5]), (21, 4, [0] + rng(7, 9)), (21, 5, rng(2, 4) + rng(10, 13)),
    (21, 6, rng(10, 19)),
    (22, 3, rng(5, 7)), (22, 4, [0, 8, 9]), (22, 5, [2, 3] + rng(12, 15)), (22, 6, rng(8, 23)),
    (23, 3, [6, 7]), (23, 4, rng(9, 11)), (23, 5, rng(0, 2) + rng(14, 17)),
    (23, 6, rng(6, 13) + rng(19, 27)), (23, 7, rng(28, 37)),
    (24, 3, [6, 7]), (24, 4, [10, 11]), (24, 5, rng(0, 2) + rng(15, 19)),
    (24, 6, rng(6, 11) + rng(22, 29)), (24, 7, rng(24, 43)),
    (25, 3, [7]), (25, 4, rng(10, 13)), (25, 5, rng(0, 2) + rng(16, 19)),
    (25, 6, rng(6, 11) + rng(24, 31)), (25, 7, rng(24, 47)),
    (26, 3, [7]), (26, 4, rng(11, 13)), (26, 5, rng(0, 2) + rng(17, 21)),
    (26, 6, rng(6, 11) + rng(25, 33)), (26, 7, rng(24, 49)),
    (27, 4, rng(11, 15)), (27, 5, rng(0, 2) + rng(17, 21)), (27, 6, rng(6, 11) + rng(26, 33)),
    (27, 7, rng(24, 51)),
    (28, 4, rng(12, 15)), (28, 5, rng(0, 2) + rng(18, 23)), (28, 6, rng(6, 11) + rng(27, 35)),
    (28, 7, rng(24, 53)),
    (29, 4, rng(13, 15)), (29, 5, rng(0, 2) + rng(19, 25)), (29, 6, rng(6, 12) + rng(27, 37)),
    (29, 7, rng(26, 53)),
    (30, 4, rng(13, 15)), (30, 5, rng(0, 2) + rng(20, 25)), (30, 6, rng(6, 14) + rng(26, 39)),
    (30, 7, rng(30, 51)),
    (31, 4, [14, 15]), (31, 5, rng(0, 2) + rng(20, 27)), (31, 6, rng(6, 39)),
    (32, 4, [15]), (32, 5, rng(0, 4) + rng(19, 29)), (32, 6, rng(10, 37)),
    (33, 4, [0, 15]), (33, 5, rng(2, 29)),
    (34, 2, [2, 3]), (34, 3, [3]), (34, 4, rng(3, 5)), (34, 5, [4, 5]), (34, 6, rng(5, 7)),
    (34, 7, rng(6, 9)), (34, 8, rng(7, 11)), (34, 9, rng(5, 13)), (34, 10, rng(0, 9)),
]
Anodes = [Fr(0)] + [A[16 - j] for j in range(1, 17)] + [qm, qp] + [B[j - 1] for j in range(1, 17)] + [Fr(2)]
assert len(Anodes) == 36
ok("A_0 < A_1 < ... < A_35", all(x < y for x, y in zip(Anodes, Anodes[1:])))
intervals = []
for j, d, ks in TABLE2:
    Aj, Aj1 = Anodes[j], Anodes[j + 1]
    for k in ks:
        intervals.append((Aj + (Aj1 - Aj) * Fr(k, 2**d), Aj + (Aj1 - Aj) * Fr(k + 1, 2**d), (j, d, k)))
intervals.sort()
problems = []
if intervals[0][0] != 0:
    problems.append(f"starts at {intervals[0][0]}")
if intervals[-1][1] != 2:
    problems.append(f"ends at {intervals[-1][1]}")
for (l1, r1, t1), (l2, r2, t2) in zip(intervals, intervals[1:]):
    if r1 < l2:
        problems.append(f"gap ({float(r1)}, {float(l2)}) between {t1} and {t2}")
    elif r1 > l2:
        problems.append(f"overlap at {float(l2)}..{float(r1)} between {t1} and {t2}")
ok(f"Table 2: {len(intervals)} intervals partition [0, 2]", not problems, "; ".join(problems[:10]))

Vstar = ((1 + ab(qm)).log() - 6 * ab(alpha) * (ab(qp) + ab(alpha**2)).log() - 2 + 12 * ab(alpha)
         + 2 * ab(qp).sqrt() * (PI + (1 / ab(qp).sqrt()).atan() - 6 * (ab(alpha) / ab(qm).sqrt()).atan()))
par = PI + (1 / ab(qp).sqrt()).atan() - 6 * (ab(alpha) / ab(qm).sqrt()).atan()
ok("(A.6) parenthesis is negative", par < 0, par.str(5))
# independent float check that V* <= min V on [q-, q+]
vmin = min(V_f(float(qm) + (float(qp) - float(qm)) * i / 1000) for i in range(1001))
ok("V* <= min of V on [q-, q+] (float)", float(Vstar.mid()) <= vmin,
   f"V* = {float(Vstar.mid()):.15f}, min V = {vmin:.15f}")

Ucache = {}
def Ur(t):
    if t not in Ucache:
        Ucache[t] = Urho_arb(t)
    return Ucache[t]
worst = None
fails = []
for l, r, tag in intervals:
    Umax = Ur(l) if Ur(l) > Ur(r) else Ur(r)
    if not (Ur(l) > Ur(r) or Ur(r) > Ur(l)):  # overlapping balls: take the ball-union upper bound
        Umax = Ur(l).union(Ur(r))
    if r <= qm:
        Vpart = V_arb(r)
    elif l >= qp:
        Vpart = V_arb(l)
    else:
        Vpart = Vstar
    Bv = 2 * Umax - Vpart
    if not (Bv < ab(BOUND_A9)):
        fails.append((tag, float(l), float(r), Bv.str(10)))
    if worst is None or float(Bv.mid()) > worst[0]:
        worst = (float(Bv.mid()), tag, float(l), float(r))
ok(f"(A.9) B(l,r) < -6645002/10^6 on all {len(intervals)} intervals (rigorous)", not fails,
   f"{len(fails)} failures: {fails[:5]}" if fails else "")
print(f"  max B = {worst[0]:.9f} on row (j,d,k)={worst[1]}, [{worst[2]:.9f}, {worst[3]:.9f}]; "
      f"slack to -6.645002: {-6.645002 - worst[0]:.3e}")
ok("-6645002/10^6 < M0 = -1329/200", BOUND_A9 < M0)

# ================================================================ 6. t >= 2 and dense scans
print("== 6. t >= 2 and dense scans of 2U^rho - V")
def bound68(t):  # arb
    return ab(Fr(13, 10)) * ab(t).log() + 6 * ab(alpha)**3 / ab(t) - 2 * PI * ab(t).sqrt()
b2 = bound68(Fr(2))
ok("(6.8) at t = 2 is < -1329/200 (rigorous)", b2 < ab(M0), b2.str(8))
# derivative 13/(10t) - 6a^3/t^2 - pi/sqrt(t) < 13/(10t) - pi/sqrt(t) < 0 iff sqrt(t) > 13/(10 pi): true for t >= 2
ok("(6.8) decreasing on [2, inf) (derivative < 13/(10t) - pi/sqrt t < 0 since sqrt 2 > 13/(10 pi))",
   math.sqrt(2) > 13 / (10 * math.pi))
# the claimed shortcuts: log 2 < 7/10, pi > 3, sqrt 2 > 7/5
ok("shortcut inequalities log 2 < 7/10, sqrt 2 > 7/5", math.log(2) < 0.7 and 2 > (7 / 5)**2)
# (6.8) is an upper bound for t >= 2 (float scan)
viol68 = 0
worst68 = -1e9
for i in range(20001):
    t = 2 * (500 ** (i / 20000))
    diff = (2 * Urho_f(t) - V_f(t)) - float(bound68(Fr(t)).mid())
    worst68 = max(worst68, diff)
    viol68 += diff > 1e-12
ok("(6.8) holds on [2, 1000] (20001 log-spaced points)", viol68 == 0,
   f"max of (2U - V) - bound = {worst68:.3e}")

def f_scan(t):
    return 2 * Urho_f(t) - V_f(t)
pts = [2 * i / 200000 for i in range(200001)]
for x in list(Af) + list(Bf) + [float(qm), float(qp)]:
    pts += [x + s * 10**(-e) for e in range(3, 13) for s in (-1, 1)]
pts = [t for t in pts if 0 <= t <= 2]
best = max((f_scan(t), t) for t in pts)
ok(f"scan of [0, 2] ({len(pts)} points): max 2U^rho - V < -6.645002", best[0] < -6.645002,
   f"max {best[0]:.9f} at t = {best[1]:.9f}; margin to M0 = {float(M0) - best[0]:.3e}")
best2 = max((f_scan(2 * 500 ** (i / 50000)), 2 * 500 ** (i / 50000)) for i in range(50001))
ok("scan of [2, 1000]: max 2U^rho - V < M0", best2[0] < float(M0), f"max {best2[0]:.6f} at t = {best2[1]:.4f}")
# local maxima of the scan on [0, 2] (where the bound is tightest)
vals = [(t, f_scan(t)) for t in [2 * i / 200000 for i in range(200001)]]
locmax = sorted(((v, t) for (tp, vp), (t, v), (tn, vn) in zip(vals, vals[1:], vals[2:]) if v >= vp and v >= vn),
                reverse=True)[:5]
print("  top local maxima on [0,2]: " + ", ".join(f"t={t:.5f}: {v:.7f}" for v, t in locmax))

# ================================================================ 7. kappa (C.6), (A.11)
print("== 7. kappa (C.6) and (A.11)")
kappa = (2 * PI / arb(3).sqrt() + (ab(Fr(4, 3))).log() + ab(Fr(9, 20)) * arb(18).log()
         + ab(Fr(37, 40)) * (1 + ab(Fr(1600, 111)).log())
         + ab(Fr(37, 20)) * ((43 + 4 * arb(114).sqrt()) / 5).log())
ok("(A.11) 2773171335773/2e11 < kappa < 6932928339433/5e11 (rigorous)",
   (kappa > ab(Fr(2773171335773, 200000000000))) and (kappa < ab(Fr(6932928339433, 500000000000))),
   kappa.str(15))
ok("(C.6) kappa < 6933/500 (rigorous)", kappa < ab(Fr(6933, 500)))
ok("(C.6) Y = (2+a+b)/(b-a) = 43/5 at a = 1/18, b = 1/3",
   (2 + Fr(1, 18) + Fr(1, 3)) / (Fr(1, 3) - Fr(1, 18)) == Fr(43, 5))
ok("(C.6) R = Y + sqrt(Y^2-1) = (43 + 4 sqrt 114)/5", Fr(43, 5)**2 - 1 == Fr(16 * 114, 25))

print(f"runtime {time.time() - T0:.1f}s")
