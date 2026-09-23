"""Phase 1.1: recompute the exact rational constants of the paper from their definitions.

Everything uses exact Fractions. Paper values are hard-coded only for comparison.
"""
from fractions import Fraction as Fr
from math import floor

alpha = Fr(3, 40)
lam = Fr(37, 40)
H = 1 + 2 * alpha

def ok(name, got, want):
    status = "OK " if got == want else "MISMATCH"
    print(f"[{status}] {name}: got {got}" + ("" if got == want else f", paper {want}"))
    return got == want

def pos(v):
    return v if v > 0 else Fr(0)

def frac(v):
    return v - floor(v)

# ---------- simple identities ----------
ok("H", H, Fr(23, 20))
ok("quadratic cancellation (B)", 2*lam - 12*lam*alpha + 2*(H**2 - H - lam**2) - 18*alpha**2 + 6*alpha, Fr(0))
ok("lambda*M0", lam * Fr(-1329, 200), Fr(-49173, 8000))

c_table = [10515596180, 29471737793, 42934365099, 58204231966, 69037621310, 78873099189,
           84856120711, 88396082127, 88303382125, 85472321255, 78899184238, 70353471918,
           58838976615, 44421321106, 30462865791, 5959622577]
ok("sum c_j (Table 1)", Fr(sum(c_table), 10**12), Fr(37, 40))

# ---------- inner limiting function R(x), eqs (5.4)-(5.6), straight from definitions ----------
def ell(x, z):
    return floor(x - z) + floor(x + z) + 1

def z_integral(fn, xs):
    """Exact integral over z in (0,1/2) of a function piecewise constant in z,
    with breakpoints at {x}, 1-{x} for x in xs."""
    pts = {Fr(0), Fr(1, 2)}
    for x in xs:
        for b in (frac(x), 1 - frac(x)):
            if 0 < b < Fr(1, 2):
                pts.add(b)
    pts = sorted(pts)
    total = Fr(0)
    for a, b in zip(pts, pts[1:]):
        total += (b - a) * fn((a + b) / 2)
    return total

def Gamma(x):
    T = floor(2 * H * x)
    s = H * x - Fr(T, 2)
    q = floor(2 * x)
    nplus = (2 * x - q) / 2
    integ = z_integral(lambda z: (T - 3 * ell(alpha * x, z)) * (T + 3 * ell(alpha * x, z) - ell(x, z) - 5),
                       [x, alpha * x])
    return integ + s * (2 * T - q - 5) + pos(s - nplus)

def J(u):
    m = floor(2 * u)
    return m * u - Fr(m * (m + 1), 4)

def Nfun(x):
    return 2 * lam * x * floor(x) - 12 * lam * x * floor(alpha * x) - 2 * J(lam * x)

def R(x):
    return -Gamma(x) - Nfun(x)

def breakpoints(lo, hi, cs, extra=()):
    pts = {Fr(lo), Fr(hi), *[Fr(e) for e in extra]}
    for c in cs:
        k = floor(c * lo)
        while Fr(k) / c <= hi:
            x = Fr(k) / c
            if lo < x < hi:
                pts.add(x)
            k += 1
    return sorted(pts)

def integrate_affine(fn, pts, weight_power, label):
    """Integrate fn(x) * x^-weight_power over pts, verifying fn is affine on each piece."""
    total = Fr(0)
    bad = 0
    for l, r in zip(pts, pts[1:]):
        samples = [l + (r - l) * Fr(k, 8) for k in range(1, 8)]
        vals = [fn(s) for s in samples]
        a = (vals[-1] - vals[0]) / (samples[-1] - samples[0])
        b = vals[0] - a * samples[0]
        if any(v != a * s + b for s, v in zip(samples, vals)):
            bad += 1
            print(f"  {label}: NOT affine on [{l}, {r}]")
        if weight_power == 3:
            total += a * (1 / l - 1 / r) + b / 2 * (1 / l**2 - 1 / r**2)
        else:
            total += a * (r**2 - l**2) / 2 + b * (r - l)
    return total, bad

# Generous breakpoint set: every x in [3,20] where c*x is an integer, for many c.
C_inner = [Fr(1), Fr(2), alpha, 2*alpha, 4*alpha, 2*lam, 2*H, 2*(1-alpha), 2*(1+alpha), 1-alpha, 1+alpha, 4*H, 4*lam]
pts = breakpoints(3, 20, C_inner)
inner, bad = integrate_affine(R, pts, 3, "R")
print(f"  inner: {len(pts)-1} pieces, non-affine pieces: {bad}")
ok("(5.18) int_3^20 R(x)/x^3", inner, Fr(322437603634266857629, 7535670527041937280000))

# Table 3 spot check: unit intervals
t3 = {3: Fr(26807, 161280), 4: Fr(37383, 704000), 5: Fr(37523, 8236800)}
for j, want in t3.items():
    got, _ = integrate_affine(R, [p for p in pts if j <= p <= j + 1], 3, "R")
    ok(f"Table 3 row {j}", got, want)

# ---------- tail pieces (5.16)/(5.17): P(20), C(20), P(M), C(M) ----------
def G0(v):
    return v * (1 - v) * (2 * v - 1) / 6

def Pfun(x):
    f, g = frac(x), frac(alpha * x)
    return Fr(74) * g * (1 - g) - lam * f * (1 - f)

def Cfun(x):
    f, g = frac(x), frac(alpha * x)
    return Fr(74) / alpha * G0(g) - lam * G0(f)

ok("P(20)", Pfun(Fr(20)), Fr(37, 2))
ok("C(20)", Cfun(Fr(20)), Fr(0))
ok("P(200)", Pfun(Fr(200)), Fr(0))
ok("C(200)", Cfun(Fr(200)), Fr(0))

# mean of P over a period (period 40 in x)
Pbar_pts = breakpoints(0, 40, [Fr(1), alpha])
# P is quadratic; integrate exactly with Simpson on each piece
Pbar = sum((r - l) / 6 * (Pfun(l + (r - l) * Fr(1, 10**9)) * 0 + Pfun((l + r) / 2) * 4 + Pfun(l) + Pfun(r))
           for l, r in zip(Pbar_pts, Pbar_pts[1:])) / 40
# endpoints at breakpoints: use one-sided limits via tiny offsets would be needed; check with midpoint-based Simpson instead
def simpson_open(fn, l, r):
    e = (r - l) * Fr(1, 10**12)
    return (r - l) / 6 * (fn(l + e) + 4 * fn((l + r) / 2) + fn(r - e))
Pbar2 = sum(simpson_open(Pfun, l, r) for l, r in zip(Pbar_pts, Pbar_pts[1:])) / 40
print(f"  mean of P ~ {float(Pbar2):.12f}, paper 2923/240 = {2923/240:.12f}")

# ---------- outer integral (5.10) ----------
def R0(y):
    if Fr(1, 3) < y < Fr(1, 2):
        return 8 - 9*y - 8*alpha - 5*min(alpha, 1 - 2*y) - 5*pos(1 + alpha - 3*y)
    if Fr(1, 2) < y < 1:
        return 7*(1 - y) - 6*min(alpha, 1 - y) - 6*pos(1 + alpha - 2*y) + pos(1 + 4*alpha - 2*y)
    return Fr(0)

def dfun(y):
    if Fr(1, 3) < y < Fr(1, 2):
        return pos((1 + 4*alpha - 3*y) - pos(1 + alpha - 3*y))
    return Fr(0)

def Tout(y):
    return R0(y) - dfun(y) - 2*lam*floor(1/y) + sum(pos(2*lam - j*y) for j in range(1, 6))

ypts = [Fr(1, 3), Fr(1, 2), Fr(1), 2*lam]
extra = set()
for c in [Fr(1), Fr(2), Fr(3)]:
    for k in range(-5, 10):
        for base in [Fr(0), alpha, 4*alpha, 1+alpha, 1+4*alpha]:
            y = (base + k) / c if c else None
            extra.add(y)
for j in range(1, 6):
    extra.add(2*lam / j)
ypts = sorted({y for y in extra | set(ypts) if Fr(1, 3) <= y <= 2*lam})
dint, _ = integrate_affine(dfun, [y for y in ypts if y <= Fr(1, 2)], 0, "d")
ok("int d over (1/3,1/2)", dint, Fr(9, 640))
Iout, bad = integrate_affine(Tout, ypts, 0, "Tout")
print(f"  outer: {len(ypts)-1} pieces, non-affine pieces: {bad}")
ok("(5.10) I_out", Iout, Fr(127751, 96000))

# ---------- A*, A_M, margins (5.19), (5.20), (7.2) ----------
Astar = Iout + inner - Fr(2689, 48000)
ok("(5.19) A*", Astar, Fr(9928298118277006344769, 7535670527041937280000))

def A_M(M):
    M = Fr(M)
    return Astar + 7*lam/M - (Fr(2923, 240) - Fr(1, 4))/M**2 + 32/M**3

U = Fr(-2733991, 2000000)
ok("A_200", A_M(200), Fr(127125602969131786927559, 94195881588024216000000))
ok("A_100000", A_M(100000), Fr(7756864096839411316755964319057, 5887242599251513500000000000000))
m200 = -1600*(A_M(200) + U) - Fr(139, 5)
m1e5 = -1600*(A_M(100000) + U) - Fr(7907, 100)
ok("margin (7.2) M=200", m200, Fr(3089837638249482469, 58872425992515135000))
ok("margin (7.2) M=100000", m1e5, Fr(29873543950273155160680943, 3679526624532195937500000000))
print(f"  margin M=200 as float: {float(m200):.6f} (relative to 139/5: {float(m200/Fr(139,5)):.4%})")
print(f"  A_100000 + U < -79/1600: {A_M(100000) + U < Fr(-79, 1600)}")
