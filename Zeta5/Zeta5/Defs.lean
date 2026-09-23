import Mathlib

/-!
# Definitions for "ζ(5) is irrational" (A. Fauzan, 17 Sep 2026)

Every object of the paper that later statements refer to is defined here, as concretely as
possible, so that each statement in the section files has a single unambiguous meaning.

Conventions.
* `K` is a natural number; the paper always has `40 ∣ K`, and `N = 3K/40`, `h = 37K/40`
  (`Nof`, `hof`) are only meaningful then.
* Rational functions in `t` are represented by a numerator polynomial and a finite set of
  simple poles. `muX S P` is `µ_X(P(t) / ∏_{j ∈ S} (t + j²))` and `tauX S P` is
  `τ_X(P(x) / ∏_{r ∈ S} (x - r))`. Both are defined by polynomial division and simple partial
  fractions, exactly as in the paper. Their values lie in `ℚ[X]`, where `X` is the
  indeterminate that is later specialised to `ζ(5)`.
* `vpGge p A b` means `v_p^G(A) ≥ b` for the Gauss valuation (min over nonzero coefficients),
  with the convention `v_p^G(0) = +∞`.

Paper ambiguities found while writing these definitions are marked `AMBIGUITY` below and
collected in `NOTES.md`.
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-! ## §2.1 Parameters (2.1) -/

/-- `N = 3K/40`. -/
def Nof (K : ℕ) : ℕ := 3 * K / 40

/-- `h = 37K/40`, the size of the Hankel matrix. -/
def hof (K : ℕ) : ℕ := 37 * K / 40

def α : ℚ := 3 / 40
def lam : ℚ := 37 / 40
def Hc : ℚ := 1 + 2 * α

/-- The real number `ζ(5)`. `riemannZeta_five_eq` in `Main.lean` shows `riemannZeta 5` is real. -/
def ζ5 : ℝ := (riemannZeta 5).re

/-- `H_j^{(5)} = ∑_{v=1}^j v⁻⁵`. -/
def H5 (j : ℕ) : ℚ := ∑ v ∈ Icc 1 j, 1 / (v : ℚ) ^ 5

/-- `D_m(t) = ∏_{j=1}^m (t + j²)`. -/
def D (m : ℕ) : ℚ[X] := ∏ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2))

/-! ## §2.1 The functional `µ_X` (2.2), (2.3) -/

/-- (2.2): `µ(tᵉ) = (-1)ᵉ B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`. Mathlib's `bernoulli` has
`B₁ = -1/2`, the paper's convention. -/
def muMono (e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) * ((2 * e + 3 : ℚ) * (2 * e + 4) * (2 * e + 5)) / 24

/-- `µ` on polynomials, by linearity. -/
def muPoly (P : ℚ[X]) : ℚ := P.sum fun e c => c * muMono e

/-- (2.3): `µ_X(1/(t + j²)) = j⁴ (X - H_j^{(5)}) - 1/4 + 1/(2j)`. -/
def muPole (j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ 4) * (X - C (H5 j)) - C (1 / 4) + C (1 / (2 * (j : ℚ)))

/-- `∏_{j ∈ S} (t + j²)`. -/
def sqPoleProd (S : Finset ℕ) : ℚ[X] := ∏ j ∈ S, (X + C ((j : ℚ) ^ 2))

/-- Residue of `P / ∏_{k ∈ S} (t + k²)` at `t = -j²`. -/
def sqResidue (S : Finset ℕ) (P : ℚ[X]) (j : ℕ) : ℚ :=
  P.eval (-(j : ℚ) ^ 2) / ∏ k ∈ S.erase j, ((k : ℚ) ^ 2 - (j : ℚ) ^ 2)

/-- `µ_X(P(t) / ∏_{j ∈ S} (t + j²))`, by polynomial division and simple partial fractions.
Meaningful when `0 ∉ S`. -/
def muX (S : Finset ℕ) (P : ℚ[X]) : ℚ[X] :=
  C (muPoly (P /ₘ sqPoleProd S)) + ∑ j ∈ S, C (sqResidue S P j) * muPole j

/-! ## §2.1 The matrix, determinant and normalisation (2.4), (2.5) -/

/-- (2.4): `G_K(X) = [µ_X(D_N(t)⁶ t^{i+j} / D_K(t))]_{0 ≤ i,j < h}`. -/
def G (K : ℕ) : Matrix (Fin (hof K)) (Fin (hof K)) ℚ[X] :=
  Matrix.of fun i j => muX (Icc 1 K) (D (Nof K) ^ 6 * X ^ ((i : ℕ) + j))

/-- `Δ_K(X) = det G_K(X)`. -/
def Delta (K : ℕ) : ℚ[X] := (G K).det

/-- (2.5): `S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)`. -/
def S (K : ℕ) : ℚ :=
  ((K.factorial : ℚ) ^ (2 * hof K) * 4 ^ (hof K - 1)) /
    (((Nof K).factorial : ℚ) ^ (12 * hof K) *
      ∏ i ∈ Icc 1 (hof K - 1), ((2 * i).factorial : ℚ) ^ 2)

/-- (2.5): `F_K = S_K Δ_K`. -/
def F (K : ℕ) : ℚ[X] := C (S K) * Delta K

/-! ## Gauss valuation -/

/-- `v_p^G(A) ≥ b`: every nonzero coefficient of `A` has `p`-adic valuation at least `b`. -/
def vpGge (p : ℕ) (A : ℚ[X]) (b : ℚ) : Prop :=
  ∀ i, A.coeff i ≠ 0 → b ≤ (padicValRat p (A.coeff i) : ℚ)

/-! ## §3 The functional `τ_X` -/

/-- `L(xᵏ) = B_k`, extended linearly. -/
def Lfun (P : ℚ[X]) : ℚ := P.sum fun k c => c * _root_.bernoulli k

/-- `τ(P) = L(P''') / 24` on polynomials. -/
def tau (P : ℚ[X]) : ℚ := Lfun (derivative^[3] P) / 24

/-- `d(r) = r` for `r ≥ 0` and `-r - 1` for `r < 0`. -/
def dIdx (r : ℤ) : ℕ := if 0 ≤ r then r.toNat else (-r - 1).toNat

/-- `τ_X(1/(x - r)) = H^{(5)}_{d(r)} - X`. -/
def tauPole (r : ℤ) : ℚ[X] := C (H5 (dIdx r)) - X

/-- `∏_{r ∈ S} (x - r)`. -/
def linPoleProd (S : Finset ℤ) : ℚ[X] := ∏ r ∈ S, (X - C (r : ℚ))

/-- Residue of `P / ∏_{s ∈ S} (x - s)` at `x = r`. -/
def linResidue (S : Finset ℤ) (P : ℚ[X]) (r : ℤ) : ℚ :=
  P.eval (r : ℚ) / ∏ s ∈ S.erase r, ((r : ℚ) - s)

/-- `τ_X(P(x) / ∏_{r ∈ S} (x - r))` by polynomial division and simple partial fractions. -/
def tauX (S : Finset ℤ) (P : ℚ[X]) : ℚ[X] :=
  C (tau (P /ₘ linPoleProd S)) + ∑ r ∈ S, C (linResidue S P r) * tauPole r

/-- The fourth Taylor coefficient `g⁽⁴⁾(0)/24` of `g = P/Q` at `0` (requires `Q(0) ≠ 0`). -/
def taylor4 (P Q : ℚ[X]) : ℚ :=
  PowerSeries.coeff 4 ((P : PowerSeries ℚ) * (Q : PowerSeries ℚ)⁻¹)

/-! ## §3.1–3.2 The `p`-adic extension

We only need finite sums of rational functions. Near (integer) poles take the value
`H^{(5)}_{d(r)} - Y`. Far poles `s` with `v_p(s) < 0` take the value (3.5) of the
expanded series. The paper's Tate-algebra extension `τ_Y^{ext}` agrees with this on such
functions (the uniqueness remark after (3.5)). -/

/-- `κ_d = d(d-1)(d-2) B_{d-3} / 24`, so that `τ(z^d) = κ_d`. This is `0` for `d < 3`. -/
def kappa (d : ℕ) : ℚ := (d : ℚ) * (d - 1) * (d - 2) * _root_.bernoulli (d - 3) / 24

/-- `τ` on polynomials over `ℚ_p`. -/
def tauP (p : ℕ) [Fact p.Prime] (f : ℚ_[p][X]) : ℚ_[p] := f.sum fun d c => c * (kappa d : ℚ_[p])

/-- (3.5): `τ(1/(z - s)) = -(1/4) ∑_{k ≥ 0} C(k+3,3) B_k s^{-k-4}` for `v_p(s) < 0`. -/
def tauAnPole (p : ℕ) [Fact p.Prime] (s : ℚ) : ℚ_[p] :=
  -(1 / 4) * ∑' k : ℕ, (((k + 3).choose 3 : ℚ) * _root_.bernoulli k : ℚ_[p]) * (s : ℚ_[p]) ^ (-(k + 4 : ℤ))

/-- Value of `τ_Y^{ext}` on the simple pole `1/(z - s)`. -/
def tauPoleP (p : ℕ) [Fact p.Prime] (Y : ℚ_[p][X]) (s : ℚ) : ℚ_[p][X] :=
  if s.den = 1 then C ((H5 (dIdx s.num) : ℚ) : ℚ_[p]) - Y else C (tauAnPole p s)

/-- `τ_Y^{ext}(U(z) / ∏_{s ∈ S} (z - s))` for distinct rational poles `S`. -/
def tauExtP (p : ℕ) [Fact p.Prime] (Y : ℚ_[p][X]) (U : ℚ_[p][X]) (S : Finset ℚ) : ℚ_[p][X] :=
  C (tauP p (U /ₘ ∏ s ∈ S, (X - C (s : ℚ_[p])))) +
    ∑ s ∈ S, C (U.eval (s : ℚ_[p]) / ∏ s' ∈ S.erase s, ((s : ℚ_[p]) - s')) * tauPoleP p Y s

/-- (3.6): `C_p = ∑_{a=1}^{p-1} τ^{an}(1/(x + a/p))`. -/
def Cp (p : ℕ) [Fact p.Prime] : ℚ_[p] := ∑ a ∈ Ico 1 p, tauAnPole p (-(a : ℚ) / p)

/-- (3.6): `Y = p⁵ X + C_p`. -/
def Yp (p : ℕ) [Fact p.Prime] : ℚ_[p][X] := C ((p : ℚ_[p]) ^ 5) * X + C (Cp p)

/-- `g(a + p x)` written as `U(x) / ∏ (x - s)`: the numerator `p^{-|S|} P(a + p x)`. -/
def distribNum (p : ℕ) [Fact p.Prime] (S : Finset ℤ) (P : ℚ[X]) (a : ℕ) : ℚ_[p][X] :=
  C ((p : ℚ_[p]) ^ (-(S.card : ℤ))) * (P.map (algebraMap ℚ ℚ_[p])).comp (C (a : ℚ_[p]) + C (p : ℚ_[p]) * X)

/-- The poles `(r - a)/p` of `g(a + p x)`. -/
def distribPoles (p : ℕ) (S : Finset ℤ) (a : ℕ) : Finset ℚ :=
  S.image fun r : ℤ => ((r : ℚ) - a) / p

/-! ## §3.3 Small primes -/

/-- `q_0 = 1`, `q_i(t) = (-1)ⁱ 2t D_{i-1}(t) / (2i)!`. -/
def qBasis (i : ℕ) : ℚ[X] :=
  if i = 0 then 1 else C ((-1) ^ i * 2 / ((2 * i).factorial : ℚ)) * X * D (i - 1)

/-- `f_i(t) = (D_N(t)/(N!)²)³ q_i(t)`. -/
def fBasis (K i : ℕ) : ℚ[X] := (C (1 / ((Nof K).factorial : ℚ) ^ 2) * D (Nof K)) ^ 3 * qBasis i

/-! ## §4.1 The inner range -/

/-- `ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (mod p)}`. -/
def ell (p A a : ℕ) : ℕ := ((Icc 1 A).filter fun j => j % p = a % p ∨ (j + a) % p = 0).card

/-- `m = (p-1)/2`. -/
def mHalf (p : ℕ) : ℕ := (p - 1) / 2

/-- `L_0 = 4M + 10`. -/
def L0 (M : ℕ) : ℕ := 4 * M + 10

/-- Right-hand side of (4.4): `h - L_0 + 3(N - m_N)`. -/
def rhs44 (K M p : ℕ) : ℤ := (hof K : ℤ) - L0 M + 3 * ((Nof K : ℤ) - (Nof K / p : ℕ))

/-- (4.4): `T`. -/
def Tin (K M p : ℕ) : ℤ := rhs44 K M p / (mHalf p : ℤ)

/-- (4.4): `E`, with `0 ≤ E < m`. -/
def Ein (K M p : ℕ) : ℤ := rhs44 K M p % (mHalf p : ℤ)

/-- `b_a = 3 ℓ_N(a)`. -/
def bIn (K p a : ℕ) : ℤ := 3 * ell p (Nof K) a

/-- The canonical position of class `a` in the ordering by decreasing `ℓ_K`: the number of
classes before it, ties broken by increasing `a`. -/
def defaultPos (K p a : ℕ) : ℕ :=
  ((Icc 1 (mHalf p)).filter fun c =>
      ell p K a < ell p K c ∨ (ell p K c = ell p K a ∧ c < a)).card

/-- `ε_a = 1` for the first `E` classes in the ordering `pos` (decreasing `ℓ_K`). The paper
lets ties be ordered arbitrarily; `gammaIn_tie_independent` states that this does not matter. -/
def epsIn (K M p : ℕ) (pos : ℕ → ℕ) (a : ℕ) : ℤ :=
  if (((Icc 1 (mHalf p)).filter fun c => pos c < pos a).card : ℤ) < Ein K M p then 1 else 0

/-- `L_a = T - b_a + ε_a` for `a ≥ 1`, and `L_0 = 4M + 10`. -/
def Lin (K M p a : ℕ) (pos : ℕ → ℕ := defaultPos K p) : ℤ :=
  if a = 0 then L0 M else Tin K M p - bIn K p a + epsIn K M p pos a

/-- `Z_a = T + ε_a`. -/
def Zin (K M p a : ℕ) (pos : ℕ → ℕ := defaultPos K p) : ℤ := Tin K M p + epsIn K M p pos a

/-- (4.6), (4.7): the row weights `w_{a,i}`. -/
def wIn (K M p a i : ℕ) (pos : ℕ → ℕ := defaultPos K p) : ℚ :=
  if a = 0 then
    (Icc 1 (mHalf p)).fold min
      (2 * i + 6 * (Nof K / p : ℕ) - (K / p : ℕ) + 1 / 2)
      (fun c => (Zin K M p c pos : ℚ) - ((ell p K c : ℚ) + 4) / 2)
  else (i : ℚ) + bIn K p a - ((ell p K a : ℚ) + 4) / 2

/-- (4.8): `γ_p^in = 2 ∑_{a=0}^m ∑_{i<L_a} w_{a,i}`. -/
def gammaIn (K M p : ℕ) (pos : ℕ → ℕ := defaultPos K p) : ℚ :=
  2 * ∑ a ∈ range (mHalf p + 1), ∑ i ∈ range (Lin K M p a pos).toNat, wIn K M p a i pos

/-- Index set of the inner basis: pairs `(a, i)` with `0 ≤ a ≤ m`, `i < L_a`. -/
abbrev InnerIdx (K M p : ℕ) := Σ a : Fin (mHalf p + 1), Fin (Lin K M p a).toNat

/-- (4.5): `E_{a,i}(t) = ∏_{0 ≤ c ≤ m, c ≠ a} (t + c²)^{L_c} (t + a²)^i`. -/
def innerBasis (K M p : ℕ) (x : InnerIdx K M p) : ℚ[X] :=
  (∏ c ∈ (range (mHalf p + 1)).erase x.1, (X + C ((c : ℚ) ^ 2)) ^ (Lin K M p c).toNat) *
    (X + C ((x.1 : ℕ) ^ 2 : ℚ)) ^ (x.2 : ℕ)

/-- The Gram matrix of `µ_X(D_N⁶ · / D_K)` in the inner basis. -/
def innerGram (K M p : ℕ) : Matrix (InnerIdx K M p) (InnerIdx K M p) ℚ[X] :=
  Matrix.of fun x y => muX (Icc 1 K) (D (Nof K) ^ 6 * innerBasis K M p x * innerBasis K M p y)

/-! ## §4.2 The outer range -/

/-- `r_p = max(0, K + 4N - 2p + 2)` from (4.10). -/
def rOut (K p : ℕ) : ℕ := K + 4 * Nof K + 2 - 2 * p

/-- (4.14): `γ_p^out`, with `v = K - p⌊K/p⌋`, `u = max(0, N + v - p + 1)`,
`t_p = min(N, v) + u`. -/
def gammaOut (K p : ℕ) : ℤ :=
  let v : ℕ := K % p
  let u : ℕ := Nof K + v + 1 - p
  let tp : ℕ := min (Nof K) v + u
  if K < 2 * p then
    -7 * ((K : ℤ) - p) + 6 * tp - 1 - min (rOut K p : ℤ) ((p : ℤ) - 1 - Nof K + u)
  else -7 * ((K : ℤ) - p) + 3 + 12 * Nof K + 5 * tp - min (rOut K p : ℤ) ((p : ℤ) + u)

/-- (4.9): the hypotheses of the outer-range estimate. -/
def OuterHyp (K p : ℕ) : Prop :=
  7 ≤ p ∧ p ≤ K ∧ K < 3 * p ∧ 2 * K < p ^ 2 ∧ 2 * Nof K < p ∧ 5 * Nof K ≤ 2 * p - 2

/-- The poles of `D_tail` in the class `±a (mod p)` (`a = 0` gives the multiples of `p`). -/
def outerClassPoles (K p a : ℕ) : Finset ℕ :=
  (Icc (Nof K + 1) K).filter fun j => j % p = a % p ∨ (j + a) % p = 0

/-- Number of outer-basis rows in class `a`: `ℓ - δ` for `a ≥ 1`, the number of pole
multiples of `p` for `a = 0`. -/
def outerCount (K p a : ℕ) : ℕ := (outerClassPoles K p a).card

abbrev OuterIdx (K p : ℕ) := Σ a : Fin (mHalf p + 1), Fin (outerCount K p a)

/-- (4.11): rows `P_a q_{a,i}` with `P_a = D_tail / Q_a`.
For `a ≥ 1`, `q_{a,i} = (t+a²)ⁱ` for `i < ℓ - 2` and `E_a (t+a²)^{i-(ℓ-2)}` after that, where
`E_a` is the product of the class factors with `j > p`.
AMBIGUITY: the paper describes the zero class only as "the rows `1, t + p²`". We read this as
`P_0 · (t + p²)ⁱ` for `i < #(zero-class poles)`. -/
def outerBasis (K p : ℕ) (x : OuterIdx K p) : ℚ[X] :=
  let a : ℕ := x.1
  let i : ℕ := x.2
  let Pa := sqPoleProd (Icc (Nof K + 1) K \ outerClassPoles K p a)
  if a = 0 then Pa * (X + C ((p : ℚ) ^ 2)) ^ i
  else
    let l := ell p K a
    if i < l - 2 then Pa * (X + C ((a : ℚ) ^ 2)) ^ i
    else Pa * sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) *
      (X + C ((a : ℚ) ^ 2)) ^ (i - (l - 2))

/-- (4.12) and the zero-class weights. -/
def wOut (K p : ℕ) (x : OuterIdx K p) : ℚ :=
  let a : ℕ := x.1
  let i : ℕ := x.2
  if a = 0 then
    (if outerCount K p 0 = 1 then -1 / 2 else if i = 0 then -2 else 0)
  else
    let l := ell p K a
    let δ : ℚ := if a ≤ Nof K then 1 else 0
    if i < l - 2 then min 0 ((i : ℚ) + 3 * δ - ((l : ℚ) + 4) / 2) else 0

/-- The integer `c_e ≡ p µ(tᵉ) (mod p)`, taken in `[0, p)`, with `c_e = 0` for `e < 2p - 3`. -/
def cCorr (p e : ℕ) : ℚ :=
  if e < 2 * p - 3 then 0
  else (let r : ℚ := p * muMono e
    (((r.num : ZMod p) * ((r.den : ℕ) : ZMod p)⁻¹).val : ℚ))

/-- `µ_X` with the polynomial moments replaced by `µ⁰(tᵉ) = µ(tᵉ) - c_e/p`. -/
def muXmod (p : ℕ) (S : Finset ℕ) (P : ℚ[X]) : ℚ[X] :=
  C ((P /ₘ sqPoleProd S).sum fun e c => c * (muMono e - cCorr p e / p)) +
    ∑ j ∈ S, C (sqResidue S P j) * muPole j

/-- The matrix `A` of (4.10). -/
def Aout (K p : ℕ) : Matrix (Fin (hof K)) (Fin (hof K)) ℚ[X] :=
  Matrix.of fun i j => muXmod p (Icc 1 K) (D (Nof K) ^ 6 * X ^ ((i : ℕ) + j))

/-- `A` in the outer basis. -/
def outerGram (K p : ℕ) : Matrix (OuterIdx K p) (OuterIdx K p) ℚ[X] :=
  Matrix.of fun x y => muXmod p (Icc 1 K) (D (Nof K) ^ 6 * outerBasis K p x * outerBasis K p y)

/-! ## §5 Normalisation (5.1), (5.2), (2.6) -/

/-- `v_p(S_K)`. -/
def vpS (K p : ℕ) : ℤ := padicValRat p (S K)

/-- (5.1): `L_p(K, M)`. We use `⌊γ_p^in⌋`, which equals `γ_p^in` by `gammaIn_isInt`; the floor
keeps the definition sound even without that lemma. For `p > K`, `γ_p^out = 0`. -/
def Lp (K M p : ℕ) : ℤ :=
  if p * M ≤ K then -6 * (hof K : ℤ) * Nat.log p (5 * K) - hof K * padicValNat p 24
  else if 3 * p ≤ K then vpS K p + ⌊gammaIn K M p⌋
  else if p ≤ K then vpS K p + gammaOut K p
  else vpS K p

/-- (5.2): `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}`. -/
def mKM (K M : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * hof K + 1)).filter Nat.Prime, (p : ℚ) ^ (-Lp K M p)

/-- (2.6): `Q_{K,M} = m_{K,M} F_K`. -/
def Q (K M : ℕ) : ℚ[X] := C (mKM K M) * F K

/-! ## §5.1–5.3 Limiting functions (real-valued) -/

namespace Lim

def α : ℝ := 3 / 40
def lam : ℝ := 37 / 40
def Hc : ℝ := 23 / 20

def pos (v : ℝ) : ℝ := max v 0

/-- `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`. -/
def ell (x z : ℝ) : ℝ := ⌊x - z⌋ + ⌊x + z⌋ + 1

/-- (5.4): `Γ(x)`. -/
def Gam (x : ℝ) : ℝ :=
  let T : ℝ := ⌊2 * Hc * x⌋
  let s := Hc * x - T / 2
  let q : ℝ := ⌊2 * x⌋
  let nplus := (2 * x - q) / 2
  (∫ z in (0 : ℝ)..(1 / 2), (T - 3 * ell (α * x) z) * (T + 3 * ell (α * x) z - ell x z - 5))
    + s * (2 * T - q - 5) + pos (s - nplus)

/-- `J(u) = m u - m(m+1)/4`, `m = ⌊2u⌋`. -/
def J (u : ℝ) : ℝ := ⌊2 * u⌋ * u - (⌊2 * u⌋ : ℝ) * (⌊2 * u⌋ + 1) / 4

/-- (5.5): `N(x)`. -/
def Nfun (x : ℝ) : ℝ := 2 * lam * x * ⌊x⌋ - 12 * lam * x * ⌊α * x⌋ - 2 * J (lam * x)

/-- (5.6): `R(x) = -Γ(x) - N(x)`. -/
def R (x : ℝ) : ℝ := -Gam x - Nfun x

/-- (5.8): `R₀(y)`. -/
def R0 (y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y < 1 / 2 then
    8 - 9 * y - 8 * α - 5 * min α (1 - 2 * y) - 5 * pos (1 + α - 3 * y)
  else if 1 / 2 < y ∧ y < 1 then
    7 * (1 - y) - 6 * min α (1 - y) - 6 * pos (1 + α - 2 * y) + pos (1 + 4 * α - 2 * y)
  else 0

/-- (5.9): `d(y)`. -/
def dfun (y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y < 1 / 2 then pos ((1 + 4 * α - 3 * y) - pos (1 + α - 3 * y)) else 0

/-- Integrand of (5.10). -/
def outerIntegrand (y : ℝ) : ℝ :=
  R0 y - dfun y - 2 * lam * ⌊1 / y⌋ + ∑ j ∈ Icc (1 : ℕ) 5, pos (2 * lam - (j : ℝ) * y)

/-- (5.12)–(5.13): fractional parts and the pieces `P`, `C` of the tail. -/
def G0 (v : ℝ) : ℝ := v * (1 - v) * (2 * v - 1) / 6
def Pper (x : ℝ) : ℝ := 74 * Int.fract (α * x) * (1 - Int.fract (α * x)) -
  lam * Int.fract x * (1 - Int.fract x)
def Cper (x : ℝ) : ℝ := 74 / α * G0 (Int.fract (α * x)) - lam * G0 (Int.fract x)

end Lim

/-- (5.10): `I_out = 127751/96000`. -/
def Iout : ℚ := 127751 / 96000

/-- (5.19). -/
def Astar : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- (5.20). -/
def AM (M : ℕ) : ℚ := Astar + 7 * lam / M - (2923 / 240 - 1 / 4) / (M : ℚ) ^ 2 + 32 / (M : ℚ) ^ 3

/-- (6.4). -/
def U : ℚ := -2733991 / 2000000

/-! ## §6 The real determinant -/

/-- (2.10): `w(y) = (2π)⁴ y⁵ / 12 · ∑_{ℓ≥1} ℓ⁴ e^{-2πℓy}`. -/
def weight (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * y ^ 5 / 12 * ∑' l : ℕ, ((l + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-2 * Real.pi * (l + 1) * y)

/-- (6.1): the external field `V`. -/
def V (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt t + (∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2)) -
    6 * ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2)

open MeasureTheory

/-- The arcsine probability measure on `(a, b)`. -/
def arcsine (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo a b)).withDensity fun t =>
    ENNReal.ofReal (1 / (Real.pi * Real.sqrt ((t - a) * (b - t))))

/-- Table 1, scaled by `10¹²`: `(a_j, b_j, c_j)` for `j = 1, …, 16`. -/
def table1 : List (ℕ × ℕ × ℕ) :=
  [(3906748086, 8992695531, 10515596180), (2312248264, 15340997855, 29471737793),
   (1402286665, 25730180724, 42934365099), (881725356, 41909578246, 58204231966),
   (578197906, 65851089563, 69037621310), (396324613, 99481037884, 78873099189),
   (283911191, 144325727458, 84856120711), (212206188, 201105762729, 88396082127),
   (165097686, 269345996903, 88303382125), (133347132, 347089554156, 85472321255),
   (111522114, 430806704415, 78899184238), (96349355, 515561896511, 70353471918),
   (85815639, 595448778546, 58838976615), (78667711, 664241383483, 44421321106),
   (74129565, 716160577112, 30462865791), (71741310, 746637295669, 5959622577)]

/-- The comparison measure `ρ = ∑ c_j ω_{[a_j, b_j]}` of Lemma 6.1. -/
def rho : Measure ℝ :=
  (table1.map fun e =>
    ENNReal.ofReal ((e.2.2 : ℝ) / 10 ^ 12) • arcsine ((e.1 : ℝ) / 10 ^ 12) ((e.2.1 : ℝ) / 10 ^ 12)).sum

/-- `U^μ(t) = ∫ log|t - u| dμ(u)`. -/
def logPot (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ u, Real.log |t - u| ∂μ

/-- `I(μ) = ∬ log|t - u| dμ(t) dμ(u)`. -/
def logEnergy (μ : Measure ℝ) : ℝ := ∫ t, logPot μ t ∂μ

/-- `M₀ = -1329/200`. -/
def M0 : ℚ := -1329 / 200

/-- (6.3): `C* = -2λ + 12αλ(1 - log α) + 3λ² - 2λ² log(2λ)`. -/
def Cstar : ℝ :=
  -2 * Lim.lam + 12 * Lim.α * Lim.lam * (1 - Real.log Lim.α) + 3 * Lim.lam ^ 2 -
    2 * Lim.lam ^ 2 * Real.log (2 * Lim.lam)

end Zeta5
