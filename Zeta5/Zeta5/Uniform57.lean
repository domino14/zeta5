import Zeta5.Section5
import Zeta5.InnerFinal
import Zeta5.Integrals5Base

/-!
# §5: the inner-range uniformity (Lemma 5.7)

`uniformity_5_7'`: for fixed `M ≥ 40`, `γ_p^in = pΓ(K/p) + O_M(1)` and
`v_p(S_K) = pN(K/p) + O_M(1)` uniformly over `(K, p)` satisfying (4.1).
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

namespace U57

/-! ## Floors -/

theorem floor_nat_div (n d : ℕ) : ⌊(n : ℝ) / d⌋ = ((n / d : ℕ) : ℤ) := by
  have : (n : ℝ) / d = (((n : ℚ) / d : ℚ) : ℝ) := by push_cast; rfl
  rw [this, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  exact (Int.natCast_div n d).symm

/-! ## `v_p(S_K)` in the inner range -/

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValNat_factorial_small (n : ℕ) (hn : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  have hlog : Nat.log p n < 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact Nat.log_lt_of_lt_pow hn0.ne' hn
  rw [padicValNat_factorial hlog]
  simp

theorem vpS_inner {K M : ℕ} (h : InnerHyp K M p) :
    vpS K p = 2 * hof K * (K / p : ℕ) - 12 * hof K * (Nof K / p : ℕ)
      - 2 * ∑ i ∈ Icc 1 (hof K - 1), (2 * i / p : ℕ) := by
  have hb := innerHyp_bounds h
  obtain ⟨hM, hK40, hK0, hKM, hpM, h3p⟩ := h
  have hh : 1 ≤ hof K := by unfold hof; omega
  set A : ℕ := K.factorial ^ (2 * hof K) * 4 ^ (hof K - 1) with hA
  set Bd : ℕ := (Nof K).factorial ^ (12 * hof K) *
    ∏ i ∈ Icc 1 (hof K - 1), (2 * i).factorial ^ 2 with hBd
  have hS : S K = (A : ℚ) / Bd := by unfold S; simp only [hA, hBd]; push_cast; ring
  have hA0 : A ≠ 0 := by positivity
  have hB0 : Bd ≠ 0 := by positivity
  have h4 : padicValNat p 4 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have : p ∣ 2 := hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hd)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have hvA : padicValNat p A = 2 * hof K * (K / p) := by
    rw [hA, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ _,
      padicValNat.pow _ _, padicValNat_factorial_small K (by nlinarith), h4]
    ring
  have hvB : padicValNat p Bd = 12 * hof K * (Nof K / p) +
      2 * ∑ i ∈ Icc 1 (hof K - 1), 2 * i / p := by
    rw [hBd, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ _,
      padicValNat_factorial_small (Nof K) (by unfold Nof; have := hb.2; omega)]
    congr 1
    have : ∀ s : Finset ℕ, (∀ i ∈ s, 2 * i < p ^ 2) →
        padicValNat p (∏ i ∈ s, (2 * i).factorial ^ 2) = 2 * ∑ i ∈ s, 2 * i / p := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | insert b s hb ih =>
        rw [prod_insert hb, sum_insert hb, padicValNat.mul (by positivity) (by positivity),
          padicValNat.pow _ _, padicValNat_factorial_small _ (hs b (mem_insert_self b s)),
          ih fun i hi => hs i (mem_insert_of_mem hi)]
        ring
    exact this _ fun i hi => by rw [mem_Icc] at hi; unfold hof at hi; omega
  show padicValRat p (S K) = _
  rw [hS, padicValRat.div (by exact_mod_cast hA0) (by exact_mod_cast hB0), padicValRat.of_nat,
    padicValRat.of_nat, hvA, hvB]
  push_cast
  ring

/-- `G₄(n) = 4tn - pt(t+1)`, `t = ⌊2n/p⌋`; `G₄(n)/4 = pJ(n/p)`. -/
def G4 (p n : ℕ) : ℤ := 4 * ((2 * n / p : ℕ) : ℤ) * n - p * ((2 * n / p : ℕ) : ℤ) * ((2 * n / p : ℕ) + 1)

theorem G4_step (hp2 : 2 ≤ p) (n : ℕ) :
    0 ≤ G4 p (n + 1) - G4 p n - 4 * ((2 * n / p : ℕ) : ℤ) ∧
      G4 p (n + 1) - G4 p n - 4 * ((2 * n / p : ℕ) : ℤ) ≤
        4 * (((2 * (n + 1) / p : ℕ) : ℤ) - ((2 * n / p : ℕ) : ℤ)) := by
  have hp0 : 0 < p := by omega
  set t := 2 * n / p with ht
  set t' := 2 * (n + 1) / p with ht'
  have h1 : t ≤ t' := Nat.div_le_div_right (by omega)
  have h2 : t' ≤ t + 1 := by
    calc t' ≤ (2 * n + p) / p := Nat.div_le_div_right (by omega)
      _ = t + 1 := by rw [Nat.add_div_right _ hp0]
  unfold G4
  rw [← ht, ← ht']
  rcases (show t' = t ∨ t' = t + 1 by omega) with e | e
  · rw [e]; push_cast; constructor <;> nlinarith
  · rw [e]
    have a1 : (t + 1) * p ≤ 2 * (n + 1) := by rw [← e]; exact Nat.div_mul_le_self _ _
    have a2 : 2 * n < (t + 1) * p := by
      have := Nat.lt_mul_div_succ (2 * n) hp0; rw [← ht] at this; linarith
    have b1 : ((t : ℤ) + 1) * p ≤ 2 * ((n : ℤ) + 1) := by exact_mod_cast a1
    have b2 : 2 * (n : ℤ) < ((t : ℤ) + 1) * p := by exact_mod_cast a2
    push_cast
    constructor <;> nlinarith

theorem G4_tele (hp2 : 2 ≤ p) (n : ℕ) :
    0 ≤ G4 p n - 4 * ∑ i ∈ range n, ((2 * i / p : ℕ) : ℤ) ∧
      G4 p n - 4 * ∑ i ∈ range n, ((2 * i / p : ℕ) : ℤ) ≤ 4 * ((2 * n / p : ℕ) : ℤ) := by
  induction n with
  | zero => simp [G4]
  | succ n ih =>
    rw [sum_range_succ]
    have := G4_step (p := p) hp2 n
    constructor <;> linarith [ih.1, ih.2, this.1, this.2]

theorem sum_Icc_eq_range (f : ℕ → ℤ) (hf : f 0 = 0) (h : ℕ) (hh : 1 ≤ h) :
    ∑ i ∈ Icc 1 (h - 1), f i = ∑ i ∈ range h, f i := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rw [sum_range_succ', hf, add_zero, show k + 1 - 1 = k by omega]
  clear hh
  induction k with
  | zero => simp
  | succ k ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem vpS_sub {K M : ℕ} (h : InnerHyp K M p) :
    (vpS K p : ℝ) - p * Lim.Nfun ((K : ℝ) / p) =
      ((G4 p (hof K) - 4 * ∑ i ∈ range (hof K), ((2 * i / p : ℕ) : ℤ) : ℤ) : ℝ) / 2 := by
  have hv := vpS_inner h
  have hb := innerHyp_bounds h
  obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  rw [hh, hN] at hv
  have hs : ((∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p : ℕ) : ℤ) =
      ∑ i ∈ range (37 * n), ((2 * i / p : ℕ) : ℤ) := by
    push_cast
    exact sum_Icc_eq_range (fun i => ((2 * i / p : ℕ) : ℤ)) (by simp) _ (by omega)
  rw [hh, hv, hs]
  have e1 : Lim.lam * ((40 * n : ℕ) : ℝ) / p = ((37 * n : ℕ) : ℝ) / p := by
    unfold Lim.lam; push_cast; ring
  have e2 : Lim.α * (((40 * n : ℕ) : ℝ) / p) = ((3 * n : ℕ) : ℝ) / p := by
    unfold Lim.α; push_cast; ring
  have e3 : 2 * (((37 * n : ℕ) : ℝ) / p) = ((2 * (37 * n) : ℕ) : ℝ) / p := by push_cast; ring
  unfold Lim.Nfun Lim.J
  rw [show Lim.lam * (((40 * n : ℕ) : ℝ) / p) = Lim.lam * ((40 * n : ℕ) : ℝ) / p by ring, e1, e2,
    e3, floor_nat_div, floor_nat_div, floor_nat_div]
  unfold G4
  push_cast
  field_simp
  unfold Lim.lam
  ring

theorem vpS_bound {K M : ℕ} (h : InnerHyp K M p) :
    |(vpS K p : ℝ) - p * Lim.Nfun ((K : ℝ) / p)| ≤ 4 * M := by
  rw [vpS_sub h]
  have hb := innerHyp_bounds h
  have hp2 := hp.out.two_le
  have ht := G4_tele (p := p) hp2 (hof K)
  obtain ⟨hM, hK40, hK0, hKM, hpM, h3p⟩ := h
  have hq : 2 * hof K / p ≤ 2 * M := by
    apply Nat.div_le_of_le_mul
    have : p * (2 * M) = 2 * (p * M) := by ring
    unfold hof; omega
  have hq' : ((2 * hof K / p : ℕ) : ℤ) ≤ 2 * M := by exact_mod_cast hq
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ ((G4 p (hof K) - 4 * ∑ i ∈ range (hof K), ((2 * i / p : ℕ) : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast ht.1
    have : (0:ℝ) ≤ M := by positivity
    linarith
  · have : ((G4 p (hof K) - 4 * ∑ i ∈ range (hof K), ((2 * i / p : ℕ) : ℤ) : ℤ) : ℝ) ≤ 8 * M := by
      have h8 : G4 p (hof K) - 4 * ∑ i ∈ range (hof K), ((2 * i / p : ℕ) : ℤ) ≤ 8 * (M : ℤ) := by
        linarith [ht.2]
      have := (Int.cast_le (R := ℝ)).2 h8
      push_cast at this ⊢; linarith
    linarith

/-! ## The Riemann-sum identity for the `z`-integral -/

theorem floor_between {p : ℕ} (hp : 0 < p) (j : ℤ) {y : ℝ}
    (h1 : (j : ℝ) / p < y) (h2 : y < ((j : ℝ) + 1) / p) : ⌊y⌋ = j / (p : ℤ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  rw [Int.floor_eq_iff]
  have e1 : j / (p : ℤ) * p ≤ j := Int.ediv_mul_le j hpz.ne'
  have e2 : j < (j / (p : ℤ) + 1) * p := Int.lt_ediv_add_one_mul_self j hpz
  have e1' : ((j / (p : ℤ) : ℤ) : ℝ) * p ≤ j := by exact_mod_cast e1
  have e2' : (j : ℝ) + 1 ≤ (((j / (p : ℤ) : ℤ) : ℝ) + 1) * p := by exact_mod_cast e2
  rw [div_lt_iff₀ hp'] at h1
  rw [lt_div_iff₀ hp'] at h2
  constructor
  · by_contra hc; push Not at hc; nlinarith
  · by_contra hc; push Not at hc; nlinarith

/-- `ℓ` on the `a`-th grid cell. -/
def ellZ (p A a : ℕ) : ℤ := ((A : ℤ) - a - 1) / p + ((A : ℤ) + a) / p + 1

def gg (T v l : ℤ) : ℤ := (T - 3 * v) * (T + 3 * v - l - 5)

theorem ell_on_cell {p : ℕ} (hp : 0 < p) (A a : ℕ) {z : ℝ}
    (h1 : (a : ℝ) / p < z) (h2 : z < ((a : ℝ) + 1) / p) :
    Lim.ell ((A : ℝ) / p) z = ellZ p A a := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold Lim.ell ellZ
  have h1' : (a : ℝ) < z * p := by rwa [div_lt_iff₀ hp'] at h1
  have h2' : z * p < a + 1 := by rwa [lt_div_iff₀ hp'] at h2
  rw [floor_between hp ((A : ℤ) - a - 1), floor_between hp ((A : ℤ) + a)]
  · push_cast; ring
  all_goals
    push_cast
    first
    | (rw [div_lt_iff₀ hp', add_mul, div_mul_cancel₀ _ hp'.ne']; linarith)
    | (rw [div_lt_iff₀ hp', sub_mul, div_mul_cancel₀ _ hp'.ne']; linarith)
    | (rw [lt_div_iff₀ hp', add_mul, div_mul_cancel₀ _ hp'.ne']; linarith)
    | (rw [lt_div_iff₀ hp', sub_mul, div_mul_cancel₀ _ hp'.ne']; linarith)

def phiZ (p N K : ℕ) (T : ℤ) (z : ℝ) : ℝ :=
  ((T : ℝ) - 3 * Lim.ell ((N : ℝ) / p) z) * (T + 3 * Lim.ell ((N : ℝ) / p) z - Lim.ell ((K : ℝ) / p) z - 5)

theorem phi_on_cell {p : ℕ} (hp : 0 < p) (N K a : ℕ) (T : ℤ) {z : ℝ}
    (h1 : (a : ℝ) / p < z) (h2 : z < ((a : ℝ) + 1) / p) :
    phiZ p N K T z = gg T (ellZ p N a) (ellZ p K a) := by
  unfold phiZ gg; rw [ell_on_cell hp N a h1 h2, ell_on_cell hp K a h1 h2]; push_cast; ring

theorem integral_cell {p : ℕ} (hp : 0 < p) (N K a : ℕ) (T : ℤ) (c : ℝ) (hc0 : (a : ℝ) / p ≤ c)
    (hc1 : c ≤ ((a : ℝ) + 1) / p) :
    ∫ z in (a : ℝ) / p..c, phiZ p N K T z = (c - a / p) * gg T (ellZ p N a) (ellZ p K a) ∧
      IntervalIntegrable (phiZ p N K T) MeasureTheory.volume ((a : ℝ) / p) c := by
  have hcell : ∀ z ∈ Set.Ioo ((a : ℝ) / p) c, phiZ p N K T z =
      (gg T (ellZ p N a) (ellZ p K a) : ℝ) + 0 * z + 0 * z ^ 2 := fun z hz => by
    rw [phi_on_cell hp N K a T hz.1 (lt_of_lt_of_le hz.2 hc1)]; ring
  refine ⟨?_, I5.piece_quad_int hc0 _ _ _ hcell⟩
  rw [I5.piece_quad hc0 _ _ _ hcell]; ring

theorem integral_sum (p N K m : ℕ) (hp : p = 2 * m + 1) (T : ℤ) :
    (p : ℝ) * ∫ z in (0 : ℝ)..(1 / 2), phiZ p N K T z =
      ∑ a ∈ range m, (gg T (ellZ p N a) (ellZ p K a) : ℝ) + (gg T (ellZ p N m) (ellZ p K m) : ℝ) / 2 := by
  have hp0 : 0 < p := by omega
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpr : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hp
  have hint : ∀ k < m, IntervalIntegrable (phiZ p N K T) MeasureTheory.volume
      ((k : ℕ) / (p : ℝ)) (((k + 1 : ℕ) : ℝ) / p) := fun k _ => by
    have := (integral_cell hp0 N K k T (((k + 1 : ℕ) : ℝ) / p) (by
      push_cast; gcongr; linarith) (by push_cast; rfl)).2
    exact this
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / p) hint
  simp only [Nat.cast_zero, zero_div] at hsum
  have hlast := integral_cell hp0 N K m T (1 / 2) (by rw [div_le_iff₀ hp']; linarith)
    (by rw [le_div_iff₀ hp']; linarith)
  have hmid : IntervalIntegrable (phiZ p N K T) MeasureTheory.volume 0 ((m : ℝ) / p) := by
    have := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k : ℝ) / p) hint
    simpa using this
  rw [← intervalIntegral.integral_add_adjacent_intervals hmid hlast.2, ← hsum, hlast.1, mul_add,
    Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    rw [(integral_cell hp0 N K k T (((k + 1 : ℕ) : ℝ) / p) (by
      push_cast; gcongr; linarith) (by push_cast; rfl)).1]
    push_cast; field_simp; ring
  · rw [hpr]; field_simp; ring

/-! ## Exact class counts -/

theorem count_mod_eq (A p r : ℕ) (hp : 0 < p) (hr1 : 1 ≤ r) (hr : r < p) :
    ((Icc 1 A).filter fun j => j % p = r).card = (A + p - r) / p := by
  apply le_antisymm
  · have : ((Icc 1 A).filter fun j => j % p = r).card ≤ (range ((A + p - r) / p)).card := by
      refine card_le_card_of_injOn (fun j => j / p) ?_ ?_
      · intro j hj
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj
        simp only [coe_range, Set.mem_Iio]
        apply Nat.lt_of_succ_le
        rw [Nat.le_div_iff_mul_le hp]
        have e := Nat.div_add_mod j p
        rw [hj.2] at e
        apply Nat.le_sub_of_add_le
        nlinarith [e, hj.1.2]
      · intro j1 hj1 j2 hj2 heq
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj1 hj2
        have e1 := Nat.div_add_mod j1 p
        have e2 := Nat.div_add_mod j2 p
        simp only at heq
        rw [heq, hj1.2] at e1
        rw [hj2.2] at e2
        omega
    simpa using this
  · have : (range ((A + p - r) / p)).card ≤ ((Icc 1 A).filter fun j => j % p = r).card := by
      refine card_le_card_of_injOn (fun t => t * p + r) ?_ ?_
      · intro t ht
        simp only [coe_range, Set.mem_Iio] at ht
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
        have h1 : (t + 1) * p ≤ (A + p - r) / p * p := Nat.mul_le_mul_right p ht
        have h2 := Nat.div_mul_le_self (A + p - r) p
        refine ⟨⟨by omega, by rw [add_mul, one_mul] at h1; omega⟩, ?_⟩
        rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
      · intro a _ b _ hab
        simp only at hab
        have : a * p = b * p := by omega
        exact Nat.eq_of_mul_eq_mul_right hp this
    simpa using this

theorem ell_exact {p : ℕ} (hp2 : p % 2 = 1) (A a : ℕ) (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    ell p A a = (A + p - a) / p + (A + a) / p := by
  have hp0 : 0 < p := by omega
  have hap : a < p := by unfold mHalf at ha; omega
  have hsplit : (Icc 1 A).filter (fun j => j % p = a % p ∨ (j + a) % p = 0) =
      (Icc 1 A).filter (fun j => j % p = a) ∪ (Icc 1 A).filter (fun j => j % p = p - a) := by
    rw [← filter_or]
    refine filter_congr fun j _ => ?_
    have hr : j % p < p := Nat.mod_lt _ hp0
    rw [Nat.mod_eq_of_lt hap, Nat.add_mod, Nat.mod_eq_of_lt hap, mod_add_small hr hap]
    omega
  have hd : Disjoint ((Icc 1 A).filter fun j => j % p = a) ((Icc 1 A).filter fun j => j % p = p - a) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_filter] at h1 h2
    unfold mHalf at ha; omega
  unfold ell
  rw [hsplit, card_union_of_disjoint hd, count_mod_eq A p a hp0 ha1 hap,
    count_mod_eq A p (p - a) hp0 (by omega) (by omega)]
  congr 2; omega

/-- The discrete class `a + 1` versus the grid cell `a`. -/
theorem ell_succ_eq {p : ℕ} (hp2 : p % 2 = 1) (A a : ℕ) (ha : a + 1 ≤ mHalf p) :
    (ell p A (a + 1) : ℤ) = ellZ p A a + (((A : ℤ) + a + 1) / p - ((A : ℤ) + a) / p) := by
  have hp0 : 0 < p := by omega
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [ell_exact hp2 A (a + 1) (by omega) ha]
  unfold ellZ
  have hap : a + 1 < p := by unfold mHalf at ha; omega
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  rw [show (A : ℤ) + p - (a + 1) = ((A : ℤ) - a - 1) + 1 * p by ring, Int.add_mul_ediv_right _ _ hpz]
  ring

/-- `∑_{a < m}` of the cell discrepancies telescopes. -/
theorem sum_disc (p A m : ℕ) (hp : 0 < p) (hm : m < p) :
    ∑ a ∈ range m, (((A : ℤ) + a + 1) / p - ((A : ℤ) + a) / p) ≤ 1 ∧
      ∀ a, 0 ≤ ((A : ℤ) + a + 1) / p - ((A : ℤ) + a) / p := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have mono : ∀ a, ((A : ℤ) + a) / p ≤ ((A : ℤ) + a + 1) / p := fun a =>
    Int.ediv_le_ediv hpz (by linarith)
  refine ⟨?_, fun a => by linarith [mono a]⟩
  have tele : ∀ k, ∑ a ∈ range k, (((A : ℤ) + a + 1) / p - ((A : ℤ) + a) / p) =
      ((A : ℤ) + k) / p - (A : ℤ) / p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [tele]
  have : ((A : ℤ) + m) / p ≤ ((A : ℤ) + p) / p := Int.ediv_le_ediv hpz (by linarith [(by exact_mod_cast hm.le : (m : ℤ) ≤ p)])
  rw [show (A : ℤ) + p = A + 1 * p by ring, Int.add_mul_ediv_right _ _ hpz.ne'] at this
  linarith

/-! ## The discrete side -/

theorem ell_cases {p : ℕ} (hp2 : p % 2 = 1) (A a : ℕ) (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    ell p A a = 2 * A / p ∨ ell p A a = 2 * A / p + 1 := by
  have hp0 : 0 < p := by omega
  rw [ell_exact hp2 A a ha1 ha]
  have hap : a < p := by unfold mHalf at ha; omega
  have hB : A + p - a + a = A + p := by omega
  generalize A + p - a = B at hB ⊢
  set u := B / p
  set v := (A + a) / p
  set q := 2 * A / p
  have u1 : u * p ≤ B := Nat.div_mul_le_self B p
  have u2 : B < p * (u + 1) := Nat.lt_mul_div_succ B hp0
  have v1 : v * p ≤ A + a := Nat.div_mul_le_self (A + a) p
  have v2 : A + a < p * (v + 1) := Nat.lt_mul_div_succ (A + a) hp0
  have q1 : q * p ≤ 2 * A := Nat.div_mul_le_self (2 * A) p
  have q2 : 2 * A < p * (q + 1) := Nat.lt_mul_div_succ (2 * A) hp0
  have hlt1 : (u + v) * p < (q + 2) * p := by
    push_cast [add_mul, mul_add] at *; linarith
  have hlt2 : (q + 1) * p < (u + v + 2) * p := by
    push_cast [add_mul, mul_add] at *; linarith
  have := Nat.lt_of_mul_lt_mul_right hlt1
  have := Nat.lt_of_mul_lt_mul_right hlt2
  omega

theorem card_inter_of_chain {P Q : Finset ℕ} (h : P ⊆ Q ∨ Q ⊆ P) :
    (P ∩ Q).card = min P.card Q.card := by
  rcases h with h | h
  · rw [inter_eq_left.mpr h, min_eq_left (card_le_card h)]
  · rw [inter_eq_right.mpr h, min_eq_right (card_le_card h)]

theorem sum_two_lin (L : ℕ) (c : ℚ) :
    ∑ i ∈ range L, 2 * ((i : ℚ) + c) = L * (L - 1) + 2 * L * c := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih]; push_cast; ring

section Disc

variable {K M : ℕ} (h : InnerHyp K M p)
include h

/-- The number of classes with `ℓ_K(a) = q + 1`. -/
def c1 (K p : ℕ) : ℕ := ((Icc 1 (mHalf p)).filter fun a => ell p K a = 2 * K / p + 1).card

theorem sum_ellK : ∑ a ∈ Icc 1 (mHalf p), ell p K a = mHalf p * (2 * K / p) + c1 K p := by
  have hp2 := (hyp_facts h).2.1
  have e : ∀ a ∈ Icc 1 (mHalf p), ell p K a =
      2 * K / p + if ell p K a = 2 * K / p + 1 then 1 else 0 := by
    intro a ha
    rcases ell_cases hp2 K a (mem_Icc.mp ha).1 (mem_Icc.mp ha).2 with e | e <;> simp [e]
  rw [sum_congr rfl e, sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel,
    sum_boole]
  rfl

theorem sum_ellK' : ∑ a ∈ Icc 1 (mHalf p), ell p K a = K - K / p := by
  have hp2 := (hyp_facts h).2.1
  have hell := sum_ell_eq (A := K) hp2
  rw [range_succ_eq_insert, sum_insert (by simp), ell_zero_eq] at hell
  omega

theorem c1_le : c1 K p ≤ mHalf p := by
  unfold c1
  calc _ ≤ (Icc 1 (mHalf p)).card := card_filter_le _ _
    _ = mHalf p := by simp

theorem sum_eps_ell :
    ∑ a ∈ Icc 1 (mHalf p), (epsIn K M p (defaultPos K p) a) * (ell p K a : ℤ) =
      (2 * K / p : ℕ) * Ein K M p + min (Ein K M p) (c1 K p) := by
  have hp2 := (hyp_facts h).2.1
  obtain ⟨hE0, hEm, -⟩ := TE_spec h
  set q := 2 * K / p
  set Et := (Ein K M p).toNat
  have hEt : (Et : ℤ) = Ein K M p := Int.toNat_of_nonneg hE0
  set P := (Icc 1 (mHalf p)).filter fun a => defaultPos K p a < Et
  set Q := (Icc 1 (mHalf p)).filter fun a => ell p K a = q + 1
  have hP : P.card = Et := card_pos_lt K p Et (by omega)
  have hQ : Q.card = c1 K p := rfl
  have e : ∀ a ∈ Icc 1 (mHalf p), (epsIn K M p (defaultPos K p) a) * (ell p K a : ℤ) =
      (if a ∈ P then (q : ℤ) else 0) + (if a ∈ P ∩ Q then 1 else 0) := by
    intro a ha
    rw [eps_char h]
    have hc := ell_cases hp2 K a (mem_Icc.mp ha).1 (mem_Icc.mp ha).2
    simp only [P, Q, mem_inter, mem_filter, ha, true_and]
    have : ((defaultPos K p a : ℤ) < Ein K M p) ↔ defaultPos K p a < Et := by omega
    by_cases h1 : defaultPos K p a < Et
    · rw [if_pos (this.mpr h1), if_pos h1]
      rcases hc with hc | hc
      · rw [if_neg (by omega), hc]; simp [q]
      · rw [if_pos ⟨h1, hc⟩, hc]; simp only [Nat.cast_add, Nat.cast_one]; ring
    · rw [if_neg (fun h' => h1 (this.mp h')), if_neg h1, if_neg (fun h' => h1 h'.1)]; simp
  rw [sum_congr rfl e, sum_add_distrib, sum_ite_mem, sum_ite_mem, sum_const, sum_const,
    inter_eq_right.mpr (filter_subset _ _), inter_eq_right.mpr (by
      intro x hx; exact (mem_filter.mp (mem_inter.mp hx).1).1)]
  have chain : P ⊆ Q ∨ Q ⊆ P := by
    by_contra hc
    simp only [not_or, not_subset] at hc
    obtain ⟨⟨c, hcP, hcQ⟩, ⟨a, haQ, haP⟩⟩ := hc
    simp only [P, Q, mem_filter] at hcP hcQ haQ haP
    have hcQ' : ell p K c ≠ q + 1 := fun e => hcQ ⟨hcP.1, e⟩
    have haP' : ¬ defaultPos K p a < Et := fun e => haP ⟨haQ.1, e⟩
    have hcl := ell_cases hp2 K c (mem_Icc.mp hcP.1).1 (mem_Icc.mp hcP.1).2
    have hb : before K p a c := by
      unfold before; left
      rcases hcl with e | e
      · rw [e, haQ.2]; omega
      · exact absurd e hcQ'
    have := (pos_lt_iff K p haQ.1).mpr hb
    have := hcP.2
    exact haP' (by omega)
  rw [card_inter_of_chain chain, hP, hQ]
  simp only [nsmul_eq_mul, mul_one]
  rw [hEt]
  push_cast
  rw [← hEt]
  ring

theorem eps_cases (a : ℕ) : epsIn K M p (defaultPos K p) a = 0 ∨ epsIn K M p (defaultPos K p) a = 1 := by
  unfold epsIn; split_ifs <;> simp

theorem class_sum (a : ℕ) (ha : a ∈ Icc 1 (mHalf p)) :
    ∑ i ∈ range (Lin K M p a).toNat, 2 * wIn K M p a i =
      ((gg (Tin K M p) (ell p (Nof K) a) (ell p K a) +
        epsIn K M p (defaultPos K p) a * (2 * Tin K M p - ell p K a - 4) : ℤ) : ℚ) := by
  have ha0 : a ≠ 0 := by simp only [mem_Icc] at ha; omega
  have hL := Lin_nonneg' h a (mem_Icc.mp ha).2
  have hLq : ((Lin K M p a).toNat : ℚ) = (Tin K M p : ℚ) - 3 * (ell p (Nof K) a : ℚ) +
      (epsIn K M p (defaultPos K p) a : ℚ) := by
    have : ((Lin K M p a).toNat : ℤ) = Lin K M p a := Int.toNat_of_nonneg hL
    have e2 : ((Lin K M p a).toNat : ℚ) = ((Lin K M p a : ℤ) : ℚ) := by exact_mod_cast this
    rw [e2]; unfold Lin bIn; rw [if_neg ha0]; push_cast; ring
  simp only [wIn, if_neg ha0]
  rw [sum_congr rfl fun (i : ℕ) _ => show 2 * ((i : ℚ) + (bIn K p a : ℚ) - ((ell p K a : ℚ) + 4) / 2) =
    2 * ((i : ℚ) + ((bIn K p a : ℚ) - ((ell p K a : ℚ) + 4) / 2)) by ring]
  rw [sum_two_lin, hLq]
  unfold gg bIn
  rcases eps_cases h a with e | e <;> rw [e] <;> push_cast <;> ring

/-- The discrete decomposition of `γ_p^in`. -/
theorem gamma_decomp :
    gammaIn K M p = 2 * ∑ i ∈ range (4 * M + 10), wIn K M p 0 i +
      (((∑ a ∈ Icc 1 (mHalf p), gg (Tin K M p) (ell p (Nof K) a) (ell p K a)) +
        Ein K M p * (2 * Tin K M p - (2 * K / p : ℕ) - 4) - min (Ein K M p) (c1 K p) : ℤ) : ℚ) := by
  unfold gammaIn
  rw [range_succ_eq_insert, sum_insert (by simp), mul_add]
  simp only [Finset.mul_sum]
  have hL0 : (Lin K M p 0).toNat = 4 * M + 10 := by simp [Lin, L0]; omega
  rw [hL0]
  congr 1
  rw [sum_congr rfl fun a ha => class_sum h a ha]
  have hE := sum_epsIn h
  have hEl := sum_eps_ell h
  have : ∑ a ∈ Icc 1 (mHalf p), (gg (Tin K M p) (ell p (Nof K) a) (ell p K a) +
      epsIn K M p (defaultPos K p) a * (2 * Tin K M p - ell p K a - 4)) =
      (∑ a ∈ Icc 1 (mHalf p), gg (Tin K M p) (ell p (Nof K) a) (ell p K a)) +
        Ein K M p * (2 * Tin K M p - (2 * K / p : ℕ) - 4) - min (Ein K M p) (c1 K p) := by
    rw [sum_add_distrib]
    have e : ∀ a ∈ Icc 1 (mHalf p), epsIn K M p (defaultPos K p) a * (2 * Tin K M p - ell p K a - 4) =
        epsIn K M p (defaultPos K p) a * (2 * Tin K M p - 4) -
          epsIn K M p (defaultPos K p) a * (ell p K a : ℤ) := fun a _ => by ring
    rw [sum_congr rfl e, sum_sub_distrib, ← sum_mul, hE, hEl]
    ring
  rw [← Int.cast_sum, this]

theorem Tin_ge : -1 ≤ Tin K M p := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  have hL := Lin_nonneg' h 1 (by unfold mHalf; omega)
  have he := epsIn_le_one K M p (defaultPos K p) 1
  have hb : (0 : ℤ) ≤ bIn K p 1 := by unfold bIn; positivity
  unfold Lin at hL; rw [if_neg (by norm_num)] at hL
  linarith

theorem w0_bound (i : ℕ) (hi : i < 4 * M + 10) : |wIn K M p 0 i| ≤ 15 * M := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  have hM := h.1
  have hT := Tin_ge h
  have hMq : (40 : ℚ) ≤ M := by exact_mod_cast hM
  have hKq : ((K / p : ℕ) : ℚ) ≤ M := by exact_mod_cast hKp.le
  have hNq : ((Nof K / p : ℕ) : ℚ) ≤ M := by exact_mod_cast hNp.le
  have hiq : (i : ℚ) + 1 ≤ 4 * M + 10 := by exact_mod_cast hi
  simp only [wIn, if_true]
  rw [abs_le]
  constructor
  · rw [Finset.le_fold_min]
    refine ⟨by have : (0 : ℚ) ≤ i := by positivity
               have : (0 : ℚ) ≤ ((Nof K / p : ℕ) : ℚ) := by positivity
               linarith, fun c hc => ?_⟩
    have hl := (ell_bounds hp2 K c (mem_Icc.mp hc).1 (mem_Icc.mp hc).2).2
    have hlq : (ell p K c : ℚ) ≤ 2 * M + 2 := by
      have : ell p K c ≤ 2 * M + 2 := by omega
      exact_mod_cast this
    have he := epsIn_nonneg K M p (defaultPos K p) c
    have hZ : (-1 : ℚ) ≤ Zin K M p c := by
      unfold Zin; have : (-1 : ℤ) ≤ Tin K M p + epsIn K M p (defaultPos K p) c := by linarith
      exact_mod_cast this
    linarith
  · rw [Finset.fold_min_le]
    left
    have : (0 : ℚ) ≤ ((K / p : ℕ) : ℚ) := by positivity
    linarith

theorem Z0_bound : |2 * ∑ i ∈ range (4 * M + 10), wIn K M p 0 i| ≤ 150 * M ^ 2 := by
  have hM := h.1
  have hMq : (40 : ℚ) ≤ M := by exact_mod_cast hM
  rw [abs_mul, abs_two]
  have := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => w0_bound h i (mem_range.mp hi))
  rw [sum_const, card_range, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

theorem Gam_eq :
    (p : ℝ) * Lim.Gam ((K : ℝ) / p) =
      p * (∫ z in (0 : ℝ)..(1 / 2), phiZ p (Nof K) K ⌊2 * Lim.Hc * ((K : ℝ) / p)⌋ z) +
      p * (Lim.Hc * ((K : ℝ) / p) - (⌊2 * Lim.Hc * ((K : ℝ) / p)⌋ : ℝ) / 2) *
        (2 * (⌊2 * Lim.Hc * ((K : ℝ) / p)⌋ : ℝ) - (2 * K / p : ℕ) - 4) -
      min (p * (Lim.Hc * ((K : ℝ) / p) - (⌊2 * Lim.Hc * ((K : ℝ) / p)⌋ : ℝ) / 2))
        ((K : ℝ) - p * (2 * K / p : ℕ) / 2) := by
  obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hN : ((Nof (40 * n) : ℕ) : ℝ) = 3 * n := by unfold Nof; push_cast [show 3 * (40 * n) / 40 = 3 * n by omega]; ring
  have hα : Lim.α * (((40 * n : ℕ) : ℝ) / p) = ((Nof (40 * n) : ℕ) : ℝ) / p := by
    rw [hN]; unfold Lim.α; push_cast; ring
  have hq : ⌊2 * (((40 * n : ℕ) : ℝ) / p)⌋ = ((2 * (40 * n) / p : ℕ) : ℤ) := by
    rw [← floor_nat_div]; push_cast; ring_nf
  unfold Lim.Gam
  simp only []
  rw [hα, hq]
  unfold phiZ Lim.pos
  have hmax : ∀ a b : ℝ, max (a - b) 0 = a - min a b := fun a b => by
    rcases le_total a b with hab | hab
    · rw [max_eq_right (by linarith), min_eq_left hab]; ring
    · rw [max_eq_left (by linarith), min_eq_right hab]
  simp only [Int.cast_natCast]
  generalize ((2 * (40 * n) / p : ℕ) : ℝ) = Q
  generalize ((40 * n : ℕ) : ℝ) = X
  have e : (p : ℝ) * ((2 * (X / p) - Q) / 2) = X - p * Q / 2 := by
    field_simp
  rw [hmax, ← e, ← mul_min_of_nonneg _ _ hp0.le]
  ring

end Disc

/-! ## Discrete sum versus the integral -/

theorem sum_Icc_shift (f : ℕ → ℤ) (m : ℕ) : ∑ a ∈ Icc 1 m, f a = ∑ a ∈ range m, f (a + 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem ellZ_bounds {p : ℕ} (hp : 0 < p) (A a : ℕ) (ha : a < p) :
    0 ≤ ellZ p A a ∧ ellZ p A a ≤ 2 * ((A / p : ℕ) : ℤ) + 2 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hap : (a : ℤ) < p := by exact_mod_cast ha
  unfold ellZ
  have h1 : -1 ≤ ((A : ℤ) - a - 1) / p := by
    rw [Int.le_ediv_iff_mul_le hpz]; linarith
  have h2 : ((A : ℤ) - a - 1) / p ≤ (A : ℤ) / p := Int.ediv_le_ediv hpz (by linarith)
  have h3 : ((A : ℤ) + a) / p ≤ ((A : ℤ) + 1 * p) / p := Int.ediv_le_ediv hpz (by linarith)
  rw [Int.add_mul_ediv_right _ _ hpz.ne'] at h3
  have h4 : 0 ≤ ((A : ℤ) + a) / p := Int.ediv_nonneg (by positivity) hpz.le
  have e : ((A / p : ℕ) : ℤ) = (A : ℤ) / p := by push_cast; rfl
  rw [e]
  constructor <;> linarith

theorem disc_01 {p : ℕ} (hp : 0 < p) (A a : ℕ) :
    ((A : ℤ) + a + 1) / p - ((A : ℤ) + a) / p = 0 ∨ ((A : ℤ) + a + 1) / p - ((A : ℤ) + a) / p = 1 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 : ((A : ℤ) + a) / p ≤ ((A : ℤ) + a + 1) / p := Int.ediv_le_ediv hpz (by linarith)
  have h2 : ((A : ℤ) + a + 1) / p ≤ ((A : ℤ) + a + 1 * p) / p := Int.ediv_le_ediv hpz (by linarith)
  rw [Int.add_mul_ediv_right _ _ hpz.ne'] at h2
  omega

theorem gg_lip (M : ℕ) (hM : 40 ≤ M) (T v l dv dl : ℤ) (hT1 : -2 ≤ T) (hT2 : T ≤ 4 * M + 1)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * M) (hl0 : 0 ≤ l) (hl : l ≤ 2 * M)
    (hdv : dv = 0 ∨ dv = 1) (hdl : dl = 0 ∨ dl = 1) :
    |gg T (v + dv) (l + dl) - gg T v l| ≤ 100 * M * (dv + dl) := by
  have hM' : (40 : ℤ) ≤ M := by exact_mod_cast hM
  unfold gg
  rw [abs_le]
  rcases hdv with rfl | rfl <;> rcases hdl with rfl | rfl <;> constructor <;> ring_nf <;> nlinarith

theorem gg_bound (M : ℕ) (hM : 40 ≤ M) (T v l : ℤ) (hT1 : -2 ≤ T) (hT2 : T ≤ 4 * M + 1)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * M) (hl0 : 0 ≤ l) (hl : l ≤ 2 * M) :
    |gg T v l| ≤ 150 * M ^ 2 := by
  have hM' : (40 : ℤ) ≤ M := by exact_mod_cast hM
  unfold gg
  rw [abs_mul]
  have h1 : |T - 3 * v| ≤ 11 * M := by rw [abs_le]; constructor <;> linarith
  have h2 : |T + 3 * v - l - 5| ≤ 13 * M := by rw [abs_le]; constructor <;> linarith
  calc |T - 3 * v| * |T + 3 * v - l - 5| ≤ (11 * M) * (13 * M) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
    _ ≤ 150 * M ^ 2 := by nlinarith

section Cmp

variable {K M : ℕ} (h : InnerHyp K M p)
include h

theorem S_vs_I (T : ℤ) (hT1 : -2 ≤ T) (hT2 : T ≤ 4 * M + 1) :
    |((∑ a ∈ Icc 1 (mHalf p), gg T (ell p (Nof K) a) (ell p K a) : ℤ) : ℝ) -
      p * ∫ z in (0 : ℝ)..(1 / 2), phiZ p (Nof K) K T z| ≤ 100 * M ^ 2 := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  have hM := h.1
  have hp0 : 0 < p := by omega
  set m := mHalf p
  rw [integral_sum p (Nof K) K m hpm.symm T, sum_Icc_shift]
  have hKp' : ((K / p : ℕ) : ℤ) ≤ M - 1 := by have := hKp; omega
  have hNp' : ((Nof K / p : ℕ) : ℤ) ≤ M - 1 := by have := hNp; omega
  -- per-cell comparison
  have cell : ∀ a ∈ range m, |gg T (ell p (Nof K) (a + 1)) (ell p K (a + 1)) -
      gg T (ellZ p (Nof K) a) (ellZ p K a)| ≤
      100 * M * ((((Nof K : ℤ) + a + 1) / p - ((Nof K : ℤ) + a) / p) +
        (((K : ℤ) + a + 1) / p - ((K : ℤ) + a) / p)) := by
    intro a ha
    have ham : a + 1 ≤ m := by rw [mem_range] at ha; omega
    have hap : a < p := by omega
    rw [ell_succ_eq hp2 (Nof K) a ham, ell_succ_eq hp2 K a ham]
    have bN := ellZ_bounds hp0 (Nof K) a hap
    have bK := ellZ_bounds hp0 K a hap
    exact gg_lip M hM T _ _ _ _ hT1 hT2 bN.1 (by linarith) bK.1 (by linarith)
      (disc_01 hp0 _ _) (disc_01 hp0 _ _)
  have hsum := abs_sum_le_sum_abs (fun a => gg T (ell p (Nof K) (a + 1)) (ell p K (a + 1)) -
      gg T (ellZ p (Nof K) a) (ellZ p K a)) (range m)
  have hsum2 := sum_le_sum cell
  rw [← Finset.mul_sum, sum_add_distrib] at hsum2
  have dN := (sum_disc p (Nof K) m hp0 (by omega)).1
  have dK := (sum_disc p K m hp0 (by omega)).1
  have hM' : (40 : ℤ) ≤ M := by exact_mod_cast hM
  have hdiff : |∑ a ∈ range m, gg T (ell p (Nof K) (a + 1)) (ell p K (a + 1)) -
      ∑ a ∈ range m, gg T (ellZ p (Nof K) a) (ellZ p K a)| ≤ 200 * M := by
    rw [← sum_sub_distrib]
    refine hsum.trans (hsum2.trans ?_)
    nlinarith
  have bNm := ellZ_bounds hp0 (Nof K) m (by omega)
  have bKm := ellZ_bounds hp0 K m (by omega)
  have hlast := gg_bound M hM T _ _ hT1 hT2 bNm.1 (by linarith) bKm.1 (by linarith)
  have hdiffR : |((∑ a ∈ range m, gg T (ell p (Nof K) (a + 1)) (ell p K (a + 1)) : ℤ) : ℝ) -
      ((∑ a ∈ range m, gg T (ellZ p (Nof K) a) (ellZ p K a) : ℤ) : ℝ)| ≤ 200 * M := by
    rw [← Int.cast_sub, ← Int.cast_abs]; exact_mod_cast hdiff
  have hlastR : |((gg T (ellZ p (Nof K) m) (ellZ p K m) : ℤ) : ℝ)| ≤ 150 * M ^ 2 := by
    rw [← Int.cast_abs]; exact_mod_cast hlast
  push_cast at hdiffR ⊢
  have hMr : (40 : ℝ) ≤ M := by exact_mod_cast hM
  rw [abs_le] at hdiffR hlastR ⊢
  constructor <;> nlinarith [hdiffR.1, hdiffR.2, hlastR.1, hlastR.2]

end Cmp

/-! ## The comparison functions -/

def Sd (K p : ℕ) (T : ℤ) : ℤ := ∑ a ∈ Icc 1 (mHalf p), gg T (ell p (Nof K) a) (ell p K a)

def Dd (K p : ℕ) (T : ℤ) (E : ℝ) : ℝ :=
  Sd K p T + E * (2 * T - (2 * K / p : ℕ) - 4) - min E (c1 K p)

def Cc (K p : ℕ) (T : ℤ) (σ : ℝ) : ℝ :=
  p * (∫ z in (0 : ℝ)..(1 / 2), phiZ p (Nof K) K T z) + σ * (2 * T - (2 * K / p : ℕ) - 4) -
    min σ ((K : ℝ) - p * (2 * K / p : ℕ) / 2)

section Cmp2

variable {K M : ℕ} (h : InnerHyp K M p)
include h

theorem Dd_trans (T : ℤ) : Dd K p T (mHalf p) = Dd K p (T + 1) 0 := by
  have hs := sum_ellK h
  have hc := c1_le h
  unfold Dd Sd
  generalize 2 * K / p = q at hs ⊢
  have e : ∑ a ∈ Icc 1 (mHalf p), gg (T + 1) (ell p (Nof K) a) (ell p K a) =
      ∑ a ∈ Icc 1 (mHalf p), gg T (ell p (Nof K) a) (ell p K a) +
        (mHalf p : ℤ) * (2 * T - 4) - ((mHalf p * q + c1 K p : ℕ) : ℤ) := by
    rw [← hs]
    push_cast
    have : ∀ a ∈ Icc 1 (mHalf p), gg (T + 1) (ell p (Nof K) a) (ell p K a) =
        gg T (ell p (Nof K) a) (ell p K a) + ((2 * T - 4) - (ell p K a : ℤ)) := fun a _ => by
      unfold gg; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  rw [e, min_eq_right (by exact_mod_cast hc), min_eq_left (by positivity)]
  push_cast
  ring

theorem q_le : 2 * K / p ≤ 2 * M := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  obtain ⟨hM, hK40, hK0, hKM, hpM, h3p⟩ := h
  apply Nat.div_le_of_le_mul
  have : p * (2 * M) = 2 * (p * M) := by ring
  omega

theorem slope_bound (T : ℤ) (hT1 : -2 ≤ T) (hT2 : T ≤ 4 * M + 1) :
    |2 * (T : ℝ) - (2 * K / p : ℕ) - 4| ≤ 11 * M := by
  have hq := q_le h
  have hM := h.1
  have hqr : ((2 * K / p : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ ((2 * K / p : ℕ) : ℝ) := by positivity
  have hT1' : (-2 : ℝ) ≤ T := by exact_mod_cast hT1
  have hT2' : (T : ℝ) ≤ 4 * M + 1 := by exact_mod_cast hT2
  have hMr : (40 : ℝ) ≤ M := by exact_mod_cast hM
  rw [abs_le]; constructor <;> linarith

theorem Dd_lip (T : ℤ) (hT1 : -2 ≤ T) (hT2 : T ≤ 4 * M + 1) (E1 E2 : ℝ) :
    |Dd K p T E1 - Dd K p T E2| ≤ |E1 - E2| * (11 * M + 1) := by
  have hs := slope_bound h T hT1 hT2
  unfold Dd
  have hmin := abs_min_sub_min_le_max E1 (c1 K p : ℝ) E2 (c1 K p)
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at hmin
  have e : (Sd K p T : ℝ) + E1 * (2 * T - (2 * K / p : ℕ) - 4) - min E1 (c1 K p) -
      ((Sd K p T : ℝ) + E2 * (2 * T - (2 * K / p : ℕ) - 4) - min E2 (c1 K p)) =
      (E1 - E2) * (2 * T - (2 * K / p : ℕ) - 4) - (min E1 (c1 K p) - min E2 (c1 K p)) := by ring
  rw [e]
  calc _ ≤ |(E1 - E2) * (2 * T - (2 * K / p : ℕ) - 4)| + |min E1 (c1 K p) - min E2 (c1 K p)| :=
        abs_sub _ _
    _ ≤ |E1 - E2| * (11 * M) + |E1 - E2| := by
        rw [abs_mul]; gcongr
    _ = _ := by ring

theorem c1_close : |(c1 K p : ℝ) - ((K : ℝ) - p * (2 * K / p : ℕ) / 2)| ≤ 1 := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  have hs := sum_ellK h
  have hs' := sum_ellK' h
  have hKle : K / p ≤ K := Nat.div_le_self _ _
  have e : mHalf p * (2 * K / p) + c1 K p + K / p = K := by omega
  have e' : ((mHalf p : ℕ) : ℝ) * ((2 * K / p : ℕ) : ℝ) + (c1 K p : ℝ) + ((K / p : ℕ) : ℝ) = K := by
    exact_mod_cast e
  have hpr : (p : ℝ) = 2 * mHalf p + 1 := by exact_mod_cast hpm.symm
  -- `q ∈ {2⌊K/p⌋, 2⌊K/p⌋ + 1}`
  have hp0 : 0 < p := by omega
  have hq1 : 2 * (K / p) ≤ 2 * K / p := by
    rw [Nat.le_div_iff_mul_le hp0]; have := Nat.div_mul_le_self K p; linarith
  have hq2 : 2 * K / p ≤ 2 * (K / p) + 1 := by
    have := Nat.lt_mul_div_succ K hp0
    have : 2 * K / p < 2 * (K / p) + 2 := by
      rw [Nat.div_lt_iff_lt_mul hp0]; nlinarith
    omega
  have hq1' : 2 * ((K / p : ℕ) : ℝ) ≤ ((2 * K / p : ℕ) : ℝ) := by exact_mod_cast hq1
  have hq2' : ((2 * K / p : ℕ) : ℝ) ≤ 2 * ((K / p : ℕ) : ℝ) + 1 := by exact_mod_cast hq2
  rw [hpr, abs_le]
  constructor <;> nlinarith

theorem Dd_Cc (T : ℤ) (hT1 : -2 ≤ T) (hT2 : T ≤ 4 * M + 1) (E σ : ℝ) :
    |Dd K p T E - Cc K p T σ| ≤ 100 * M ^ 2 + |E - σ| * (11 * M + 1) + 1 := by
  have hs := slope_bound h T hT1 hT2
  have hSI := S_vs_I h T hT1 hT2
  have hc := c1_close h
  unfold Dd Cc
  have hmin := abs_min_sub_min_le_max E (c1 K p : ℝ) σ ((K : ℝ) - p * (2 * K / p : ℕ) / 2)
  have hmin' : |min E (c1 K p : ℝ) - min σ ((K : ℝ) - p * (2 * K / p : ℕ) / 2)| ≤ |E - σ| + 1 :=
    hmin.trans (max_le (by linarith [abs_nonneg (E - σ)]) (by linarith [abs_nonneg (E - σ)]))
  set I := ∫ z in (0 : ℝ)..(1 / 2), phiZ p (Nof K) K T z
  set sl := 2 * (T : ℝ) - (2 * K / p : ℕ) - 4
  have e : (Sd K p T : ℝ) + E * sl - min E (c1 K p) -
      (p * I + σ * sl - min σ ((K : ℝ) - p * (2 * K / p : ℕ) / 2)) =
      ((Sd K p T : ℝ) - p * I) + (E - σ) * sl -
        (min E (c1 K p : ℝ) - min σ ((K : ℝ) - p * (2 * K / p : ℕ) / 2)) := by ring
  rw [e]
  have hSd : (Sd K p T : ℝ) = ((∑ a ∈ Icc 1 (mHalf p), gg T (ell p (Nof K) a) (ell p K a) : ℤ) : ℝ) := rfl
  calc _ ≤ |((Sd K p T : ℝ) - p * I) + (E - σ) * sl| +
        |min E (c1 K p : ℝ) - min σ ((K : ℝ) - p * (2 * K / p : ℕ) / 2)| := abs_sub _ _
    _ ≤ |(Sd K p T : ℝ) - p * I| + |(E - σ) * sl| + (|E - σ| + 1) := by
        gcongr; exact abs_add_le _ _
    _ ≤ 100 * M ^ 2 + |E - σ| * (11 * M) + (|E - σ| + 1) := by
        rw [abs_mul, hSd]; gcongr
    _ = _ := by ring

end Cmp2

/-! ## Assembly -/

section Final

variable {K M : ℕ} (h : InnerHyp K M p)
include h

theorem gamma_real :
    (gammaIn K M p : ℝ) = ((2 * ∑ i ∈ range (4 * M + 10), wIn K M p 0 i : ℚ) : ℝ) +
      Dd K p (Tin K M p) (Ein K M p) := by
  rw [gamma_decomp h]
  unfold Dd Sd
  generalize 2 * K / p = q
  push_cast
  ring

/-- The fill relation: `mT + E = m·(2Hx) + Δ` with `|Δ| ≤ 8M`, where `x = K/p`. -/
theorem fill_rel :
    |((mHalf p : ℝ) * Tin K M p + Ein K M p) - mHalf p * (2 * Lim.Hc * ((K : ℝ) / p))| ≤ 8 * M := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  obtain ⟨-, -, hTE⟩ := TE_spec h
  obtain ⟨hM, ⟨n, rfl⟩, hK0, hKM, hpM, h3p⟩ := h
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  unfold rhs44 L0 at hTE
  simp only [hN, hh] at hTE hNp
  have hTE' : ((mHalf p : ℝ) * Tin (40 * n) M p + Ein (40 * n) M p) =
      37 * n - (4 * M + 10) + 3 * (3 * n - ((3 * n / p : ℕ) : ℝ)) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hTE
    generalize 3 * n / p = r at this ⊢
    push_cast at this ⊢
    linarith
  have hpr : (p : ℝ) = 2 * mHalf p + 1 := by exact_mod_cast hpm.symm
  have hp0 : (0 : ℝ) < p := by linarith [(by positivity : (0 : ℝ) ≤ mHalf p)]
  have hmv : (mHalf p : ℝ) * (2 * Lim.Hc * (((40 * n : ℕ) : ℝ) / p)) = 46 * n - 46 * n / p := by
    unfold Lim.Hc
    have : (mHalf p : ℝ) = (p - 1) / 2 := by linarith
    rw [this]; push_cast; field_simp; ring
  have hnp : (40 * n : ℝ) < p * M := by exact_mod_cast hpM
  have hnp' : 46 * (n : ℝ) / p ≤ 46 * M / 40 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; nlinarith
  have hnp0 : 0 ≤ 46 * (n : ℝ) / p := by positivity
  have hNr : ((3 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hNp.le
  have hN0 : (0 : ℝ) ≤ ((3 * n / p : ℕ) : ℝ) := by positivity
  have hMr : (40 : ℝ) ≤ M := by exact_mod_cast hM
  rw [hTE', hmv, abs_le]
  constructor <;> linarith

theorem m_large : 100 * (M : ℝ) ≤ mHalf p := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  have hb := (innerHyp_bounds h).1
  have : 100 * M ≤ mHalf p := by omega
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
theorem gamma_bound : |(gammaIn K M p : ℝ) - p * Lim.Gam ((K : ℝ) / p)| ≤ 1000 * M ^ 2 := by
  obtain ⟨hp7, hp2, hpm, hKp, hNp⟩ := hyp_facts h
  have hM := h.1
  have hMr : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : 40 * (M : ℝ) ≤ M ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hMr (by linarith)
  have hTl := Tin_ge h
  have hTu := Tin_le h
  obtain ⟨hE0, hEm, -⟩ := TE_spec h
  have hZ : |((2 * ∑ i ∈ range (4 * M + 10), wIn K M p 0 i : ℚ) : ℝ)| ≤ 150 * M ^ 2 := by
    have := Z0_bound h
    rw [← Rat.cast_abs]; exact_mod_cast this
  have hG : (p : ℝ) * Lim.Gam ((K : ℝ) / p) =
      Cc K p ⌊2 * Lim.Hc * ((K : ℝ) / p)⌋ (p * (Lim.Hc * ((K : ℝ) / p) -
        (⌊2 * Lim.Hc * ((K : ℝ) / p)⌋ : ℝ) / 2)) := by
    rw [Gam_eq h]; rfl
  rw [gamma_real h, hG]
  have hfill := fill_rel h
  have hml := m_large h
  set m : ℝ := (mHalf p : ℝ) with hm
  set v : ℝ := 2 * Lim.Hc * ((K : ℝ) / p) with hv
  set T := Tin K M p
  set E : ℝ := ((Ein K M p : ℤ) : ℝ) with hEdef
  set Tf := ⌊v⌋
  have hpr : (p : ℝ) = 2 * m + 1 := by rw [hm]; exact_mod_cast hpm.symm
  have hσ : (p : ℝ) * (Lim.Hc * ((K : ℝ) / p) - (Tf : ℝ) / 2) = (2 * m + 1) * (v - Tf) / 2 := by
    rw [hv]; linear_combination (2 * Lim.Hc * ((K : ℝ) / p) - Tf) / 2 * hpr
  rw [hσ]
  set σ := (2 * m + 1) * (v - Tf) / 2
  set Δ := (m * T + E) - m * v with hΔ
  have hΔb := abs_le.mp hfill
  have hE0r : (0 : ℝ) ≤ E := by rw [hEdef]; exact_mod_cast hE0
  have hEmr : E < m := by rw [hEdef, hm]; exact_mod_cast hEm
  have hf1 : (Tf : ℝ) ≤ v := Int.floor_le v
  have hf2 : v < (Tf : ℝ) + 1 := Int.lt_floor_add_one v
  set Z := ((2 * ∑ i ∈ range (4 * M + 10), wIn K M p 0 i : ℚ) : ℝ)
  have hTl' : (-1 : ℝ) ≤ T := by exact_mod_cast hTl
  have hTu' : (T : ℝ) ≤ 4 * M := by exact_mod_cast hTu
  -- `T_f ∈ {T - 1, T, T + 1}`
  have hup : Tf ≤ T + 1 := by
    by_contra hc
    have : (T : ℝ) + 2 ≤ Tf := by exact_mod_cast (by omega : T + 2 ≤ Tf)
    nlinarith
  have hlo : T - 1 ≤ Tf := by
    by_contra hc
    have : (Tf : ℝ) ≤ T - 2 := by exact_mod_cast (by omega : Tf ≤ T - 2)
    nlinarith
  have hsplit : Z + Dd K p T E - Cc K p Tf σ = Z + (Dd K p T E - Cc K p Tf σ) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rcases (show Tf = T ∨ Tf = T + 1 ∨ Tf = T - 1 by omega) with e | e | e
  · -- no transition
    have hTf : (Tf : ℝ) = T := by exact_mod_cast e
    rw [e]
    have hc := Dd_Cc h T (by omega) (by omega) E σ
    have hEσ : |E - σ| ≤ 8 * M + 1 := by
      have : E - σ = Δ - (v - T) / 2 := by rw [hΔ]; simp only [σ]; rw [hTf]; ring
      rw [this, abs_le]; constructor <;> linarith
    have f1 : |E - σ| * (11 * M + 1) ≤ (8 * M + 1) * (11 * M + 1) :=
      mul_le_mul_of_nonneg_right hEσ (by positivity)
    have g1 : (8 * (M : ℝ) + 1) * (11 * M + 1) = 88 * M ^ 2 + 19 * M + 1 := by ring
    linarith
  · -- `T_f = T + 1`
    have hTf : (Tf : ℝ) = T + 1 := by rw [e]; push_cast; ring
    rw [e]
    have hl := Dd_lip h T (by omega) (by omega) E m
    have htr := Dd_trans h T
    have hc := Dd_Cc h (T + 1) (by omega) (by omega) 0 σ
    have hmE : m - E ≤ 8 * M := by
      have : m * (T + 1) ≤ m * v := by rw [← hTf]; exact mul_le_mul_of_nonneg_left hf1 (by linarith)
      linarith
    have hσ0 : 0 ≤ σ := by simp only [σ]; rw [hTf] at hf1 ⊢; nlinarith
    have hσ1 : σ ≤ 12 * M := by
      have h1 : m * (v - Tf) ≤ 8 * M := by rw [hTf]; linarith
      have h2 : 2 * m * σ = (2 * m + 1) * (m * (v - Tf)) := by simp only [σ]; ring
      have h3 : (0 : ℝ) ≤ m * (v - Tf) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have eq : Dd K p T E - Cc K p (T + 1) σ =
        (Dd K p T E - Dd K p T m) + (Dd K p (T + 1) 0 - Cc K p (T + 1) σ) := by
      rw [hm, htr]; ring
    rw [eq]
    have hab := abs_add_le (Dd K p T E - Dd K p T m) (Dd K p (T + 1) 0 - Cc K p (T + 1) σ)
    have e1 : |E - m| ≤ 8 * M := by rw [abs_le]; constructor <;> linarith
    have e2 : |(0 : ℝ) - σ| ≤ 12 * M := by rw [abs_le]; constructor <;> linarith
    have f1 := mul_le_mul_of_nonneg_right e1 (by positivity : (0 : ℝ) ≤ 11 * M + 1)
    have f2 := mul_le_mul_of_nonneg_right e2 (by positivity : (0 : ℝ) ≤ 11 * M + 1)
    have g1 : 8 * (M : ℝ) * (11 * M + 1) = 88 * M ^ 2 + 8 * M := by ring
    have g2 : 12 * (M : ℝ) * (11 * M + 1) = 132 * M ^ 2 + 12 * M := by ring
    linarith
  · -- `T_f = T - 1`
    have hTf : (Tf : ℝ) = T - 1 := by rw [e]; push_cast; ring
    rw [e]
    have hl := Dd_lip h T (by omega) (by omega) E 0
    have htr := Dd_trans h (T - 1)
    rw [sub_add_cancel] at htr
    have hc := Dd_Cc h (T - 1) (by omega) (by omega) m σ
    have hE8 : E ≤ 8 * M := by
      have : m * v ≤ m * T := by
        have : v ≤ T := by linarith
        exact mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    have hmσ : |m - σ| ≤ 12 * M := by
      have h1 : m * (T - v) ≤ 8 * M := by linarith
      have h1' : 0 ≤ T - v := by linarith
      have h2 : m - σ = -1 / 2 + (2 * m + 1) * (T - v) / 2 := by simp only [σ]; rw [hTf]; ring
      have h3 : (0 : ℝ) ≤ m * (T - v) := mul_nonneg (by linarith) h1'
      have h4 : (T : ℝ) - v ≤ 1 := by linarith
      rw [h2, abs_le]; constructor <;> nlinarith
    have eq : Dd K p T E - Cc K p (T - 1) σ =
        (Dd K p T E - Dd K p T 0) + (Dd K p (T - 1) m - Cc K p (T - 1) σ) := by
      rw [hm, htr]; ring
    rw [eq]
    have hab := abs_add_le (Dd K p T E - Dd K p T 0) (Dd K p (T - 1) m - Cc K p (T - 1) σ)
    have e1 : |E - 0| ≤ 8 * M := by rw [sub_zero, abs_le]; constructor <;> linarith
    have f1 := mul_le_mul_of_nonneg_right e1 (by positivity : (0 : ℝ) ≤ 11 * M + 1)
    have f2 := mul_le_mul_of_nonneg_right hmσ (by positivity : (0 : ℝ) ≤ 11 * M + 1)
    have g1 : 8 * (M : ℝ) * (11 * M + 1) = 88 * M ^ 2 + 8 * M := by ring
    have g2 : 12 * (M : ℝ) * (11 * M + 1) = 132 * M ^ 2 + 12 * M := by ring
    linarith

end Final

end U57

/-- **Lemma 5.7** (the inner-range uniformity), with `C(M) = 1000 M²`. -/
theorem uniformity_5_7' (M : ℕ) (hM : 40 ≤ M) :
    ∃ Cst : ℝ, ∀ K p : ℕ, [Fact p.Prime] → InnerHyp K M p →
      |(gammaIn K M p : ℝ) - p * Lim.Gam ((K : ℝ) / p)| ≤ Cst ∧
      |(vpS K p : ℝ) - p * Lim.Nfun ((K : ℝ) / p)| ≤ Cst := by
  refine ⟨1000 * M ^ 2, fun K p _ h => ⟨U57.gamma_bound h, (U57.vpS_bound h).trans ?_⟩⟩
  have : (40 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith

end Zeta5
