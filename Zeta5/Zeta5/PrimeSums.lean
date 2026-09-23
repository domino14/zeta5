import Zeta5.Defs
import Zeta5.PNT

/-!
# Prime sums via the prime number theorem

Consequences of `prime_number_theorem` used in Proposition 5.2: Riemann-sum limits of
`∑ φ(p/K) log p` over primes (upper bounds for bounded, almost-everywhere continuous `φ`), the
inner-range version in the variable `x = K/p`, and the small-prime bound.
-/

open Finset Filter Topology MeasureTheory

noncomputable section

namespace Zeta5

namespace PS

open Chebyshev in
/-- `θ(x)` as a filtered sum over `range N`. -/
lemma theta_eq_filter (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hxN : x < N) :
    θ x = ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ x), Real.log p := by
  rw [Chebyshev.theta]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_Ioc, mem_range]
  constructor
  · rintro ⟨⟨-, hp⟩, hpr⟩
    have := (Nat.le_floor_iff hx0).1 hp
    exact ⟨by exact_mod_cast this.trans_lt hxN, hpr, this⟩
  · rintro ⟨-, hpr, hp⟩
    exact ⟨⟨hpr.pos, (Nat.le_floor_iff hx0).2 hp⟩, hpr⟩

open Chebyshev in
/-- Sum of `log p` over primes in `(c, d]` is `θ(d) - θ(c)`. -/
lemma sum_cell (N : ℕ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hdN : d < N) :
    ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ c < p ∧ (p : ℝ) ≤ d), Real.log p = θ d - θ c := by
  rw [theta_eq_filter N (hc.trans hcd) hdN, theta_eq_filter N hc (hcd.trans_lt hdN),
    eq_sub_iff_add_eq, ← Finset.sum_union]
  · congr 1
    ext p
    simp only [mem_union, mem_filter, mem_range]
    constructor
    · rintro (⟨h1, h2, -, h4⟩ | ⟨h1, h2, h3⟩)
      exacts [⟨h1, h2, h4⟩, ⟨h1, h2, h3.trans hcd⟩]
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_ge c p with h | h
      exacts [Or.inl ⟨h1, h2, h, h3⟩, Or.inr ⟨h1, h2, h⟩]
  · exact Finset.disjoint_filter.2 fun p _ h1 h2 => by linarith [h1.2.1, h2.2]

open Chebyshev in
lemma theta_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun K : ℕ => θ (c * K) / K) atTop (𝓝 c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  · have h1 : Tendsto (fun K : ℕ => c * (K : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc
    have h2 := (prime_number_theorem.comp h1).const_mul c
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    simp only [Function.comp]
    field_simp

open Chebyshev in
lemma cell_tendsto (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Tendsto (fun K : ℕ => (θ (d * K) - θ (c * K)) / K) atTop (𝓝 (d - c)) := by
  simpa [sub_div] using (theta_tendsto d hd).sub (theta_tendsto c hc)

open Chebyshev in
/-- Eventually `θ(dK) - θ(cK) ≤ (d - c + δ) K`. -/
lemma cell_upper (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ K : ℕ in atTop, θ (d * K) - θ (c * K) ≤ (d - c + δ) * K := by
  filter_upwards [(cell_tendsto c d hc hd).eventually (Iio_mem_nhds (by linarith : d - c < d - c + δ)),
    eventually_gt_atTop 0] with K hK hK0
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK0
  have := (div_lt_iff₀ hK').1 hK
  linarith

open Chebyshev in
/-- Eventually `θ(dK) - θ(cK) ≥ (d - c - δ) K`. -/
lemma cell_lower (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ K : ℕ in atTop, (d - c - δ) * K ≤ θ (d * K) - θ (c * K) := by
  filter_upwards [(cell_tendsto c d hc hd).eventually (Ioi_mem_nhds (by linarith : d - c - δ < d - c)),
    eventually_gt_atTop 0] with K hK hK0
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK0
  have := (lt_div_iff₀ hK').1 hK
  linarith

lemma hof_le (K : ℕ) : (hof K : ℝ) ≤ Lim.lam * K := by
  unfold hof
  have := Nat.cast_div_le (α := ℝ) (m := 37 * K) (n := 40)
  rw [show Lim.lam = 37 / 40 by norm_num [Lim.lam]]
  push_cast at this
  linarith

lemma padicVal24_log_le (p : ℕ) [hp : Fact p.Prime] :
    (padicValNat p 24 : ℝ) * Real.log p ≤ if p ≤ 24 then Real.log 24 else 0 := by
  split_ifs with h
  · have hd : p ^ padicValNat p 24 ∣ 24 := pow_padicValNat_dvd
    have hle : ((p ^ padicValNat p 24 : ℕ) : ℝ) ≤ 24 := by exact_mod_cast Nat.le_of_dvd (by norm_num) hd
    have hpos : (0 : ℝ) < ((p ^ padicValNat p 24 : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hp.out.pos _
    have := Real.log_le_log hpos hle
    push_cast at this
    rwa [Real.log_pow] at this
  · have : ¬ p ∣ 24 := fun hd => h (Nat.le_of_dvd (by norm_num) hd)
    simp [padicValNat.eq_zero_of_not_dvd this]

lemma eventually_sqrt_le (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ K : ℕ in atTop, C * Real.sqrt (5 * K) ≤ δ * K := by
  set C' := max C 0
  have hlim := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (Real.sqrt 5 * (C' + 1) / δ)
  filter_upwards [hlim] with K hK
  simp only [Function.comp] at hK
  have hs : Real.sqrt (5 * K) = Real.sqrt 5 * Real.sqrt K := Real.sqrt_mul (by norm_num) _
  have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (Nat.cast_nonneg K)
  have h1 : Real.sqrt 5 * (C' + 1) ≤ δ * Real.sqrt K := by
    rw [div_le_iff₀ hδ] at hK; linarith
  have hC : C ≤ C' + 1 := by have := le_max_left C 0; linarith
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have h5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  rw [hs]
  calc C * (Real.sqrt 5 * Real.sqrt K) ≤ (C' + 1) * (Real.sqrt 5 * Real.sqrt K) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg h5 hsK)
    _ = (Real.sqrt 5 * (C' + 1)) * Real.sqrt K := by ring
    _ ≤ (δ * Real.sqrt K) * Real.sqrt K := mul_le_mul_of_nonneg_right h1 hsK
    _ = δ * K := by rw [mul_assoc, hKK]

/-! ### Step majorants -/

/-- Grid points of the uniform partition of `[a, b]` into `n` cells. -/
def cx (a b : ℝ) (n i : ℕ) : ℝ := a + (b - a) * i / n

/-- Supremum of `φ` over the closed `i`-th cell (intersected with `[a, b]`). -/
def cM (φ : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  sSup (φ '' (Set.Icc (cx a b n i) (cx a b n (i + 1)) ∩ Set.Icc a b))

/-- The step majorant of `φ + B`. -/
def cG (φ : ℝ → ℝ) (a b B : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ range n, (Set.Ioc (cx a b n i) (cx a b n (i + 1))).indicator (fun _ => cM φ a b n i + B) y

section cells
variable {a b : ℝ}

lemma cx_mono (hab : a ≤ b) (n : ℕ) {i j : ℕ} (hij : i ≤ j) : cx a b n i ≤ cx a b n j := by
  unfold cx
  have : (b - a) * i ≤ (b - a) * j :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by linarith)
  have := div_le_div_of_nonneg_right this (Nat.cast_nonneg n)
  linarith

lemma cx_zero (n : ℕ) : cx a b n 0 = a := by simp [cx]

lemma cx_self {n : ℕ} (hn : 0 < n) : cx a b n n = b := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [cx, mul_div_assoc, div_self this]

lemma cx_succ_sub {n : ℕ} (_hn : 0 < n) (i : ℕ) : cx a b n (i + 1) - cx a b n i = (b - a) / n := by
  unfold cx; push_cast; ring

lemma cx_ge (hab : a ≤ b) (n i : ℕ) : a ≤ cx a b n i := by
  have := cx_mono hab n (Nat.zero_le i); rwa [cx_zero] at this

lemma cx_le (hab : a ≤ b) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) : cx a b n i ≤ b := by
  have := cx_mono hab n hi; rwa [cx_self hn] at this

lemma cell_unique (hab : a ≤ b) {n i j : ℕ} {y : ℝ}
    (hi : y ∈ Set.Ioc (cx a b n i) (cx a b n (i + 1)))
    (hj : y ∈ Set.Ioc (cx a b n j) (cx a b n (j + 1))) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := cx_mono hab n (Nat.succ_le_of_lt h); linarith [hi.2, hj.1]
  · have := cx_mono hab n (Nat.succ_le_of_lt h); linarith [hj.2, hi.1]

lemma cell_exists (hab : a < b) {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : y ∈ Set.Ioc a b) :
    ∃ i < n, y ∈ Set.Ioc (cx a b n i) (cx a b n (i + 1)) := by
  have hw : 0 < b - a := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set t := (y - a) * n / (b - a) with ht
  have ht0 : 0 < t := by have := hy.1; apply div_pos (mul_pos (by linarith) hn') hw
  have htn : t ≤ n := by
    rw [ht, div_le_iff₀ hw]; nlinarith [hy.2]
  have hc1 : 1 ≤ ⌈t⌉₊ := Nat.one_le_iff_ne_zero.2 (by simpa using ht0)
  refine ⟨⌈t⌉₊ - 1, ?_, ?_, ?_⟩
  · have := Nat.ceil_le.2 htn; omega
  · have h1 := Nat.ceil_lt_add_one ht0.le
    have h2 : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by push_cast [Nat.cast_sub hc1]; ring
    unfold cx
    rw [h2]
    have h3 : ((⌈t⌉₊ : ℝ) - 1) < t := by linarith
    rw [ht, lt_div_iff₀ hw] at h3
    rw [add_comm, ← lt_sub_iff_add_lt, div_lt_iff₀ hn']
    linarith
  · have h1 := Nat.le_ceil t
    have h2 : ((⌈t⌉₊ - 1 + 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) := by rw [Nat.sub_add_cancel hc1]
    unfold cx
    rw [h2]
    rw [ht, div_le_iff₀ hw] at h1
    rw [add_comm, ← sub_le_iff_le_add, le_div_iff₀ hn']
    linarith

variable {φ : ℝ → ℝ} {B : ℝ}

lemma cM_bdd (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (n i : ℕ) :
    BddAbove (φ '' (Set.Icc (cx a b n i) (cx a b n (i + 1)) ∩ Set.Icc a b)) :=
  ⟨B, fun _ ⟨y, hy, hz⟩ => hz ▸ (le_abs_self _).trans (hB y hy.2)⟩

lemma cM_le (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (hB0 : 0 ≤ B) (n i : ℕ) : cM φ a b n i ≤ B :=
  Real.sSup_le (fun _ ⟨y, hy, hz⟩ => hz ▸ (le_abs_self _).trans (hB y hy.2)) hB0

lemma cM_ge (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (hB0 : 0 ≤ B) (n i : ℕ) : -B ≤ cM φ a b n i := by
  by_cases hne : (φ '' (Set.Icc (cx a b n i) (cx a b n (i + 1)) ∩ Set.Icc a b)).Nonempty
  · obtain ⟨z, y, hy, rfl⟩ := hne
    have h1 := le_csSup (cM_bdd hB n i) ⟨y, hy, rfl⟩
    have h2 := neg_abs_le (φ y)
    have h3 := hB y hy.2
    unfold cM; linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold cM; rw [hne, Real.sSup_empty]; linarith

lemma le_cM (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) {n i : ℕ} {y : ℝ}
    (hy : y ∈ Set.Icc (cx a b n i) (cx a b n (i + 1)) ∩ Set.Icc a b) : φ y ≤ cM φ a b n i :=
  le_csSup (cM_bdd hB n i) ⟨y, hy, rfl⟩

lemma cG_eval (hab : a < b) {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : y ∈ Set.Ioc a b) :
    ∃ i < n, y ∈ Set.Ioc (cx a b n i) (cx a b n (i + 1)) ∧ cG φ a b B n y = cM φ a b n i + B := by
  obtain ⟨i, hi, hyi⟩ := cell_exists hab hn hy
  refine ⟨i, hi, hyi, ?_⟩
  unfold cG
  rw [Finset.sum_eq_single_of_mem i (mem_range.2 hi), Set.indicator_of_mem hyi]
  intro j _ hji
  exact Set.indicator_of_notMem (fun hj => hji (cell_unique hab.le hj hyi)) _

lemma cG_bounds (hab : a < b) (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (hB0 : 0 ≤ B) {n : ℕ}
    (hn : 0 < n) {y : ℝ} (hy : y ∈ Set.Ioc a b) :
    φ y + B ≤ cG φ a b B n y ∧ 0 ≤ cG φ a b B n y ∧ cG φ a b B n y ≤ 2 * B := by
  obtain ⟨i, hi, hyi, heq⟩ := cG_eval (φ := φ) (B := B) hab hn hy
  rw [heq]
  have := le_cM hB ⟨Set.Ioc_subset_Icc_self hyi, Set.Ioc_subset_Icc_self hy⟩
  have := cM_le hB hB0 n i
  have := cM_ge hB hB0 n i
  refine ⟨by linarith, by linarith, by linarith⟩

lemma cG_measurable (n : ℕ) : Measurable (cG φ a b B n) :=
  Finset.measurable_sum _ fun _ _ => measurable_const.indicator measurableSet_Ioc

lemma cG_tendsto (hab : a < b) (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) {y : ℝ}
    (hy : y ∈ Set.Ioo a b) (hc : ContinuousAt φ y) :
    Tendsto (fun n => cG φ a b B n y) atTop (𝓝 (φ y + B)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.1 hc (η / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hN0 : (0 : ℝ) < N := lt_trans (div_pos (by linarith) hδ) hN
  refine ⟨N, fun n hn => ?_⟩
  have hn0 : 0 < n := by
    have : 0 < N := by exact_mod_cast hN0
    omega
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨i, hi, hyi, heq⟩ := cG_eval (φ := φ) (B := B) hab hn0 (Set.Ioo_subset_Ioc_self hy)
  rw [heq, Real.dist_eq]
  have hlow := le_cM hB ⟨Set.Ioc_subset_Icc_self hyi, Set.Ioo_subset_Icc_self hy⟩
  have hwidth : cx a b n (i + 1) - cx a b n i < δ := by
    rw [cx_succ_sub hn0]
    rw [div_lt_iff₀ hδ] at hN
    rw [div_lt_iff₀ (by exact_mod_cast hn0)]
    nlinarith
  have hup : cM φ a b n i ≤ φ y + η / 2 := by
    unfold cM
    have hne : (Set.Icc (cx a b n i) (cx a b n (i + 1)) ∩ Set.Icc a b).Nonempty :=
      ⟨y, Set.Ioc_subset_Icc_self hyi, Set.Ioo_subset_Icc_self hy⟩
    apply csSup_le (hne.image φ)
    rintro _ ⟨u, hu, rfl⟩
    have hd : dist u y < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1.1, hu.1.2, hyi.1, hyi.2]
    have := hδφ hd
    rw [Real.dist_eq, abs_lt] at this
    linarith
  rw [abs_lt]; constructor <;> linarith

lemma integral_cG (hab : a < b) {n : ℕ} (hn : 0 < n) :
    ∫ y in a..b, cG φ a b B n y = ∑ i ∈ range n, (cM φ a b n i + B) * ((b - a) / n) := by
  unfold cG
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i + 1 ≤ n := mem_range.1 hi
    have h1 := cx_ge hab.le n i
    have h2 := cx_le hab.le hn hi'
    have h3 := cx_mono hab.le n (Nat.le_succ i)
    rw [intervalIntegral.integral_of_le hab.le, integral_indicator_const _ measurableSet_Ioc,
      Measure.real, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc h1 h2), Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), cx_succ_sub hn, smul_eq_mul, mul_comm]
  · intro i _
    exact (intervalIntegrable_iff.2 ((integrableOn_const (by
      rw [Set.uIoc_of_le hab.le, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).indicator
      measurableSet_Ioc))

end cells

section dct
variable {a b : ℝ} {φ : ℝ → ℝ} {B : ℝ} {D : Set ℝ}

lemma ae_cG_tendsto (hab : a < b) (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (hD : D.Countable)
    (hcont : ∀ y ∈ Set.Ioo a b, y ∉ D → ContinuousAt φ y) :
    ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Set.uIoc a b →
      Tendsto (fun n => cG φ a b B n y) atTop (𝓝 (φ y + B)) := by
  filter_upwards [(hD.union (Set.countable_singleton b)).ae_notMem volume] with y hy hyab
  rw [Set.uIoc_of_le hab.le] at hyab
  have hyb : y ≠ b := fun h => hy (Or.inr h)
  have hyD : y ∉ D := fun h => hy (Or.inl h)
  have hyo : y ∈ Set.Ioo a b := ⟨hyab.1, lt_of_le_of_ne hyab.2 hyb⟩
  exact cG_tendsto hab hB hyo (hcont y hyo hyD)

lemma phi_intervalIntegrable (hab : a < b) (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (hD : D.Countable)
    (hcont : ∀ y ∈ Set.Ioo a b, y ∉ D → ContinuousAt φ y) : IntervalIntegrable φ volume a b := by
  have hmeas : AEStronglyMeasurable φ (volume.restrict (Set.uIoc a b)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n y => cG φ a b B n y - B)
    · intro n; exact ((cG_measurable n).sub measurable_const).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [ae_cG_tendsto hab hB hD hcont] with y hy hyab
      simpa using (hy hyab).sub_const B
  rw [intervalIntegrable_iff]
  refine Integrable.mono' (g := fun _ => B) (integrableOn_const (by
      rw [Set.uIoc_of_le hab.le, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) hmeas ?_
  rw [ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun y hy => ?_
  rw [Set.uIoc_of_le hab.le] at hy
  exact hB y (Set.Ioc_subset_Icc_self hy)

lemma integral_cG_tendsto (hab : a < b) (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B) (hB0 : 0 ≤ B)
    (hD : D.Countable) (hcont : ∀ y ∈ Set.Ioo a b, y ∉ D → ContinuousAt φ y) :
    Tendsto (fun n => ∫ y in a..b, cG φ a b B n y) atTop (𝓝 (∫ y in a..b, (φ y + B))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B)
  · exact Filter.Eventually.of_forall fun n => (cG_measurable n).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with n hn
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Set.uIoc_of_le hab.le] at hy
    obtain ⟨-, h1, h2⟩ := cG_bounds (φ := φ) hab hB hB0 hn hy
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  · exact intervalIntegrable_const
  · exact ae_cG_tendsto hab hB hD hcont

end dct

/-- Change of variables `x = 1/y`. -/
lemma integral_inv_subst (M : ℝ) (hM : 3 ≤ M) (f : ℝ → ℝ) :
    ∫ y in M⁻¹..(3 : ℝ)⁻¹, y * f y⁻¹ = ∫ x in (3 : ℝ)..M, f x / x ^ 3 := by
  have hM0 : (0 : ℝ) < M := by linarith
  rw [intervalIntegral.integral_of_le ((inv_le_inv₀ hM0 (by norm_num)).2 hM),
    intervalIntegral.integral_of_le hM]
  have himg : Inv.inv '' Set.Ico (3 : ℝ) M = Set.Ioc M⁻¹ 3⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      have hx0 : (0 : ℝ) < x := by linarith
      exact ⟨(inv_lt_inv₀ hM0 hx0).2 hx2, (inv_le_inv₀ hx0 (by norm_num)).2 hx1⟩
    · rintro ⟨hy1, hy2⟩
      have hy0 : 0 < y := lt_trans (inv_pos.2 hM0) hy1
      refine ⟨y⁻¹, ⟨?_, ?_⟩, inv_inv y⟩
      · exact (le_inv_comm₀ (by norm_num : (0 : ℝ) < 3) hy0).2 hy2
      · exact (inv_lt_comm₀ hM0 hy0).1 hy1
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ico
    (fun x hx => (hasDerivAt_inv (by linarith [hx.1] : x ≠ 0)).hasDerivWithinAt)
    inv_injective.injOn]
  rw [setIntegral_congr_fun measurableSet_Ico (g := fun x => f x / x ^ 3)]
  · rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  · intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    simp only [smul_eq_mul, inv_inv]
    rw [abs_neg, abs_of_pos (by positivity)]
    field_simp

end PS

open PS in
/-- Small primes `p ≤ K/M`: the contribution of `-L_p` is `6λK²/M + o(K²)`. -/
theorem small_prime_sum_bound (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      ∑ p ∈ (range (K + 1)).filter (fun p => p.Prime ∧ p * M ≤ K),
          ((6 * hof K * Nat.log p (5 * K) + hof K * padicValNat p 24 : ℕ) : ℝ) * Real.log p
        ≤ (6 * Lim.lam / M + ε) * (K : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set δ := ε / 13 with hδdef
  have hδ : 0 < δ := by positivity
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.2 hM'.le
  filter_upwards [cell_upper 0 (M : ℝ)⁻¹ le_rfl hMinv δ hδ, eventually_sqrt_le C δ hδ,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (25 * Real.log 24 / δ),
    eventually_gt_atTop 0] with K hθ hsq h24 hK0
  have hK : (0 : ℝ) < K := by exact_mod_cast hK0
  simp only [zero_mul, Chebyshev.theta_zero, sub_zero] at hθ
  set s := (range (K + 1)).filter (fun p => p.Prime ∧ p * M ≤ K) with hs
  -- the three pieces
  have hsplit : ∀ p ∈ s, ((6 * hof K * Nat.log p (5 * K) + hof K * padicValNat p 24 : ℕ) : ℝ) *
      Real.log p = 6 * hof K * (Real.log p + ((Nat.log p (5 * K) : ℝ) - 1) * Real.log p) +
        hof K * ((padicValNat p 24 : ℝ) * Real.log p) := by
    intro p _; push_cast; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  -- θ(K/M)
  have hθs : ∑ p ∈ s, Real.log p = Chebyshev.theta ((M : ℝ)⁻¹ * K) := by
    rw [theta_eq_filter (K + 1) (mul_nonneg hMinv hK.le) ?_]
    · apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [hs, mem_filter, mem_range]
      rw [inv_mul_eq_div, le_div_iff₀ hM']
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by exact_mod_cast h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by exact_mod_cast h3⟩
    · have : (M : ℝ)⁻¹ * K ≤ K := by
        rw [inv_mul_le_iff₀ hM']; nlinarith [(by exact_mod_cast hM : (1 : ℝ) ≤ M)]
      push_cast; linarith
  -- ψ - θ
  have hψ : ∑ p ∈ s, ((Nat.log p (5 * K) : ℝ) - 1) * Real.log p ≤ C * Real.sqrt (5 * K) := by
    have h1 : ∑ p ∈ s, ((Nat.log p (5 * K) : ℝ) - 1) * Real.log p ≤
        ∑ p ∈ Nat.primesLE (5 * K), ((Nat.log p (5 * K) : ℝ) - 1) * Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [hs, mem_filter, mem_range] at hp
        rw [Nat.mem_primesLE]
        exact ⟨by omega, hp.2.1⟩
      · intro p hp _
        rw [Nat.mem_primesLE] at hp
        have : 1 ≤ Nat.log p (5 * K) := Nat.log_pos hp.2.one_lt hp.1
        have : (1 : ℝ) ≤ Nat.log p (5 * K) := by exact_mod_cast this
        exact mul_nonneg (by linarith) (Real.log_natCast_nonneg p)
    have h2 := hC ((5 * K : ℕ) : ℝ)
    rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
      ← Finset.sum_sub_distrib] at h2
    push_cast at h2
    refine h1.trans (le_of_eq_of_le (Finset.sum_congr rfl fun p _ => by ring) h2)
  -- 24
  have h24s : ∑ p ∈ s, (padicValNat p 24 : ℝ) * Real.log p ≤ 25 * Real.log 24 := by
    calc ∑ p ∈ s, (padicValNat p 24 : ℝ) * Real.log p
        ≤ ∑ p ∈ s, (if p ≤ 24 then Real.log 24 else 0) := by
          apply Finset.sum_le_sum
          intro p hp
          simp only [hs, mem_filter] at hp
          have := Fact.mk hp.2.1
          exact padicVal24_log_le p
      _ = ∑ p ∈ s.filter (· ≤ 24), Real.log 24 := (Finset.sum_filter _ _).symm
      _ ≤ ∑ p ∈ range 25, Real.log 24 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; simp only [mem_filter] at hp; simp only [mem_range]; omega
          · intro _ _ _; exact Real.log_nonneg (by norm_num)
      _ = 25 * Real.log 24 := by simp
  have h24' : 25 * Real.log 24 ≤ δ * K := by rw [div_le_iff₀ hδ] at h24; linarith
  have hh := hof_le K
  have hh0 : (0 : ℝ) ≤ hof K := Nat.cast_nonneg _
  have hlam : Lim.lam = 37 / 40 := by norm_num [Lim.lam]
  have hA : ∑ p ∈ s, Real.log p + ∑ p ∈ s, ((Nat.log p (5 * K) : ℝ) - 1) * Real.log p ≤
      ((M : ℝ)⁻¹ + 2 * δ) * K := by
    rw [hθs]; nlinarith
  have hA0 : 0 ≤ ((M : ℝ)⁻¹ + 2 * δ) * K := by positivity
  have e1 := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 6 * hof K)
  have e2 := mul_le_mul_of_nonneg_right hh hA0
  have e3 := mul_le_mul_of_nonneg_left (h24s.trans h24') hh0
  have e4 := mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ δ * K)
  have hMM : (M : ℝ)⁻¹ * M = 1 := inv_mul_cancel₀ hM'.ne'
  rw [hlam] at e2 e4 ⊢
  have : 6 * (37 / 40 : ℝ) / M = 6 * (37 / 40) * (M : ℝ)⁻¹ := by ring
  rw [this]
  nlinarith

/-- Chebyshev upper bound `θ(n) ≤ n log 4` in sum form (for O(1)-error bookkeeping). -/
theorem sum_log_primes_le (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  rw [PS.theta_eq_filter (n + 1) (Nat.cast_nonneg n) (by push_cast; linarith)] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by exact_mod_cast Nat.lt_succ_iff.1 h1⟩
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩

end Zeta5

namespace Zeta5

open PS in
/-- Outer range, variable y = p/K. -/
theorem outer_prime_sum_limsup (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (φ : ℝ → ℝ) (B : ℝ)
    (hB : ∀ y ∈ Set.Icc a b, |φ y| ≤ B)
    (D : Set ℝ) (hD : D.Countable)
    (hcont : ∀ y ∈ Set.Ioo a b, y ∉ D → ContinuousAt φ y)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      ∑ p ∈ (range (⌊b * K⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ a * K < p ∧ (p : ℝ) ≤ b * K),
          φ ((p : ℝ) / K) * Real.log p
        ≤ ((∫ y in a..b, φ y) + ε) * K := by
  rcases hab.eq_or_lt with rfl | hab'
  · filter_upwards with K
    rw [Finset.sum_eq_zero, intervalIntegral.integral_same, zero_add]
    · positivity
    · intro p hp; simp only [mem_filter] at hp; linarith [hp.2.2.1, hp.2.2.2]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  have hφi := phi_intervalIntegrable hab' hB hD hcont
  have hlim := integral_cG_tendsto hab' hB hB0 hD hcont
  rw [intervalIntegral.integral_add hφi intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hlim
  obtain ⟨n, hn1, hn0⟩ := ((hlim.eventually (Iio_mem_nhds (by linarith :
    (∫ y in a..b, φ y) + (b - a) * B < (∫ y in a..b, φ y) + (b - a) * B + ε / 2))).and
    (eventually_gt_atTop 0)).exists
  replace hn1 : _ < _ := hn1
  rw [integral_cG hab' hn0] at hn1
  set IG := ∑ i ∈ range n, (cM φ a b n i + B) * ((b - a) / n) with hIG
  set T := ∑ i ∈ range n, (cM φ a b n i + B) with hTdef
  set δ := ε / (2 * ((2 * n + 1) * B + 1)) with hδ
  have hden : 0 < 2 * ((2 * (n : ℝ) + 1) * B + 1) := by positivity
  have hδ0 : 0 < δ := div_pos hε hden
  have hδB : (2 * n + 1) * B * δ ≤ ε / 2 := by
    have : δ * (2 * ((2 * n + 1) * B + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  have hcells : ∀ᶠ K : ℕ in atTop, ∀ i ∈ range n,
      Chebyshev.theta (cx a b n (i + 1) * K) - Chebyshev.theta (cx a b n i * K) ≤
        ((b - a) / n + δ) * K := by
    rw [eventually_all_finset]
    intro i _
    have := cell_upper (cx a b n i) (cx a b n (i + 1)) (ha.le.trans (cx_ge hab n i))
      (ha.le.trans (cx_ge hab n (i + 1))) δ hδ0
    rwa [cx_succ_sub hn0] at this
  filter_upwards [hcells, cell_lower a b ha.le (ha.le.trans hab) δ hδ0, eventually_gt_atTop 0]
    with K hc hl hK0
  have hK : (0 : ℝ) < K := by exact_mod_cast hK0
  set N := ⌊b * K⌋₊ + 1 with hN
  have hbN : b * K < N := by rw [hN]; push_cast; exact Nat.lt_floor_add_one _
  set s := (range N).filter (fun p : ℕ => p.Prime ∧ a * K < p ∧ (p : ℝ) ≤ b * K) with hs
  have htot : ∑ p ∈ s, Real.log p = Chebyshev.theta (b * K) - Chebyshev.theta (a * K) :=
    sum_cell N (by positivity) (by nlinarith) hbN
  have hmem : ∀ p ∈ s, (p : ℝ) / K ∈ Set.Ioc a b := by
    intro p hp
    simp only [hs, mem_filter] at hp
    exact ⟨(lt_div_iff₀ hK).2 hp.2.2.1, (div_le_iff₀ hK).2 hp.2.2.2⟩
  have hmaj : ∑ p ∈ s, (φ ((p : ℝ) / K) + B) * Real.log p ≤
      ∑ p ∈ s, cG φ a b B n ((p : ℝ) / K) * Real.log p :=
    Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
      (cG_bounds hab' hB hB0 hn0 (hmem p hp)).1 (Real.log_natCast_nonneg p)
  have hcG : ∑ p ∈ s, cG φ a b B n ((p : ℝ) / K) * Real.log p ≤
      ∑ i ∈ range n, (cM φ a b n i + B) * (((b - a) / n + δ) * K) := by
    unfold cG
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i + 1 ≤ n := mem_range.1 hi
    have hsub : ∑ p ∈ s, (Set.Ioc (cx a b n i) (cx a b n (i + 1))).indicator
        (fun _ => cM φ a b n i + B) ((p : ℝ) / K) * Real.log p =
        (cM φ a b n i + B) *
          ∑ p ∈ s.filter (fun p : ℕ => (p : ℝ) / K ∈ Set.Ioc (cx a b n i) (cx a b n (i + 1))),
            Real.log p := by
      rw [Finset.mul_sum, Finset.sum_filter (s := s)
        (p := fun p : ℕ => (p : ℝ) / K ∈ Set.Ioc (cx a b n i) (cx a b n (i + 1)))]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Set.indicator_apply]
      split_ifs <;> ring
    rw [hsub]
    apply mul_le_mul_of_nonneg_left _ (by linarith [cM_ge hB hB0 n i])
    have h1 := cx_ge hab n i
    have h2 := cx_le hab hn0 hi'
    have h3 := cx_mono hab n (Nat.le_succ i)
    calc ∑ p ∈ s.filter (fun p : ℕ => (p : ℝ) / K ∈ Set.Ioc (cx a b n i) (cx a b n (i + 1))),
            Real.log p
        ≤ ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ cx a b n i * K < p ∧
            (p : ℝ) ≤ cx a b n (i + 1) * K), Real.log p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [hs, mem_filter] at hp ⊢
            obtain ⟨⟨hpN, hpr, -⟩, hp1, hp2⟩ := hp
            exact ⟨hpN, hpr, (lt_div_iff₀ hK).1 hp1, (div_le_iff₀ hK).1 hp2⟩
          · intro p _ _; exact Real.log_natCast_nonneg p
      _ = Chebyshev.theta (cx a b n (i + 1) * K) - Chebyshev.theta (cx a b n i * K) :=
          sum_cell N (by nlinarith) (by nlinarith) (by nlinarith)
      _ ≤ ((b - a) / n + δ) * K := hc i hi
  have hsplit : ∑ p ∈ s, φ ((p : ℝ) / K) * Real.log p =
      ∑ p ∈ s, (φ ((p : ℝ) / K) + B) * Real.log p - B * ∑ p ∈ s, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hsplit2 : ∑ i ∈ range n, (cM φ a b n i + B) * (((b - a) / n + δ) * K) =
      IG * K + δ * K * T := by
    rw [hIG, hTdef, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hT : T ≤ n * (2 * B) := by
    calc T ≤ ∑ i ∈ range n, 2 * B :=
          Finset.sum_le_sum fun i _ => by linarith [cM_le hB hB0 n i]
      _ = n * (2 * B) := by simp
  rw [hsplit, htot]
  have m1 := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ δ * K)
  have m2 := mul_le_mul_of_nonneg_left hl hB0
  have m3 := mul_le_mul_of_nonneg_right hn1.le hK.le
  have m4 := mul_le_mul_of_nonneg_right hδB hK.le
  nlinarith [hmaj, hcG, hsplit2]

end Zeta5

namespace Zeta5

open PS in
/-- Inner range, variable x = K/p. -/
theorem inner_prime_sum_limsup (M : ℕ) (hM : 3 < M) (f : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (3 : ℝ) M, |f x| ≤ B)
    (D : Set ℝ) (hD : D.Countable)
    (hcont : ∀ x ∈ Set.Ioo (3 : ℝ) M, x ∉ D → ContinuousAt f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      ∑ p ∈ (range (K + 1)).filter (fun p => p.Prime ∧ K < p * M ∧ 3 * p ≤ K),
          (p : ℝ) * f ((K : ℝ) / p) * Real.log p
        ≤ ((∫ x in (3 : ℝ)..M, f x / x ^ 3) + ε) * (K : ℝ) ^ 2 := by
  have hM' : (3 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 3 ⟨le_rfl, hM'.le⟩)
  have ho := outer_prime_sum_limsup (M : ℝ)⁻¹ 3⁻¹ (inv_pos.2 hM0)
    ((inv_le_inv₀ hM0 (by norm_num)).2 hM'.le) (fun y => y * f y⁻¹) B ?_ (Inv.inv '' D)
    (hD.image _) ?_ ε hε
  · filter_upwards [ho, eventually_gt_atTop 0] with K hK hK0
    rw [integral_inv_subst M hM'.le] at hK
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
    have heq : ∑ p ∈ (range (K + 1)).filter (fun p => p.Prime ∧ K < p * M ∧ 3 * p ≤ K),
          (p : ℝ) * f ((K : ℝ) / p) * Real.log p =
        K * ∑ p ∈ (range (⌊(3 : ℝ)⁻¹ * K⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ (M : ℝ)⁻¹ * K < p ∧ (p : ℝ) ≤ 3⁻¹ * K),
          (p : ℝ) / K * f ((p : ℝ) / K)⁻¹ * Real.log p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr
      · ext p
        simp only [mem_filter, mem_range]
        rw [inv_mul_lt_iff₀ hM0]
        constructor
        · rintro ⟨-, hpr, h1, h2⟩
          have h1' : (K : ℝ) < M * p := by rw [mul_comm]; exact_mod_cast h1
          have h2' : (3 : ℝ) * p ≤ K := by exact_mod_cast h2
          have hle : (p : ℝ) ≤ 3⁻¹ * K := by linarith
          exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hpr, h1', hle⟩
        · rintro ⟨-, hpr, h1, h2⟩
          have h1' : K < p * M := by
            have : (K : ℝ) < p * M := by linarith
            exact_mod_cast this
          have h2' : 3 * p ≤ K := by
            have : (3 : ℝ) * p ≤ K := by linarith
            exact_mod_cast this
          exact ⟨by omega, hpr, h1', h2'⟩
      · intro p hp
        simp only [mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        rw [inv_div]
        field_simp
    rw [heq]
    calc (K : ℝ) * _ ≤ K * (((∫ x in (3 : ℝ)..M, f x / x ^ 3) + ε) * K) :=
          mul_le_mul_of_nonneg_left hK hKr.le
      _ = _ := by ring
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (inv_pos.2 hM0) hy.1
    have h1 : 3 ≤ y⁻¹ := (le_inv_comm₀ (by norm_num : (0 : ℝ) < 3) hy0).2 hy.2
    have h2 : y⁻¹ ≤ M := (inv_le_comm₀ hM0 hy0).1 hy.1
    have hy1 : y ≤ 1 := hy.2.trans (by norm_num)
    rw [abs_mul, abs_of_pos hy0]
    calc y * |f y⁻¹| ≤ 1 * B :=
          mul_le_mul hy1 (hB _ ⟨h1, h2⟩) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  · intro y hy hyD
    have hy0 : 0 < y := lt_trans (inv_pos.2 hM0) hy.1
    have h1 : 3 < y⁻¹ := (lt_inv_comm₀ (by norm_num : (0 : ℝ) < 3) hy0).2 hy.2
    have h2 : y⁻¹ < M := (inv_lt_comm₀ hM0 hy0).1 hy.1
    have hnD : y⁻¹ ∉ D := fun h => hyD ⟨y⁻¹, h, inv_inv y⟩
    exact continuousAt_id.mul ((hcont y⁻¹ ⟨h1, h2⟩ hnD).comp (continuousAt_inv₀ hy0.ne'))

end Zeta5
