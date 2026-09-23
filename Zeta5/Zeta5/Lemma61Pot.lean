import Zeta5.Lemma61

/-!
# Lemma 6.1, (6.2): certified rational enclosures and the potential inequality

Computable rational upper/lower bounds for `√`, `log`, `arctan`, with soundness lemmas; the
potential inequality `2U^ρ(t) - V(t) < -6645002/10⁶` is then checked on a rational partition of
`[0, 2]` by kernel evaluation (`decide +kernel`), and on `[2, ∞)` by hand.
-/

open Finset MeasureTheory Set

noncomputable section

namespace Zeta5

namespace Pot

/-! ## Rounding -/

def P : ℕ := 40

def rup (q : ℚ) : ℚ := (⌈q * 2 ^ P⌉ : ℚ) / 2 ^ P
def rdn (q : ℚ) : ℚ := (⌊q * 2 ^ P⌋ : ℚ) / 2 ^ P

lemma le_rup (q : ℚ) : q ≤ rup q := by
  unfold rup; rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _

lemma rdn_le (q : ℚ) : rdn q ≤ q := by
  unfold rdn; rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _

/-! ## Square roots -/

def sqU (x : ℚ) : ℚ :=
  let s : ℚ := ((Nat.sqrt ⌈x * 2 ^ (2 * P)⌉.toNat + 1 : ℕ) : ℚ) / 2 ^ P
  if x ≤ s * s then s else x + 1

def sqL (x : ℚ) : ℚ :=
  let s : ℚ := ((Nat.sqrt ⌊x * 2 ^ (2 * P)⌋.toNat : ℕ) : ℚ) / 2 ^ P
  if s * s ≤ x then s else 0

lemma sqU_nonneg (x : ℚ) (hx : 0 ≤ x) : 0 ≤ sqU x := by
  unfold sqU; dsimp only; split_ifs <;> positivity

lemma sqrt_le_sqU (x : ℚ) (hx : 0 ≤ x) : Real.sqrt x ≤ (sqU x : ℝ) := by
  unfold sqU
  dsimp only
  split_ifs with h
  · rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast (show x ≤ _ by rw [← sq] at h; exact h)
  · rw [Real.sqrt_le_left (by positivity)]
    have : (x : ℝ) ≤ ((x : ℝ) + 1) ^ 2 := by nlinarith [(Rat.cast_nonneg.2 hx : (0 : ℝ) ≤ x)]
    push_cast; exact this

lemma sqL_nonneg (x : ℚ) : 0 ≤ sqL x := by
  unfold sqL; dsimp only; split_ifs <;> positivity

lemma sqL_le_sqrt (x : ℚ) : (sqL x : ℝ) ≤ Real.sqrt x := by
  unfold sqL
  dsimp only
  split_ifs with h
  · apply Real.le_sqrt_of_sq_le
    rw [sq]; exact_mod_cast h
  · push_cast; exact Real.sqrt_nonneg _

/-! ## Logarithms -/

/-- Enclosure of `log 2` (from `log2_enc`). -/
def L2lo : ℚ := 6931471805599453094172 / 10 ^ 22 - 1 / 10 ^ 21
def L2hi : ℚ := 6931471805599453094172 / 10 ^ 22 + 1 / 10 ^ 21

lemma log2_bounds : (L2lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ L2hi := by
  obtain ⟨h1, h2⟩ := L61.log2_enc
  unfold L2lo L2hi; push_cast
  constructor <;> linarith

def NT : ℕ := 14

def atSQ (z : ℚ) (m : ℕ) : ℚ := ∑ k ∈ range m, 2 * (1 / (2 * (k : ℚ) + 1)) * z ^ (2 * k + 1)

lemma atSQ_cast (z : ℚ) (m : ℕ) : ((atSQ z m : ℚ) : ℝ) = L61.atS z m := by
  unfold atSQ L61.atS; push_cast; rfl

/-- `log((1+z)/(1-z))` is monotone in `z ∈ [0, 1)`. -/
lemma ratio_mono {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w < 1) :
    (1 + z) / (1 - z) ≤ (1 + w) / (1 - w) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma ratio_eq (y : ℝ) (hy : 0 < y) : (1 + (y - 1) / (y + 1)) / (1 - (y - 1) / (y + 1)) = y := by
  field_simp; ring

/-- Upper bound for `log y`, precise on `[1, 2)`; valid for all `y > 0`. -/
def lnU1 (y : ℚ) : ℚ :=
  let z := rup ((y - 1) / (y + 1))
  if 0 ≤ (y - 1) / (y + 1) ∧ z < 1 then
    rup (atSQ z NT + 2 * z ^ (2 * NT + 1) / ((2 * NT + 1) * (1 - z ^ 2)))
  else y - 1

def lnL1 (y : ℚ) : ℚ :=
  let z := rdn ((y - 1) / (y + 1))
  if 0 ≤ z ∧ (y - 1) / (y + 1) < 1 then rdn (atSQ z NT) else 1 - 1 / y

lemma log_le_lnU1 (y : ℚ) (hy : 0 < y) : Real.log y ≤ lnU1 y := by
  unfold lnU1
  dsimp only
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    set z0 := (y - 1) / (y + 1)
    set z := rup z0
    have hz0 : (0 : ℝ) ≤ z0 := by exact_mod_cast h0
    have hzz : (z0 : ℝ) ≤ z := by exact_mod_cast le_rup z0
    have hz1 : (z : ℝ) < 1 := by exact_mod_cast h1
    have hyr : (0 : ℝ) < y := by exact_mod_cast hy
    have hb := (L61.log_series_bounds z (hz0.trans hzz) hz1 NT).2
    have e : (z0 : ℝ) = ((y : ℝ) - 1) / (y + 1) := by simp [z0]
    calc Real.log y = Real.log ((1 + (z0 : ℝ)) / (1 - z0)) := by rw [e, ratio_eq _ hyr]
      _ ≤ Real.log ((1 + (z : ℝ)) / (1 - z)) :=
          Real.log_le_log (by have : (z0 : ℝ) < 1 := hzz.trans_lt hz1
                              apply div_pos <;> linarith) (ratio_mono hz0 hzz hz1)
      _ ≤ _ := hb
      _ ≤ _ := by
          have := le_rup (atSQ z NT + 2 * z ^ (2 * NT + 1) / ((2 * NT + 1) * (1 - z ^ 2)))
          have hc : ((atSQ z NT + 2 * z ^ (2 * NT + 1) / ((2 * NT + 1) * (1 - z ^ 2)) : ℚ) : ℝ) =
              L61.atS z NT + 2 * (z : ℝ) ^ (2 * NT + 1) / ((2 * NT + 1) * (1 - (z : ℝ) ^ 2)) := by
            push_cast [atSQ_cast]; ring
          rw [← hc]; exact_mod_cast this
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < y by exact_mod_cast hy)
    push_cast; exact this

lemma lnL1_le_log (y : ℚ) (hy : 0 < y) : (lnL1 y : ℝ) ≤ Real.log y := by
  unfold lnL1
  dsimp only
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    set z0 := (y - 1) / (y + 1)
    set z := rdn z0
    have hz0 : (0 : ℝ) ≤ z := by exact_mod_cast h0
    have hzz : (z : ℝ) ≤ z0 := by exact_mod_cast rdn_le z0
    have hz1 : (z0 : ℝ) < 1 := by exact_mod_cast h1
    have hyr : (0 : ℝ) < y := by exact_mod_cast hy
    have hb := (L61.log_series_bounds z hz0 (hzz.trans_lt hz1) NT).1
    have e : (z0 : ℝ) = ((y : ℝ) - 1) / (y + 1) := by simp [z0]
    calc ((rdn (atSQ z NT) : ℚ) : ℝ) ≤ ((atSQ z NT : ℚ) : ℝ) := by exact_mod_cast rdn_le _
      _ = L61.atS z NT := atSQ_cast _ _
      _ ≤ Real.log ((1 + (z : ℝ)) / (1 - z)) := hb
      _ ≤ Real.log ((1 + (z0 : ℝ)) / (1 - z0)) :=
          Real.log_le_log (by apply div_pos <;> linarith) (ratio_mono hz0 hzz hz1)
      _ = Real.log y := by rw [e, ratio_eq _ hyr]
  · have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < y by exact_mod_cast hy)
    push_cast; simpa [one_div] using this

/-- Range reduction by powers of two. -/
def lnUp (y : ℚ) : ℚ :=
  let k := Nat.log2 ⌊y⌋.toNat
  lnU1 (y / 2 ^ k) + k * L2hi

def lnLp (y : ℚ) : ℚ :=
  let k := Nat.log2 ⌊y⌋.toNat
  lnL1 (y / 2 ^ k) + k * L2lo

lemma log_split (y : ℚ) (hy : 0 < y) (k : ℕ) :
    Real.log y = Real.log ((y / 2 ^ k : ℚ) : ℝ) + k * Real.log 2 := by
  push_cast
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]; ring

lemma log_le_lnUp (y : ℚ) (hy : 0 < y) : Real.log y ≤ lnUp y := by
  unfold lnUp
  rw [log_split y hy (Nat.log2 ⌊y⌋.toNat)]
  push_cast
  have h1 := log_le_lnU1 (y / 2 ^ Nat.log2 ⌊y⌋.toNat) (by positivity)
  have h2 := log2_bounds.2
  have hk : (0 : ℝ) ≤ (Nat.log2 ⌊y⌋.toNat : ℝ) := Nat.cast_nonneg _
  push_cast at h1
  nlinarith

lemma lnLp_le_log (y : ℚ) (hy : 0 < y) : (lnLp y : ℝ) ≤ Real.log y := by
  unfold lnLp
  rw [log_split y hy (Nat.log2 ⌊y⌋.toNat)]
  push_cast
  have h1 := lnL1_le_log (y / 2 ^ Nat.log2 ⌊y⌋.toNat) (by positivity)
  have h2 := log2_bounds.1
  have hk : (0 : ℝ) ≤ (Nat.log2 ⌊y⌋.toNat : ℝ) := Nat.cast_nonneg _
  push_cast at h1
  nlinarith

/-- Bounds for `log y`, `y > 0` (for `y < 1` via `log y = -log(1/y)`). -/
def lnU (y : ℚ) : ℚ := if 1 ≤ y then lnUp y else -lnLp (1 / y)
def lnL (y : ℚ) : ℚ := if 1 ≤ y then lnLp y else -lnUp (1 / y)

lemma log_le_lnU (y : ℚ) (hy : 0 < y) : Real.log y ≤ lnU y := by
  unfold lnU
  split_ifs
  · exact log_le_lnUp y hy
  · have := lnLp_le_log (1 / y) (by positivity)
    have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Rat.cast_div, Rat.cast_one, Real.log_div one_ne_zero hy0, Real.log_one] at this
    rw [Rat.cast_neg]
    linarith

lemma lnL_le_log (y : ℚ) (hy : 0 < y) : (lnL y : ℝ) ≤ Real.log y := by
  unfold lnL
  split_ifs
  · exact lnLp_le_log y hy
  · have := log_le_lnUp (1 / y) (by positivity)
    have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Rat.cast_div, Rat.cast_one, Real.log_div one_ne_zero hy0, Real.log_one] at this
    rw [Rat.cast_neg]
    linarith


/-! ## Arctangents -/

def atSer (x : ℚ) (m : ℕ) : ℚ := ∑ i ∈ range m, (-1) ^ i * (x ^ (2 * i + 1) / (2 * (i : ℚ) + 1))

lemma arctan_alt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑ i ∈ range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / (2 * (i : ℝ) + 1))) ≤ Real.arctan x ∧
      Real.arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  set f : ℕ → ℝ := fun i => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) with hf
  have hs' : HasSum (fun i => (-1) ^ i * f i) (Real.arctan x) := by
    convert hs using 1; funext i; simp only [hf]; push_cast; ring
  have ht := hs'.tendsto_sum_nat
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le fun n => ?_
    simp only [hf]
    have h1 : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
      pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have h2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ (by positivity) h2]
    push_cast
    nlinarith [pow_nonneg hx0 (2 * (n + 1) + 1), pow_nonneg hx0 (2 * n + 1)]
  exact ⟨hanti.alternating_series_le_tendsto ht k, hanti.tendsto_le_alternating_series ht k⟩

lemma atSer_cast (x : ℚ) (m : ℕ) : ((atSer x m : ℚ) : ℝ) =
    ∑ i ∈ range m, (-1) ^ i * ((x : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
  unfold atSer; push_cast; rfl

/-- `arctan` bounds for `0 ≤ x`, precise for `x ≤ 1/2`. -/
def atU0 (x : ℚ) : ℚ :=
  if 0 ≤ x ∧ rup x < 1 then rup (atSer (rup x) 13) else x

def atL0 (x : ℚ) : ℚ :=
  if 0 ≤ rdn x ∧ x < 1 then rdn (atSer (rdn x) 12) else 0

lemma arctan_le_atU0 (x : ℚ) (hx : 0 ≤ x) : Real.arctan x ≤ atU0 x := by
  unfold atU0
  split_ifs with h
  · have hx' : (x : ℝ) ≤ (rup x : ℝ) := by exact_mod_cast le_rup x
    have h0 : (0 : ℝ) ≤ (rup x : ℝ) := by exact_mod_cast hx.trans (le_rup x)
    have h1 : (rup x : ℝ) < 1 := by exact_mod_cast h.2
    calc Real.arctan x ≤ Real.arctan (rup x) := Real.arctan_mono hx'
      _ ≤ _ := (arctan_alt _ h0 h1 6).2
      _ = ((atSer (rup x) 13 : ℚ) : ℝ) := (atSer_cast _ _).symm
      _ ≤ _ := by exact_mod_cast le_rup _
  · exact Real.arctan_le_self (by exact_mod_cast hx)

lemma atL0_le_arctan (x : ℚ) (hx : 0 ≤ x) : (atL0 x : ℝ) ≤ Real.arctan x := by
  unfold atL0
  split_ifs with h
  · have hx' : (rdn x : ℝ) ≤ (x : ℝ) := by exact_mod_cast rdn_le x
    have h0 : (0 : ℝ) ≤ (rdn x : ℝ) := by exact_mod_cast h.1
    have h1 : (rdn x : ℝ) < 1 := hx'.trans_lt (by exact_mod_cast h.2)
    calc ((rdn (atSer (rdn x) 12) : ℚ) : ℝ) ≤ ((atSer (rdn x) 12 : ℚ) : ℝ) := by
          exact_mod_cast rdn_le _
      _ = _ := atSer_cast _ _
      _ ≤ Real.arctan (rdn x) := (arctan_alt _ h0 h1 6).1
      _ ≤ _ := Real.arctan_mono hx'
  · push_cast; exact Real.arctan_nonneg.2 (by exact_mod_cast hx)

/-- Signed versions for `|z| < 1`. -/
def atUs (z : ℚ) : ℚ := if 0 ≤ z then atU0 z else -atL0 (-z)
def atLs (z : ℚ) : ℚ := if 0 ≤ z then atL0 z else -atU0 (-z)

lemma arctan_le_atUs (z : ℚ) : Real.arctan z ≤ atUs z := by
  unfold atUs
  split_ifs with h
  · exact arctan_le_atU0 z h
  · have := atL0_le_arctan (-z) (by linarith)
    push_cast at this ⊢
    rw [Real.arctan_neg] at this; linarith

lemma atLs_le_arctan (z : ℚ) : (atLs z : ℝ) ≤ Real.arctan z := by
  unfold atLs
  split_ifs with h
  · exact atL0_le_arctan z h
  · have := arctan_le_atU0 (-z) (by linarith)
    push_cast at this ⊢
    rw [Real.arctan_neg] at this; linarith

def PIlo : ℚ := 3141592 / 10 ^ 6
def PIhi : ℚ := 3141593 / 10 ^ 6

lemma pi_bounds : (PIlo : ℝ) < Real.pi ∧ Real.pi < PIhi := by
  unfold PIlo PIhi
  constructor
  · have := Real.pi_gt_d6; push_cast; linarith
  · have := Real.pi_lt_d6; push_cast; linarith

lemma arctan_shift (x : ℝ) (hx : 0 < x) :
    Real.arctan x = Real.pi / 4 + Real.arctan ((x - 1) / (x + 1)) := by
  have hz : 1 * ((x - 1) / (x + 1)) < 1 := by
    rw [one_mul, div_lt_one (by linarith)]; linarith
  rw [← Real.arctan_one, Real.arctan_add hz]
  congr 1
  field_simp
  ring

lemma arctan_inv' (x : ℝ) (hx : 0 < x) : Real.arctan x = Real.pi / 2 - Real.arctan (1 / x) := by
  rw [one_div, Real.arctan_inv_of_pos hx]; ring

/-- `arctan` bounds for `x ≥ 0`. -/
def atU (x : ℚ) : ℚ :=
  if x ≤ 1 / 2 then atU0 x
  else if x ≤ 2 then PIhi / 4 + atUs ((x - 1) / (x + 1))
  else PIhi / 2 - atL0 (1 / x)

def atL (x : ℚ) : ℚ :=
  if x ≤ 1 / 2 then atL0 x
  else if x ≤ 2 then PIlo / 4 + atLs ((x - 1) / (x + 1))
  else PIlo / 2 - atU0 (1 / x)

lemma arctan_le_atU (x : ℚ) (hx : 0 ≤ x) : Real.arctan x ≤ atU x := by
  have hpi := pi_bounds
  unfold atU
  split_ifs with h1 h2
  · exact arctan_le_atU0 x hx
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
    have := arctan_le_atUs ((x - 1) / (x + 1))
    rw [arctan_shift _ hx0]
    push_cast at this ⊢; linarith
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
    have := atL0_le_arctan (1 / x) (by positivity)
    rw [arctan_inv' _ hx0]
    push_cast at this ⊢; linarith

lemma atL_le_arctan (x : ℚ) (hx : 0 ≤ x) : (atL x : ℝ) ≤ Real.arctan x := by
  have hpi := pi_bounds
  unfold atL
  split_ifs with h1 h2
  · exact atL0_le_arctan x hx
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
    have := atLs_le_arctan ((x - 1) / (x + 1))
    rw [arctan_shift _ hx0]
    push_cast at this ⊢; linarith
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
    have := arctan_le_atU0 (1 / x) (by positivity)
    rw [arctan_inv' _ hx0]
    push_cast at this ⊢; linarith


/-! ## The integrals `∫₀ᶜ log(t + u²) du` -/

def Ic (c t : ℝ) : ℝ := ∫ u in (0 : ℝ)..c, Real.log (t + u ^ 2)

lemma Ic_integrable (c t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => Real.log (t + u ^ 2)) volume 0 c := by
  rcases ht.eq_or_lt with h | h
  · subst h
    have : (fun u : ℝ => Real.log (0 + u ^ 2)) = fun u => 2 * Real.log u := by
      funext u; rw [zero_add, Real.log_pow]; push_cast; ring
    rw [this]
    exact (intervalIntegral.intervalIntegrable_log' (a := 0) (b := c)).const_mul 2
  · refine (Continuous.continuousOn ?_).intervalIntegrable
    exact Continuous.log (by fun_prop) fun u => by positivity

lemma Ic_closed (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    Ic c t = c * Real.log (t + c ^ 2) - 2 * c + 2 * Real.sqrt t * Real.arctan (c / Real.sqrt t) := by
  unfold Ic
  rcases ht.eq_or_lt with h | h
  · subst h
    have : (fun u : ℝ => Real.log (0 + u ^ 2)) = fun u => 2 * Real.log u := by
      funext u; rw [zero_add, Real.log_pow]; push_cast; ring
    rw [this, intervalIntegral.integral_const_mul, integral_log, zero_add, Real.log_pow,
      Real.sqrt_zero]
    simp; ring
  · set s := Real.sqrt t with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 h
    have hts : t = s ^ 2 := (Real.sq_sqrt h.le).symm
    have hd : ∀ u ∈ uIcc (0 : ℝ) c, HasDerivAt
        (fun u => u * Real.log (t + u ^ 2) - 2 * u + 2 * s * Real.arctan (u / s))
        (Real.log (t + u ^ 2)) u := by
      intro u _
      have hpos : 0 < t + u ^ 2 := by positivity
      have h1 := ((hasDerivAt_id' u).mul (((hasDerivAt_pow 2 u).const_add t).log hpos.ne'))
      have h2 := (((hasDerivAt_id' u).div_const s).arctan).const_mul (2 * s)
      have h3 := (h1.sub ((hasDerivAt_id' u).const_mul 2)).add h2
      convert h3 using 1
      rw [hts] at hpos ⊢
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Ic_integrable c t h.le)]
    simp

lemma Ic_mono (c : ℝ) (hc : 0 < c) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    Ic c t₁ ≤ Ic c t₂ := by
  unfold Ic
  apply intervalIntegral.integral_mono_on_of_le_Ioo hc.le (Ic_integrable c t₁ h1)
    (Ic_integrable c t₂ (h1.trans h12))
  intro u hu
  have : 0 < t₁ + u ^ 2 := by have := hu.1; positivity
  exact Real.log_le_log this (by linarith)

lemma V_eq (t : ℝ) : V t = 2 * Real.pi * Real.sqrt t + Ic 1 t - 6 * Ic (3 / 40) t := rfl

/-- `V` on `[l, r]` is at least `2π√l + I₁(l) - 6 I_α(r)`. -/
lemma V_lower (l t r : ℝ) (hl : 0 ≤ l) (hlt : l ≤ t) (htr : t ≤ r) :
    2 * Real.pi * Real.sqrt l + Ic 1 l - 6 * Ic (3 / 40) r ≤ V t := by
  rw [V_eq]
  have h1 := Ic_mono 1 one_pos hl hlt
  have h2 := Ic_mono (3 / 40) (by norm_num) (hl.trans hlt) htr
  have h3 : Real.sqrt l ≤ Real.sqrt t := Real.sqrt_le_sqrt hlt
  nlinarith [Real.pi_pos]


/-! ## Computable lower bound for `V` on an interval -/

def Qα : ℚ := 3 / 40

def I1L (l : ℚ) : ℚ := lnL (l + 1) - 2 + 2 * sqL l * atL (1 / sqU l)

def IαU (r : ℚ) : ℚ :=
  Qα * lnU (r + Qα ^ 2) - 2 * Qα +
    2 * sqU r * (if 0 < sqL r then atU (Qα / sqL r) else PIhi / 2)

def VL (l r : ℚ) : ℚ := 2 * PIlo * sqL l + I1L l - 6 * IαU r

lemma I1L_le (l : ℚ) (hl : 0 ≤ l) : (I1L l : ℝ) ≤ Ic 1 l := by
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  rw [Ic_closed 1 l one_pos hl', one_pow, one_mul]
  unfold I1L
  push_cast
  have h1 := lnL_le_log (l + 1) (by linarith)
  push_cast at h1
  have hsL := sqL_le_sqrt l
  have hsL0 : (0 : ℝ) ≤ sqL l := by exact_mod_cast sqL_nonneg l
  have hat0 : 0 ≤ Real.arctan (1 / Real.sqrt l) := Real.arctan_nonneg.2 (by positivity)
  have key : (sqL l : ℝ) * (atL (1 / sqU l) : ℝ) ≤ Real.sqrt l * Real.arctan (1 / Real.sqrt l) := by
    rcases hsL0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]; positivity
    · have hsq : 0 < Real.sqrt l := h0.trans_le hsL
      have hsU : Real.sqrt l ≤ (sqU l : ℝ) := sqrt_le_sqU l hl
      have hA : (atL (1 / sqU l) : ℝ) ≤ Real.arctan (1 / Real.sqrt l) := by
        refine (atL_le_arctan _ (by have := sqU_nonneg l hl; positivity)).trans ?_
        apply Real.arctan_mono
        push_cast
        exact one_div_le_one_div_of_le hsq hsU
      calc (sqL l : ℝ) * (atL (1 / sqU l) : ℝ) ≤ (sqL l : ℝ) * Real.arctan (1 / Real.sqrt l) :=
            mul_le_mul_of_nonneg_left hA hsL0
        _ ≤ _ := mul_le_mul_of_nonneg_right hsL hat0
  push_cast at key
  linarith

lemma IαU_ge (r : ℚ) (hr : 0 ≤ r) : Ic (3 / 40) r ≤ (IαU r : ℝ) := by
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  rw [Ic_closed (3 / 40) r (by norm_num) hr']
  unfold IαU Qα
  have h1 := log_le_lnU (r + (3 / 40) ^ 2) (by positivity)
  push_cast at h1 ⊢
  have hsU := sqrt_le_sqU r hr
  have hat0 : 0 ≤ Real.arctan (3 / 40 / Real.sqrt r) := Real.arctan_nonneg.2 (by positivity)
  set B : ℚ := if 0 < sqL r then atU (3 / 40 / sqL r) else PIhi / 2 with hB
  have hAB : Real.arctan (3 / 40 / Real.sqrt r) ≤ (B : ℝ) := by
    rw [hB]
    split_ifs with h
    · have hsL := sqL_le_sqrt r
      have h0 : (0 : ℝ) < sqL r := by exact_mod_cast h
      refine le_trans ?_ (arctan_le_atU _ (by positivity))
      apply Real.arctan_mono
      push_cast
      exact div_le_div_of_nonneg_left (by norm_num) h0 hsL
    · have := Real.arctan_lt_pi_div_two (3 / 40 / Real.sqrt r)
      have := pi_bounds.2
      push_cast; linarith
  have key : Real.sqrt r * Real.arctan (3 / 40 / Real.sqrt r) ≤ (sqU r : ℝ) * (B : ℝ) :=
    mul_le_mul hsU hAB hat0 (by exact_mod_cast sqU_nonneg r hr)
  have e : (((if 0 < sqL r then atU (3 / 40 / sqL r) else PIhi / 2 : ℚ)) : ℝ) = (B : ℝ) := rfl
  rw [e]
  nlinarith

lemma VL_le (l r : ℚ) (hl : 0 ≤ l) (t : ℝ) (hlt : (l : ℝ) ≤ t) (htr : t ≤ r) :
    (VL l r : ℝ) ≤ V t := by
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hr : (0 : ℚ) ≤ r := by exact_mod_cast hl'.trans (hlt.trans htr)
  refine le_trans ?_ (V_lower l t r hl' hlt htr)
  unfold VL
  push_cast
  have h1 := I1L_le l hl
  have h2 := IαU_ge r hr
  have h3 : (2 * PIlo : ℝ) * sqL l ≤ 2 * Real.pi * Real.sqrt l :=
    mul_le_mul (by linarith [pi_bounds.1]) (sqL_le_sqrt l) (by exact_mod_cast sqL_nonneg l)
      (by positivity)
  linarith

/-! ## The arcsine potentials -/

def aQ (k : ℕ) : ℚ := ((L61.ent k).1 : ℚ) / 10 ^ 12
def bQ (k : ℕ) : ℚ := ((L61.ent k).2.1 : ℚ) / 10 ^ 12
def cQ (k : ℕ) : ℚ := ((L61.ent k).2.2 : ℚ) / 10 ^ 12

lemma aQ_cast (k : ℕ) : (aQ k : ℝ) = L61.A k := by
  unfold aQ L61.A ta; push_cast; rfl
lemma bQ_cast (k : ℕ) : (bQ k : ℝ) = L61.B k := by
  unfold bQ L61.B tb; push_cast; rfl
lemma cQ_cast (k : ℕ) : (cQ k : ℝ) = L61.Cc k := by
  unfold cQ L61.Cc tc; push_cast; rfl

def UkU (k : ℕ) (t : ℚ) : ℚ :=
  if aQ k ≤ t ∧ t ≤ bQ k then lnU ((bQ k - aQ k) / 4)
  else lnU ((|t - (aQ k + bQ k) / 2| + sqU ((t - aQ k) * (t - bQ k))) / 2)

/-- Outside its interval, the argument of the logarithm exceeds `r/2`. -/
lemma out_arg (a b t : ℝ) (hab : a < b) (h : ¬(a ≤ t ∧ t ≤ b)) :
    (b - a) / 2 < |t - (a + b) / 2| ∧ 0 ≤ (t - a) * (t - b) := by
  by_cases h1 : a ≤ t
  · have : b < t := by by_contra h3; exact h ⟨h1, not_lt.1 h3⟩
    refine ⟨?_, by nlinarith⟩
    rw [abs_of_pos (by linarith)]; linarith
  · push Not at h1
    refine ⟨?_, by nlinarith⟩
    rw [abs_of_neg (by linarith)]; linarith

lemma Uk_le_UkU (k : ℕ) (hk : k < 16) (t : ℚ) : L61.Uk k t ≤ UkU k t := by
  have hab := (L61.AB k hk).2.1
  rw [L61.Uk_eq k hk]
  unfold UkU
  have ha := aQ_cast k
  have hb := bQ_cast k
  by_cases h : aQ k ≤ t ∧ t ≤ bQ k
  · have h' : L61.A k ≤ t ∧ (t : ℝ) ≤ L61.B k := by
      rw [← ha, ← hb]; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    rw [if_pos h', if_pos h]
    have := log_le_lnU ((bQ k - aQ k) / 4) (by
      have : aQ k < bQ k := by exact_mod_cast (show (aQ k : ℝ) < bQ k by rw [ha, hb]; exact hab)
      linarith)
    unfold L61.Lk
    push_cast at this; rw [ha, hb] at this; exact this
  · have h' : ¬(L61.A k ≤ t ∧ (t : ℝ) ≤ L61.B k) := by
      rw [← ha, ← hb]; exact fun h2 => h ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
    rw [if_neg h', if_neg h]
    obtain ⟨hr, hp⟩ := out_arg _ _ _ hab h'
    have hpq : (0 : ℚ) ≤ (t - aQ k) * (t - bQ k) := by
      have : (0 : ℝ) ≤ ((t - aQ k) * (t - bQ k) : ℚ) := by push_cast; rw [ha, hb]; exact hp
      exact_mod_cast this
    have hsq := sqrt_le_sqU _ hpq
    have hpos : (0 : ℝ) < (|(t : ℝ) - (L61.A k + L61.B k) / 2| + Real.sqrt ((t - L61.A k) * (t - L61.B k))) / 2 := by
      have := Real.sqrt_nonneg ((t - L61.A k) * (t - L61.B k)); linarith
    have hpos' : (0 : ℚ) < (|t - (aQ k + bQ k) / 2| + sqU ((t - aQ k) * (t - bQ k))) / 2 := by
      have := sqU_nonneg _ hpq
      have : (0 : ℝ) < |(t : ℝ) - (L61.A k + L61.B k) / 2| := by linarith
      have : (0 : ℚ) < |t - (aQ k + bQ k) / 2| := by
        have : (0 : ℝ) < ((|t - (aQ k + bQ k) / 2| : ℚ) : ℝ) := by push_cast; rw [ha, hb]; linarith
        exact_mod_cast this
      positivity
    refine le_trans (Real.log_le_log hpos ?_) (log_le_lnU _ hpos')
    have e : (((t - aQ k) * (t - bQ k) : ℚ) : ℝ) = (t - L61.A k) * (t - L61.B k) := by
      push_cast; rw [ha, hb]
    rw [e] at hsq
    push_cast
    rw [ha, hb]
    linarith

lemma Uk_ge_Lk (k : ℕ) (hk : k < 16) (t : ℝ) : L61.Lk k ≤ L61.Uk k t := by
  have hab := (L61.AB k hk).2.1
  rw [L61.Uk_eq k hk]
  split_ifs with h
  · exact le_rfl
  · obtain ⟨hr, hp⟩ := out_arg _ _ _ hab h
    have := Real.sqrt_nonneg ((t - L61.A k) * (t - L61.B k))
    unfold L61.Lk
    exact Real.log_le_log (by linarith) (by linarith)

/-- Each arcsine potential is quasi-convex. -/
lemma Uk_quasi (k : ℕ) (hk : k < 16) {l t r : ℝ} (hlt : l ≤ t) (htr : t ≤ r) :
    L61.Uk k t ≤ max (L61.Uk k l) (L61.Uk k r) := by
  have hab := (L61.AB k hk).2.1
  set a := L61.A k
  set b := L61.B k
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [L61.Uk_const k hk t h]
    exact le_max_of_le_left (Uk_ge_Lk k hk l)
  · rw [L61.Uk_eq k hk t, if_neg h]
    obtain ⟨hr, hp⟩ := out_arg _ _ _ hab h
    have hsq0 := Real.sqrt_nonneg ((t - a) * (t - b))
    by_cases h1 : a ≤ t
    · have hbt : b < t := by by_contra h3; exact h ⟨h1, not_lt.1 h3⟩
      apply le_max_of_le_right
      have hr' : ¬(a ≤ r ∧ r ≤ b) := fun h2 => by linarith [h2.2]
      rw [L61.Uk_eq k hk r, if_neg hr']
      apply Real.log_le_log (by linarith)
      have e1 : |t - (a + b) / 2| ≤ |r - (a + b) / 2| := by
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      have e2 : Real.sqrt ((t - a) * (t - b)) ≤ Real.sqrt ((r - a) * (r - b)) :=
        Real.sqrt_le_sqrt (by nlinarith)
      linarith
    · push Not at h1
      apply le_max_of_le_left
      have hl' : ¬(a ≤ l ∧ l ≤ b) := fun h2 => by linarith [h2.1]
      rw [L61.Uk_eq k hk l, if_neg hl']
      apply Real.log_le_log (by linarith)
      have e1 : |t - (a + b) / 2| ≤ |l - (a + b) / 2| := by
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
      have e2 : Real.sqrt ((t - a) * (t - b)) ≤ Real.sqrt ((l - a) * (l - b)) :=
        Real.sqrt_le_sqrt (by nlinarith)
      linarith

/-! ## The checker -/

def Ubnd (l r : ℚ) : ℚ := ∑ k ∈ range 16, cQ k * max (UkU k l) (UkU k r)

def Bd : ℚ := -66451 / 10 ^ 4

def chk (l r : ℚ) : Bool := decide (0 ≤ l ∧ l ≤ r ∧ 2 * Ubnd l r - VL l r ≤ Bd)

lemma chk_sound (l r : ℚ) (h : chk l r = true) (t : ℝ) (hlt : (l : ℝ) ≤ t) (htr : t ≤ r) :
    2 * logPot rho t - V t ≤ Bd := by
  unfold chk at h
  obtain ⟨hl, -, hB⟩ := of_decide_eq_true h
  have hV := VL_le l r hl t hlt htr
  have hU : logPot rho t ≤ (Ubnd l r : ℝ) := by
    rw [L61.logPot_rho]
    unfold Ubnd
    push_cast
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [cQ_cast]
    refine mul_le_mul_of_nonneg_left ?_ (L61.Cc_nonneg k)
    refine (Uk_quasi k hk' hlt htr).trans ?_
    exact max_le_max (Uk_le_UkU k hk' l) (Uk_le_UkU k hk' r)
  have hB' : (2 * (Ubnd l r : ℝ) - VL l r) ≤ Bd := by exact_mod_cast hB
  linarith

def chain : ℚ → List ℚ → Bool
  | _, [] => true
  | l, r :: rest => chk l r && chain r rest

def lastD : ℚ → List ℚ → ℚ
  | l, [] => l
  | _, r :: rest => lastD r rest

lemma chain_sound : ∀ (xs : List ℚ) (l : ℚ), chain l xs = true → xs ≠ [] →
    ∀ t : ℝ, (l : ℝ) ≤ t → t ≤ lastD l xs → 2 * logPot rho t - V t ≤ Bd
  | [], _, _, hne, _, _, _ => absurd rfl hne
  | r :: rest, l, h, _, t, h1, h2 => by
    simp only [chain, Bool.and_eq_true] at h
    rcases le_or_gt t r with htr | htr
    · exact chk_sound l r h.1 t h1 htr
    · rcases rest with _ | ⟨r', rest'⟩
      · simp only [lastD] at h2; exact absurd h2 (not_le.2 htr)
      · exact chain_sound (r' :: rest') r h.2 (List.cons_ne_nil _ _) t htr.le h2

lemma chain_append (l : ℚ) (xs ys : List ℚ) :
    chain l (xs ++ ys) = (chain l xs && chain (lastD l xs) ys) := by
  induction xs generalizing l with
  | nil => simp [chain, lastD]
  | cons x xs ih => simp [chain, lastD, ih, Bool.and_assoc]

lemma lastD_append (l : ℚ) (xs ys : List ℚ) : lastD l (xs ++ ys) = lastD (lastD l xs) ys := by
  induction xs generalizing l with
  | nil => simp [lastD]
  | cons x xs ih => simp [lastD, ih]


/-! ## The tail `t ≥ 2` -/

lemma Uk_le_log (k : ℕ) (hk : k < 16) (t : ℝ) (ht : 2 ≤ t) : L61.Uk k t ≤ Real.log t := by
  obtain ⟨h0, hab, h2⟩ := L61.AB k hk
  have h' : ¬(L61.A k ≤ t ∧ t ≤ L61.B k) := fun h => by linarith [h.2]
  rw [L61.Uk_eq k hk, if_neg h']
  obtain ⟨hr, hp⟩ := out_arg _ _ _ hab h'
  have hm : |t - (L61.A k + L61.B k) / 2| = t - (L61.A k + L61.B k) / 2 := abs_of_pos (by linarith)
  have hsq : Real.sqrt ((t - L61.A k) * (t - L61.B k)) ≤ t - (L61.A k + L61.B k) / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have := Real.sqrt_nonneg ((t - L61.A k) * (t - L61.B k))
  exact Real.log_le_log (by linarith) (by linarith)

lemma sum_Cc : ∑ k ∈ range 16, L61.Cc k = 37 / 40 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, L61.Cc, tc, L61.ent, table1]
  norm_num

lemma Ic1_ge (t : ℝ) (ht : 1 ≤ t) : Real.log t ≤ Ic 1 t := by
  unfold Ic
  have := intervalIntegral.integral_mono_on (μ := volume) zero_le_one intervalIntegrable_const
    (Ic_integrable 1 t (by linarith)) (fun u _ => Real.log_le_log (by linarith)
      (by nlinarith : t ≤ t + u ^ 2))
  simpa using this

lemma Icα_le (t : ℝ) (ht : 1 ≤ t) : Ic (3 / 40) t ≤ 3 / 40 * Real.log (t + (3 / 40) ^ 2) := by
  unfold Ic
  have := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 3 / 40)
    (Ic_integrable (3 / 40) t (by linarith)) intervalIntegrable_const
    (fun u hu => Real.log_le_log (by nlinarith) (by nlinarith [hu.1, hu.2] :
      t + u ^ 2 ≤ t + (3 / 40) ^ 2))
  simpa using this

lemma tail_bound (t : ℝ) (ht : 2 ≤ t) : 2 * logPot rho t - V t < -6645002 / 10 ^ 6 := by
  have hU : logPot rho t ≤ 37 / 40 * Real.log t := by
    rw [L61.logPot_rho, ← sum_Cc, Finset.sum_mul]
    exact Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (Uk_le_log k (Finset.mem_range.1 hk) t ht) (L61.Cc_nonneg k)
  rw [V_eq]
  have h1 := Ic1_ge t (by linarith)
  have h2 := Icα_le t (by linarith)
  set s := Real.sqrt t with hs
  have hs2 : s ^ 2 = t := Real.sq_sqrt (by linarith)
  have hs1 : 141 / 100 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; linarith
  have hL : Real.log t = 2 * Real.log s := by rw [← hs2, Real.log_pow]; push_cast; ring
  have hLs := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
  have hL0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hα : Real.log (t + (3 / 40) ^ 2) ≤ Real.log t + (3 / 40) ^ 2 / 2 := by
    have hpos : 0 < t := by linarith
    have : Real.log (t + (3 / 40) ^ 2) - Real.log t ≤ (t + (3 / 40) ^ 2) / t - 1 := by
      rw [← Real.log_div (by positivity) hpos.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have e : (t + (3 / 40) ^ 2) / t - 1 = (3 / 40) ^ 2 / t := by field_simp; ring
    have : (3 / 40 : ℝ) ^ 2 / t ≤ (3 / 40) ^ 2 / 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
    linarith
  have hpi : 314 / 100 * s ≤ Real.pi * s :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_d2]) (by linarith)
  nlinarith

end Pot

end Zeta5
