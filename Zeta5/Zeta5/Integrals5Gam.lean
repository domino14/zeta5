import Zeta5.Integrals5Base

/-!
# Closed form of `R` (eq. (B.1) and (5.13))

`R x = x F(x) + Q`, with `Q` given explicitly by `Qc` in terms of fractional parts.
-/

open MeasureTheory Set
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace Zeta5.I5

def ind (p z : ℝ) : ℝ := if p < z then 1 else 0
def d0 (u : ℝ) : ℝ := min u (1 - u)
def es (u : ℝ) : ℝ := if u ≤ 1 / 2 then 1 else -1

lemma ind_of_lt {p z : ℝ} (h : p < z) : ind p z = 1 := if_pos h
lemma ind_of_le {p z : ℝ} (h : z ≤ p) : ind p z = 0 := if_neg (not_lt.2 h)

lemma es_cases (u : ℝ) : (es u = 1 ∧ d0 u = u) ∨ (es u = -1 ∧ d0 u = 1 - u) := by
  unfold es d0
  by_cases h : u ≤ 1 / 2
  · left; exact ⟨if_pos h, min_eq_left (by linarith)⟩
  · right; exact ⟨if_neg h, min_eq_right (by push Not at h; linarith)⟩

lemma d0_mem (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ d0 u ∧ d0 u ≤ 1 / 2 := by
  unfold d0
  constructor
  · exact le_min h0 (by linarith)
  · rcases le_total u (1 - u) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith

lemma const_piece {h : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hab : a ≤ b) (H : ∀ z ∈ Ioo a b, h z = c) :
    IntervalIntegrable h volume a b ∧ ∫ z in a..b, h z = (b - a) * c := by
  have e : ∀ z ∈ Ioo a b, h z = c + 0 * z + 0 * z ^ 2 := fun z hz => by rw [H z hz]; ring
  refine ⟨piece_quad_int hab _ _ _ e, ?_⟩
  rw [piece_quad hab _ _ _ e]; ring

lemma step3 {h : ℝ → ℝ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (a0 a1 b0 b1 b2 : ℝ)
    (H : ∀ z ∈ Ioo (0 : ℝ) (1 / 2), z ≠ p → z ≠ q →
      h z = (a0 + a1 * ind q z) * (b0 + b1 * ind q z + b2 * ind p z)) :
    ∫ z in (0 : ℝ)..(1 / 2), h z = a0 * b0 / 2 + (a0 * b1 + a1 * b0 + a1 * b1) * (1 / 2 - q) +
      a0 * b2 * (1 / 2 - p) + a1 * b2 * (1 / 2 - max p q) := by
  rcases le_total p q with hpq | hpq
  · have e1 := const_piece (h := h) (a0 * b0) hp0 fun z hz => by
      rw [H z ⟨hz.1, by linarith [hz.2]⟩ hz.2.ne (by linarith [hz.2] : z < q).ne,
        ind_of_le hz.2.le, ind_of_le (by linarith [hz.2] : z ≤ q)]; ring
    have e2 := const_piece (h := h) (a0 * (b0 + b2)) hpq fun z hz => by
      rw [H z ⟨by linarith [hz.1], by linarith [hz.2]⟩ hz.1.ne' hz.2.ne,
        ind_of_le hz.2.le, ind_of_lt hz.1]; ring
    have e3 := const_piece (h := h) ((a0 + a1) * (b0 + b1 + b2)) hq1 fun z hz => by
      rw [H z ⟨by linarith [hz.1], hz.2⟩ (by linarith [hz.1] : p < z).ne' hz.1.ne',
        ind_of_lt hz.1, ind_of_lt (by linarith [hz.1] : p < z)]; ring
    rw [(chain (chain e1 e2) e3).2, max_eq_right hpq]; ring
  · have e1 := const_piece (h := h) (a0 * b0) hq0 fun z hz => by
      rw [H z ⟨hz.1, by linarith [hz.2]⟩ (by linarith [hz.2] : z < p).ne hz.2.ne,
        ind_of_le hz.2.le, ind_of_le (by linarith [hz.2] : z ≤ p)]; ring
    have e2 := const_piece (h := h) ((a0 + a1) * (b0 + b1)) hpq fun z hz => by
      rw [H z ⟨by linarith [hz.1], by linarith [hz.2]⟩ hz.2.ne hz.1.ne',
        ind_of_le hz.2.le, ind_of_lt hz.1]; ring
    have e3 := const_piece (h := h) ((a0 + a1) * (b0 + b1 + b2)) hp1 fun z hz => by
      rw [H z ⟨by linarith [hz.1], hz.2⟩ hz.1.ne' (by linarith [hz.1] : q < z).ne',
        ind_of_lt hz.1, ind_of_lt (by linarith [hz.1] : q < z)]; ring
    rw [(chain (chain e1 e2) e3).2, max_eq_left hpq]; ring

lemma ell_step (y z : ℝ) (hz : z ∈ Ioo (0 : ℝ) (1 / 2)) (hzp : z ≠ d0 (Int.fract y)) :
    Lim.ell y z = 2 * (⌊y⌋ : ℝ) + 1 - es (Int.fract y) * ind (d0 (Int.fract y)) z := by
  obtain ⟨hz0, hz1⟩ := hz
  have hy : y = ⌊y⌋ + Int.fract y := (Int.floor_add_fract y).symm
  have f0 := Int.fract_nonneg y
  have f1 := Int.fract_lt_one y
  unfold Lim.ell
  by_cases hu : Int.fract y ≤ 1 / 2
  · have hd : d0 (Int.fract y) = Int.fract y := min_eq_left (by linarith)
    have he : es (Int.fract y) = 1 := if_pos hu
    rw [hd] at hzp; rw [hd, he]
    have h2 : ⌊y + z⌋ = ⌊y⌋ := Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
    rcases lt_or_gt_of_ne hzp with h | h
    · have h1 : ⌊y - z⌋ = ⌊y⌋ := Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
      rw [h1, h2, ind_of_le h.le]; ring
    · have h1 : ⌊y - z⌋ = ⌊y⌋ - 1 :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2, ind_of_lt h]; push_cast; ring
  · push Not at hu
    have hd : d0 (Int.fract y) = 1 - Int.fract y := min_eq_right (by linarith)
    have he : es (Int.fract y) = -1 := if_neg (not_le.2 hu)
    rw [hd] at hzp; rw [hd, he]
    have h1 : ⌊y - z⌋ = ⌊y⌋ := Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
    rcases lt_or_gt_of_ne hzp with h | h
    · have h2 : ⌊y + z⌋ = ⌊y⌋ := Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
      rw [h1, h2, ind_of_le h.le]; ring
    · have h2 : ⌊y + z⌋ = ⌊y⌋ + 1 :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2, ind_of_lt h]; push_cast; ring

/-- The `z`-integral in `Γ`. -/
lemma gam_int (x T : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), (T - 3 * Lim.ell (Lim.α * x) z) *
        (T + 3 * Lim.ell (Lim.α * x) z - Lim.ell x z - 5) =
      let p := d0 (Int.fract x)
      let q := d0 (Int.fract (Lim.α * x))
      let a0 := T - 3 * (2 * (⌊Lim.α * x⌋ : ℝ) + 1)
      let a1 := 3 * es (Int.fract (Lim.α * x))
      let b0 := T + 3 * (2 * (⌊Lim.α * x⌋ : ℝ) + 1) - (2 * (⌊x⌋ : ℝ) + 1) - 5
      let b1 := -3 * es (Int.fract (Lim.α * x))
      let b2 := es (Int.fract x)
      a0 * b0 / 2 + (a0 * b1 + a1 * b0 + a1 * b1) * (1 / 2 - q) +
        a0 * b2 * (1 / 2 - p) + a1 * b2 * (1 / 2 - max p q) := by
  have hp := d0_mem (Int.fract x) (Int.fract_nonneg _) (Int.fract_lt_one _).le
  have hq := d0_mem (Int.fract (Lim.α * x)) (Int.fract_nonneg _) (Int.fract_lt_one _).le
  refine step3 hp.1 hp.2 hq.1 hq.2 _ _ _ _ _ fun z hz hzp hzq => ?_
  rw [ell_step x z hz hzp, ell_step (Lim.α * x) z hz hzq]
  ring

/-- `R(x) - x F(x)`, eq. (5.13) with (B.1). Arguments: `{x}, {αx}, {2Hx}, {2x}, {2λx}`. -/
def Qc (f g τ σ η : ℝ) : ℝ :=
  9 * (d0 g * (1 - 2 * d0 g)) -
    3 * (es f * es g * (d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g)) +
    ((τ ^ 2 - σ * τ) / 2 - Lim.pos ((τ - σ) / 2)) + (η - η ^ 2) / 2

theorem R_eq (x : ℝ) :
    Lim.R x = x * (4 * Lim.lam + 2 * Lim.lam * Int.fract x - 12 * Lim.lam * Int.fract (Lim.α * x)) +
      Qc (Int.fract x) (Int.fract (Lim.α * x)) (Int.fract (2 * Lim.Hc * x)) (Int.fract (2 * x))
        (Int.fract (2 * (Lim.lam * x))) := by
  simp only [Lim.R, Lim.Gam, Lim.Nfun, Lim.J]
  rw [gam_int]
  simp only [← Int.self_sub_fract, Qc]
  rcases es_cases (Int.fract x) with ⟨he, hd⟩ | ⟨he, hd⟩ <;>
  rcases es_cases (Int.fract (Lim.α * x)) with ⟨he', hd'⟩ | ⟨he', hd'⟩ <;>
  · rw [he, hd, he', hd']
    simp only [Lim.pos, Lim.Hc, Lim.α, Lim.lam]
    ring_nf

lemma Qc_bounds (f g τ σ η : ℝ) (hf : 0 ≤ f ∧ f ≤ 1) (hg : 0 ≤ g ∧ g ≤ 1)
    (hτ : 0 ≤ τ ∧ τ ≤ 1) (hσ : 0 ≤ σ ∧ σ ≤ 1) (hη : 0 ≤ η ∧ η ≤ 1) :
    -1 / 2 ≤ Qc f g τ σ η ∧ Qc f g τ σ η ≤ 13 / 8 := by
  have hp := d0_mem f hf.1 hf.2
  have hq := d0_mem g hg.1 hg.2
  set p := d0 f
  set q := d0 g
  have t1a : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq.1 (by linarith)
  have t1b : q * (1 - 2 * q) ≤ 1 / 8 := by nlinarith [sq_nonneg (q - 1 / 4)]
  have t2 : 0 ≤ p + q - max p q - 2 * p * q ∧ p + q - max p q - 2 * p * q ≤ 1 / 8 := by
    rcases le_total p q with h | h
    · rw [max_eq_right h]; constructor <;> nlinarith [sq_nonneg (p - 1 / 4)]
    · rw [max_eq_left h]; constructor <;> nlinarith [sq_nonneg (q - 1 / 4)]
  have hs : ∀ u, es u = 1 ∨ es u = -1 := fun u => by
    unfold es; split_ifs <;> simp
  have t2' : -1 / 8 ≤ es f * es g * (p + q - max p q - 2 * p * q) ∧
      es f * es g * (p + q - max p q - 2 * p * q) ≤ 1 / 8 := by
    rcases hs f with h | h <;> rcases hs g with h' | h' <;> rw [h, h'] <;>
      constructor <;> linarith [t2.1, t2.2]
  have t3 : -1 / 8 ≤ (τ ^ 2 - σ * τ) / 2 - Lim.pos ((τ - σ) / 2) ∧
      (τ ^ 2 - σ * τ) / 2 - Lim.pos ((τ - σ) / 2) ≤ 0 := by
    unfold Lim.pos
    rcases le_total ((τ - σ) / 2) 0 with h | h
    · rw [max_eq_right h]; constructor <;> nlinarith [sq_nonneg (τ - σ / 2)]
    · rw [max_eq_left h]; constructor <;> nlinarith [sq_nonneg (τ - (1 + σ) / 2)]
  have t4a : 0 ≤ (η - η ^ 2) / 2 := by nlinarith
  have t4b : (η - η ^ 2) / 2 ≤ 1 / 8 := by nlinarith [sq_nonneg (η - 1 / 2)]
  unfold Qc
  constructor <;> linarith [t2'.1, t2'.2, t3.1, t3.2]

theorem _root_.Zeta5.R_decomp_bound' (x : ℝ) (_hx : 3 ≤ x) :
    -1 / 2 ≤ Lim.R x - x * (4 * Lim.lam + 2 * Lim.lam * Int.fract x -
        12 * Lim.lam * Int.fract (Lim.α * x)) ∧
    Lim.R x - x * (4 * Lim.lam + 2 * Lim.lam * Int.fract x -
        12 * Lim.lam * Int.fract (Lim.α * x)) ≤ 13 / 8 := by
  have r : ∀ u : ℝ, 0 ≤ Int.fract u ∧ Int.fract u ≤ 1 :=
    fun u => ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  rw [R_eq]; simp only [add_sub_cancel_left]
  exact Qc_bounds _ _ _ _ _ (r _) (r _) (r _) (r _) (r _)

lemma fract_nat (u : ℝ) (k : ℕ) (h1 : (k : ℝ) ≤ u) (h2 : u < k + 1) : Int.fract u = u - k := by
  rw [Int.fract, show ⌊u⌋ = (k : ℤ) from Int.floor_eq_iff.2 ⟨by push_cast; linarith,
    by push_cast; linarith⟩]; push_cast; ring

end Zeta5.I5
