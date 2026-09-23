import Zeta5.Integrals5Gam
import Zeta5.Integrals5

/-!
# Integrability of `R(x)/x³` and the tails (5.16), (5.17)
-/

open MeasureTheory Set Filter Topology
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
noncomputable section
namespace Zeta5.I5

/-- `F(x) = 4λ + 2λ{x} - 12λ{αx}`. -/
def Fx (x : ℝ) : ℝ := 4 * Lim.lam + 2 * Lim.lam * Int.fract x - 12 * Lim.lam * Int.fract (Lim.α * x)

lemma meas_es : Measurable es :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

lemma meas_d0 : Measurable d0 := by unfold d0; fun_prop

lemma meas_fract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract

lemma meas_Fx : Measurable Fx := by
  unfold Fx
  have h1 := meas_fract
  have h2 : Measurable fun x : ℝ => Int.fract (Lim.α * x) := meas_fract.comp (by fun_prop)
  fun_prop

lemma meas_R : Measurable Lim.R := by
  have e : Lim.R = fun x => x * Fx x + Qc (Int.fract x) (Int.fract (Lim.α * x))
      (Int.fract (2 * Lim.Hc * x)) (Int.fract (2 * x)) (Int.fract (2 * (Lim.lam * x))) := by
    funext x; rw [R_eq]; rfl
  rw [e]
  have hF := meas_Fx
  have m : ∀ c : ℝ, Measurable fun x : ℝ => Int.fract (c * x) := fun c => meas_fract.comp (by fun_prop)
  have m1 : Measurable fun x : ℝ => Int.fract x := meas_fract
  have m2 := m Lim.α
  have m3 := m (2 * Lim.Hc)
  have m4 := m 2
  have m5 : Measurable fun x : ℝ => Int.fract (2 * (Lim.lam * x)) := meas_fract.comp (by fun_prop)
  have e1 := meas_es.comp m1
  have e2 := meas_es.comp m2
  have d1 := meas_d0.comp m1
  have d2 := meas_d0.comp m2
  unfold Qc Lim.pos
  simp only [Function.comp_def] at e1 e2 d1 d2
  fun_prop

lemma Fx_bounds (x : ℝ) : -37 / 5 ≤ Fx x ∧ Fx x ≤ 111 / 20 := by
  have := Int.fract_nonneg x; have := Int.fract_lt_one x
  have := Int.fract_nonneg (Lim.α * x); have := Int.fract_lt_one (Lim.α * x)
  unfold Fx Lim.lam; constructor <;> linarith

lemma Q_bounds (x : ℝ) (hx : 3 ≤ x) : -1 / 2 ≤ Lim.R x - x * Fx x ∧ Lim.R x - x * Fx x ≤ 13 / 8 :=
  R_decomp_bound' x hx

lemma R_abs_le (x : ℝ) (hx : 3 ≤ x) : |Lim.R x| ≤ 9 * x := by
  have h1 := Fx_bounds x
  have h2 := Q_bounds x hx
  rw [abs_le]; constructor <;> nlinarith

lemma R_div_bound (x : ℝ) (hx : 3 ≤ x) : ‖Lim.R x / x ^ 3‖ ≤ 9 * x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < x ^ 3), Real.rpow_neg hx0.le,
    Real.rpow_two, div_le_iff₀ (by positivity)]
  have := R_abs_le x hx
  calc |Lim.R x| ≤ 9 * x := this
    _ = 9 * (x ^ 2)⁻¹ * x ^ 3 := by field_simp

theorem _root_.Zeta5.R_integrableOn' :
    IntegrableOn (fun x => Lim.R x / x ^ 3) (Set.Ici 3) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hg : IntegrableOn (fun x : ℝ => 9 * x ^ (-2 : ℝ)) (Ioi 3) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul 9
  refine Integrable.mono' hg ?_ ?_
  · exact (meas_R.div (by fun_prop)).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      R_div_bound x (le_of_lt hx))

/-! ### Derivatives of `P`, `C` -/

/-- The exceptional set: `x ∈ ℤ` or `αx ∈ ℤ`. -/
def Sx : Set ℝ := range (fun k : ℤ => (k : ℝ)) ∪ range (fun k : ℤ => (k : ℝ) * (40 / 3))

lemma Sx_countable : Sx.Countable := (countable_range _).union (countable_range _)

lemma hasDerivAt_fract' {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) : HasDerivAt Int.fract 1 x := by
  have h1 : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (hx _).symm
  have h2 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have e : (fun y => y - (⌊x⌋ : ℝ)) =ᶠ[𝓝 x] Int.fract := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with y hy
    rw [Int.fract, Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩]
  exact ((hasDerivAt_id x).sub_const _).congr_of_eventuallyEq e.symm

lemma fract_derivs {x : ℝ} (hx : x ∉ Sx) :
    HasDerivAt Int.fract 1 x ∧ HasDerivAt (fun y => Int.fract (Lim.α * y)) Lim.α x := by
  simp only [Sx, mem_union, mem_range, not_or, not_exists] at hx
  refine ⟨hasDerivAt_fract' fun k h => hx.1 k h.symm, ?_⟩
  have : ∀ k : ℤ, Lim.α * x ≠ k := fun k h => hx.2 k (by
    unfold Lim.α at h; linarith)
  have h3 := (hasDerivAt_fract' this).comp x ((hasDerivAt_id x).const_mul Lim.α)
  rw [one_mul, mul_one] at h3; exact h3

lemma Pper_deriv {x : ℝ} (hx : x ∉ Sx) : HasDerivAt Lim.Pper (Fx x + Lim.lam) x := by
  obtain ⟨h1, h2⟩ := fract_derivs hx
  have := ((h2.mul ((hasDerivAt_const x 1).sub h2)).const_mul 74).sub
    ((h1.mul ((hasDerivAt_const x 1).sub h1)).const_mul Lim.lam)
  convert this using 1
  · funext y; simp [Lim.Pper] <;> ring
  · simp [Fx, Lim.α, Lim.lam] <;> ring

lemma Cper_deriv {x : ℝ} (hx : x ∉ Sx) : HasDerivAt Lim.Cper (Lim.Pper x - 2923 / 240) x := by
  obtain ⟨h1, h2⟩ := fract_derivs hx
  have hG : ∀ {f : ℝ → ℝ} {f' : ℝ}, HasDerivAt f f' x →
      HasDerivAt (fun y => Lim.G0 (f y)) ((f x * (1 - f x) - 1 / 6) * f') x := by
    intro f f' hf
    have := ((((hf.mul ((hasDerivAt_const x 1).sub hf)).mul
      ((hf.const_mul 2).sub (hasDerivAt_const x 1)))).div_const 6)
    convert this using 1
    · funext y; simp [Lim.G0] <;> ring
    · simp <;> ring
  have := ((hG h2).const_mul (74 / Lim.α)).sub ((hG h1).const_mul Lim.lam)
  convert this using 1
  · funext y; simp [Lim.Cper] <;> ring
  · simp [Lim.Pper, Lim.α, Lim.lam] <;> ring

lemma Pper_cont : Continuous Lim.Pper := by
  have h : Continuous ((fun v : ℝ => v * (1 - v)) ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (by fun_prop) (by norm_num)
  have h' : Continuous fun x : ℝ => Int.fract (Lim.α * x) * (1 - Int.fract (Lim.α * x)) :=
    h.comp (continuous_const_mul Lim.α)
  unfold Lim.Pper
  exact (h'.const_smul (74 : ℝ)).sub (h.const_smul Lim.lam) |>.congr fun x => by
    simp [smul_eq_mul, mul_assoc]

lemma Cper_cont : Continuous Lim.Cper := by
  have h : Continuous (Lim.G0 ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (by unfold Lim.G0; fun_prop) (by norm_num [Lim.G0])
  have h' : Continuous fun x : ℝ => Lim.G0 (Int.fract (Lim.α * x)) :=
    h.comp (continuous_const_mul Lim.α)
  unfold Lim.Cper
  exact (h'.const_smul (74 / Lim.α)).sub (h.const_smul Lim.lam) |>.congr fun x => by
    simp [smul_eq_mul]

lemma Pper_abs_le (x : ℝ) : |Lim.Pper x - 2923 / 240| ≤ 32 := by
  have := Int.fract_nonneg x; have := Int.fract_lt_one x
  have := Int.fract_nonneg (Lim.α * x); have := Int.fract_lt_one (Lim.α * x)
  unfold Lim.Pper Lim.lam; rw [abs_le]; constructor <;> nlinarith

/-- The primitive `Φ` with `Φ' = F/x² - 6C/x⁴` off `Sx`. -/
def Phi (x : ℝ) : ℝ := (Lim.Pper x - 2923 / 240) / x ^ 2 + Lim.lam / x + 2 * Lim.Cper x / x ^ 3

lemma Phi_deriv {x : ℝ} (hx0 : 0 < x) (hx : x ∉ Sx) :
    HasDerivAt Phi (Fx x / x ^ 2 - 6 * Lim.Cper x / x ^ 4) x := by
  have hP := Pper_deriv hx
  have hC := Cper_deriv hx
  have h2 := hasDerivAt_pow 2 x
  have h3 := hasDerivAt_pow 3 x
  have := (((hP.sub_const (2923 / 240)).div h2 (by positivity)).add
    ((hasDerivAt_const x Lim.lam).div (hasDerivAt_id x) hx0.ne')).add
    ((hC.const_mul 2).div h3 (by positivity))
  convert this using 1
  · funext y; simp [Phi]
  · simp only [id]; field_simp; ring

lemma Phi_cont : Continuous fun x => Lim.Pper x - 2923 / 240 := by
  have := Pper_cont; fun_prop

lemma Phi_contOn (a b : ℝ) (ha : 0 < a) : ContinuousOn Phi (Icc a b) := by
  have hP := Pper_cont; have hC := Cper_cont
  unfold Phi
  apply ContinuousOn.add; apply ContinuousOn.add
  · exact (hP.sub continuous_const).continuousOn.div (by fun_prop) fun x hx => by
      have : 0 < x := by linarith [hx.1]
      positivity
  · exact continuousOn_const.div continuousOn_id fun x hx => by
      have : 0 < x := by linarith [hx.1]
      positivity
  · exact (hC.const_smul (2 : ℝ)).continuousOn.div (by fun_prop) fun x hx => by
      have : 0 < x := by linarith [hx.1]
      positivity

lemma Phi_abs_le (x : ℝ) (hx : 1 ≤ x) : |Phi x| ≤ 65 / x := by
  have h1 := Pper_abs_le x
  have h2 := Cper_bound' x
  have hx0 : 0 < x := by linarith
  unfold Phi
  have e1 : |(Lim.Pper x - 2923 / 240) / x ^ 2| ≤ 32 / x := by
    rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2), div_le_div_iff₀ (by positivity) hx0]
    nlinarith
  have e2 : |Lim.lam / x| ≤ 1 / x := by
    rw [abs_div, abs_of_pos hx0, Lim.lam]; gcongr; norm_num [abs_of_pos]
  have e3 : |2 * Lim.Cper x / x ^ 3| ≤ 32 / x := by
    rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 3), div_le_div_iff₀ (by positivity) hx0,
      abs_mul, abs_two]
    have : x ≤ x ^ 3 := by nlinarith
    nlinarith [abs_nonneg (Lim.Cper x)]
  calc |_| ≤ |(Lim.Pper x - 2923 / 240) / x ^ 2| + |Lim.lam / x| + |2 * Lim.Cper x / x ^ 3| :=
        abs_add_three _ _ _
    _ ≤ 32 / x + 1 / x + 32 / x := by linarith
    _ = 65 / x := by ring

/-! ### The tail identity -/

lemma ii_of_bdd {f : ℝ → ℝ} {a b : ℝ} (B : ℝ) (hm : Measurable f)
    (hb : ∀ x ∈ uIoc a b, |f x| ≤ B) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := B) ?_ hm.aestronglyMeasurable ?_
  · exact ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  · exact (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hb x hx)

lemma abs_div_pow_le (a x : ℝ) (k : ℕ) (hx : 1 ≤ x) : |a / x ^ k| ≤ |a| := by
  rw [abs_div, abs_of_pos (by positivity : 0 < x ^ k)]
  exact div_le_self (abs_nonneg a) (one_le_pow₀ hx)

lemma mem_uIoc_ge {M N x : ℝ} (hMN : M ≤ N) (hx : x ∈ uIoc M N) : M ≤ x := by
  rw [uIoc_of_le hMN] at hx; exact hx.1.le

lemma ii_T1 {M N : ℝ} (hM : 3 ≤ M) (hMN : M ≤ N) :
    IntervalIntegrable (fun x => Fx x / x ^ 2) volume M N :=
  ii_of_bdd 8 (meas_Fx.div (by fun_prop)) fun x hx => by
    have h := mem_uIoc_ge hMN hx
    refine (abs_div_pow_le _ _ _ (by linarith)).trans ?_
    have := Fx_bounds x; rw [abs_le]; constructor <;> linarith

lemma ii_T2 {M N : ℝ} (hM : 3 ≤ M) (hMN : M ≤ N) :
    IntervalIntegrable (fun x => 6 * Lim.Cper x / x ^ 4) volume M N :=
  ii_of_bdd 96 ((Cper_cont.measurable.const_mul 6).div (by fun_prop)) fun x hx => by
    have h := mem_uIoc_ge hMN hx
    refine (abs_div_pow_le _ _ _ (by linarith)).trans ?_
    have := Cper_bound' x; rw [abs_mul]; norm_num; linarith

lemma ii_T3 {M N : ℝ} (hM : 3 ≤ M) (hMN : M ≤ N) :
    IntervalIntegrable (fun x => (Lim.R x - x * Fx x) / x ^ 3) volume M N :=
  ii_of_bdd 2 ((meas_R.sub (by have := meas_Fx; fun_prop)).div (by fun_prop)) fun x hx => by
    have h := mem_uIoc_ge hMN hx
    refine (abs_div_pow_le _ _ _ (by linarith)).trans ?_
    have := Q_bounds x (by linarith); rw [abs_le]; constructor <;> linarith

lemma tail_identity {M N : ℝ} (hM : 3 ≤ M) (hMN : M ≤ N) :
    ∫ x in M..N, Lim.R x / x ^ 3 =
      Phi N - Phi M + ∫ x in M..N, (6 * Lim.Cper x / x ^ 4 + (Lim.R x - x * Fx x) / x ^ 3) := by
  have hf' := (ii_T1 hM hMN).sub (ii_T2 hM hMN)
  have hr := (ii_T2 hM hMN).add (ii_T3 hM hMN)
  have e : ∫ x in M..N, Lim.R x / x ^ 3 = ∫ x in M..N, ((Fx x / x ^ 2 - 6 * Lim.Cper x / x ^ 4) +
      (6 * Lim.Cper x / x ^ 4 + (Lim.R x - x * Fx x) / x ^ 3)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hMN] at hx
    have : 0 < x := by linarith [hx.1]
    simp only; field_simp; ring
  rw [e, intervalIntegral.integral_add hf' hr,
    integral_eq_of_hasDerivAt_off_countable_of_le Phi _ hMN Sx_countable
      (Phi_contOn M N (by linarith)) (fun x hx => Phi_deriv (by linarith [hx.1.1]) hx.2) hf']

lemma integral_inv34 {M N : ℝ} (hM : 0 < M) (hMN : M ≤ N) (a b : ℝ) :
    ∫ x in M..N, (a / x ^ 4 + b / x ^ 3) =
      (-a / (3 * N ^ 3) - b / (2 * N ^ 2)) - (-a / (3 * M ^ 3) - b / (2 * M ^ 2)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hMN] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h3 := ((hasDerivAt_pow 3 x).const_mul 3).inv (by positivity)
    have h2 := ((hasDerivAt_pow 2 x).const_mul 2).inv (by positivity)
    have := (h3.const_mul (-a)).sub (h2.const_mul b)
    convert this using 1
    · funext y; simp only [Pi.sub_apply, Pi.inv_apply]; ring
    · field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hMN]
    apply ContinuousOn.add <;> apply ContinuousOn.div continuousOn_const (by fun_prop) <;>
      intro x hx <;> have : 0 < x := by linarith [hx.1]
    all_goals positivity

lemma tail_bounds (M : ℝ) (hM : 3 ≤ M) :
    -Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2) ≤ ∫ x in Ioi M, Lim.R x / x ^ 3 ∧
      ∫ x in Ioi M, Lim.R x / x ^ 3 ≤ -Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2) := by
  have hM0 : 0 < M := by linarith
  have hint : IntegrableOn (fun x => Lim.R x / x ^ 3) (Ioi M) :=
    R_integrableOn'.mono_set (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 hM))
  have hlim := intervalIntegral_tendsto_integral_Ioi M hint tendsto_id
  have h0 : Tendsto (fun N : ℝ => 65 / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have key : ∀ N, M ≤ N →
      -65 / N + (-Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2)) ≤ ∫ x in M..id N, Lim.R x / x ^ 3 ∧
      ∫ x in M..id N, Lim.R x / x ^ 3 ≤ 65 / N + (-Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2)) := by
    intro N hN
    have hN0 : 0 < N := by linarith
    have hPhi := Phi_abs_le N (by linarith)
    rw [abs_le] at hPhi
    simp only [id]
    rw [tail_identity hM hN]
    have hr := (ii_T2 hM hN).add (ii_T3 hM hN)
    have lo : ∫ x in M..N, (-96 / x ^ 4 + (-1 / 2) / x ^ 3) ≤
        ∫ x in M..N, (6 * Lim.Cper x / x ^ 4 + (Lim.R x - x * Fx x) / x ^ 3) := by
      apply intervalIntegral.integral_mono_on hN _ hr
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hC := Cper_bound' x; rw [abs_lt] at hC
        have hQ := Q_bounds x (by linarith [hx.1])
        have : -96 / x ^ 4 ≤ 6 * Lim.Cper x / x ^ 4 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        have : -1 / 2 / x ^ 3 ≤ (Lim.R x - x * Fx x) / x ^ 3 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hN]
        apply ContinuousOn.add <;> apply ContinuousOn.div continuousOn_const (by fun_prop) <;>
          intro x hx <;> have : 0 < x := by linarith [hx.1]
        all_goals positivity
    have hi : ∫ x in M..N, (96 / x ^ 4 + (13 / 8) / x ^ 3) ≥
        ∫ x in M..N, (6 * Lim.Cper x / x ^ 4 + (Lim.R x - x * Fx x) / x ^ 3) := by
      apply intervalIntegral.integral_mono_on hN hr
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hN]
        apply ContinuousOn.add <;> apply ContinuousOn.div continuousOn_const (by fun_prop) <;>
          intro x hx <;> have : 0 < x := by linarith [hx.1]
        all_goals positivity
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hC := Cper_bound' x; rw [abs_lt] at hC
        have hQ := Q_bounds x (by linarith [hx.1])
        have : 6 * Lim.Cper x / x ^ 4 ≤ 96 / x ^ 4 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        have : (Lim.R x - x * Fx x) / x ^ 3 ≤ 13 / 8 / x ^ 3 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
    rw [integral_inv34 hM0 hN] at lo hi
    have p1 : 0 ≤ 32 / N ^ 3 + 1 / (4 * N ^ 2) := by positivity
    have p2 : 0 ≤ 32 / N ^ 3 + 13 / (16 * N ^ 2) := by positivity
    constructor
    · have : -(-96) / (3 * N ^ 3) - -1 / 2 / (2 * N ^ 2) = 32 / N ^ 3 + 1 / (4 * N ^ 2) := by ring
      have : -(-96) / (3 * M ^ 3) - -1 / 2 / (2 * M ^ 2) = 32 / M ^ 3 + 1 / (4 * M ^ 2) := by ring
      have : -65 / N = -(65 / N) := by ring
      linarith
    · have : -96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2) = -(32 / N ^ 3 + 13 / (16 * N ^ 2)) := by ring
      have : -96 / (3 * M ^ 3) - 13 / 8 / (2 * M ^ 2) = -(32 / M ^ 3 + 13 / (16 * M ^ 2)) := by ring
      linarith
  constructor
  · have ht : Tendsto (fun N : ℝ => -65 / N + (-Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2))) atTop
        (𝓝 (0 + (-Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2)))) :=
      (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
    rw [zero_add] at ht
    exact le_of_tendsto_of_tendsto ht hlim ((eventually_ge_atTop M).mono fun N hN => (key N hN).1)
  · have ht : Tendsto (fun N : ℝ => 65 / N + (-Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2))) atTop
        (𝓝 (0 + (-Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2)))) := h0.add tendsto_const_nhds
    rw [zero_add] at ht
    exact le_of_tendsto_of_tendsto hlim ht ((eventually_ge_atTop M).mono fun N hN => (key N hN).2)

lemma Phi_20 : Phi 20 = (37 / 2 - 2923 / 240) / 400 + 37 / 800 := by
  have h1 : Int.fract (Lim.α * 20) = 1 / 2 := by
    rw [fract_nat _ 1 (by norm_num [Lim.α]) (by norm_num [Lim.α])]; norm_num [Lim.α]
  have h2 : Int.fract (20 : ℝ) = 0 := by exact_mod_cast Int.fract_natCast 20
  simp only [Phi, Lim.Pper, Lim.Cper, Lim.G0, h1, h2, Lim.lam]
  norm_num

theorem _root_.Zeta5.tail_5_16' : ∫ x in Set.Ioi (20 : ℝ), Lim.R x / x ^ 3 ≤ -2689 / 48000 := by
  have := (tail_bounds 20 (by norm_num)).2
  rw [Phi_20] at this
  linarith

theorem _root_.Zeta5.tail_5_17' (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) :
    -Lim.lam / M + (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 - 32 / (M : ℝ) ^ 3 ≤
      ∫ x in Set.Ioi (M : ℝ), Lim.R x / x ^ 3 := by
  obtain ⟨k, rfl⟩ := hM
  have hk : 1 ≤ k := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : Int.fract (Lim.α * ((40 * k : ℕ) : ℝ)) = 0 := by
    rw [show Lim.α * ((40 * k : ℕ) : ℝ) = ((3 * k : ℕ) : ℝ) by push_cast; unfold Lim.α; ring]
    exact Int.fract_natCast _
  have h2 : Int.fract ((40 * k : ℕ) : ℝ) = 0 := Int.fract_natCast _
  have hPhi : Phi ((40 * k : ℕ) : ℝ) =
      (0 - 2923 / 240) / ((40 * k : ℕ) : ℝ) ^ 2 + Lim.lam / ((40 * k : ℕ) : ℝ) := by
    simp only [Phi, Lim.Pper, Lim.Cper, Lim.G0, h1, h2]; ring
  have := (tail_bounds ((40 * k : ℕ) : ℝ) (by push_cast; linarith)).1
  rw [hPhi] at this
  have hpos : (0 : ℝ) < ((40 * k : ℕ) : ℝ) := by push_cast; linarith
  have e : -Lim.lam / ((40 * k : ℕ) : ℝ) + (2923 / 240 - 1 / 4) / ((40 * k : ℕ) : ℝ) ^ 2 -
      32 / ((40 * k : ℕ) : ℝ) ^ 3 = -((0 - 2923 / 240) / ((40 * k : ℕ) : ℝ) ^ 2 +
        Lim.lam / ((40 * k : ℕ) : ℝ)) - 32 / ((40 * k : ℕ) : ℝ) ^ 3 -
        1 / (4 * ((40 * k : ℕ) : ℝ) ^ 2) := by
    field_simp; ring
  rw [e]; exact this

end Zeta5.I5
