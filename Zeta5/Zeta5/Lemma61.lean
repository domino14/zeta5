import Zeta5.AppendixA

/-!
# Lemma 6.1: mass, support, the arcsine potential (A.1)
-/

open Finset MeasureTheory Set

noncomputable section

namespace Zeta5

namespace L61

/-- `θ ↦ m - r cos θ` with `m = (a+b)/2`, `r = (b-a)/2`. -/
def phi (a b θ : ℝ) : ℝ := (a + b) / 2 - (b - a) / 2 * Real.cos θ

lemma phi_hasDeriv (a b θ : ℝ) :
    HasDerivWithinAt (phi a b) ((b - a) / 2 * Real.sin θ) (Ioo 0 Real.pi) θ := by
  have := ((Real.hasDerivAt_cos θ).const_mul ((b - a) / 2)).const_sub ((a + b) / 2)
  refine (this.congr_deriv ?_).hasDerivWithinAt
  ring

lemma phi_injOn (a b : ℝ) (hab : a < b) : InjOn (phi a b) (Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have hr : (b - a) / 2 ≠ 0 := by linarith
  have : Real.cos x = Real.cos y := by
    unfold phi at hxy
    have := mul_left_cancel₀ hr (by linarith : (b - a) / 2 * Real.cos x = (b - a) / 2 * Real.cos y)
    exact this
  exact Real.injOn_cos ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ this

lemma phi_image (a b : ℝ) (hab : a < b) : phi a b '' Ioo 0 Real.pi = Ioo a b := by
  have hr : 0 < (b - a) / 2 := by linarith
  ext u
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have h1 : Real.cos θ < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
    have h2 : -1 < Real.cos θ := by
      rw [← Real.cos_pi]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
    unfold phi
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    set x := ((a + b) / 2 - u) / ((b - a) / 2) with hx
    have hx1 : x < 1 := by rw [hx, div_lt_one hr]; linarith
    have hx2 : -1 < x := by rw [hx, lt_div_iff₀ hr]; linarith
    refine ⟨Real.arccos x, ⟨Real.arccos_pos.2 hx1, Real.arccos_lt_pi.2 hx2⟩, ?_⟩
    unfold phi
    rw [Real.cos_arccos hx2.le hx1.le, hx, mul_div_cancel₀ _ hr.ne']
    ring

lemma density_phi (a b θ : ℝ) (hab : a < b) (hθ : θ ∈ Ioo 0 Real.pi) :
    |(b - a) / 2 * Real.sin θ| * (1 / (Real.pi * Real.sqrt ((phi a b θ - a) * (b - phi a b θ))))
      = 1 / Real.pi := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hr : 0 < (b - a) / 2 := by linarith
  have hprod : (phi a b θ - a) * (b - phi a b θ) = ((b - a) / 2 * Real.sin θ) ^ 2 := by
    unfold phi
    linear_combination (-(b - a) ^ 2 / 4) * Real.sin_sq_add_cos_sq θ
  rw [hprod, Real.sqrt_sq (by positivity), abs_of_pos (by positivity)]
  have : (b - a) / 2 * Real.sin θ ≠ 0 := by positivity
  have hba : b - a ≠ 0 := by linarith
  field_simp

end L61

open L61

/-- The arcsine density is measurable. -/
lemma arcsine_density_measurable (a b : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (1 / (Real.pi * Real.sqrt ((t - a) * (b - t)))) := by
  fun_prop

/-- Integration against the arcsine measure: `∫ f dω = π⁻¹ ∫_{(0,π)} f(m - r cos θ) dθ`. -/
theorem integral_arcsine (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) :
    ∫ u, f u ∂(arcsine a b) = 1 / Real.pi * ∫ θ in Ioo 0 Real.pi, f (phi a b θ) := by
  unfold arcsine
  have hmeas : Measurable fun t : ℝ => (1 / (Real.pi * Real.sqrt ((t - a) * (b - t)))).toNNReal := by
    fun_prop
  rw [show (fun t : ℝ => ENNReal.ofReal (1 / (Real.pi * Real.sqrt ((t - a) * (b - t))))) =
      fun t => ((1 / (Real.pi * Real.sqrt ((t - a) * (b - t)))).toNNReal : ENNReal) from rfl,
    integral_withDensity_eq_integral_smul hmeas]
  rw [← phi_image a b hab, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => phi_hasDeriv a b θ) (phi_injOn a b hab), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (by positivity), ← mul_assoc, density_phi a b θ hab hθ]

/-- The arcsine measure is a probability measure. -/
theorem arcsine_univ (a b : ℝ) (hab : a < b) : arcsine a b univ = 1 := by
  unfold arcsine
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← phi_image a b hab,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun θ _ => phi_hasDeriv a b θ) (phi_injOn a b hab)]
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => ENNReal.ofReal (1 / Real.pi))
    (fun θ hθ => by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), density_phi a b θ hab hθ])]
  rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
  simp [Real.pi_pos.ne']

instance arcsine_isProb (a b : ℝ) [Fact (a < b)] : IsProbabilityMeasure (arcsine a b) :=
  ⟨arcsine_univ a b Fact.out⟩

theorem arcsine_compl (a b : ℝ) : arcsine a b (Ioo a b)ᶜ = 0 := by
  unfold arcsine
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (measurableSet_Ioo.compl)]
  simp


/-- Scaled table entries. -/
def ta (e : ℕ × ℕ × ℕ) : ℝ := (e.1 : ℝ) / 10 ^ 12
def tb (e : ℕ × ℕ × ℕ) : ℝ := (e.2.1 : ℝ) / 10 ^ 12
def tc (e : ℕ × ℕ × ℕ) : ℝ := (e.2.2 : ℝ) / 10 ^ 12

lemma table1_ab (e : ℕ × ℕ × ℕ) (he : e ∈ table1) : 0 < ta e ∧ ta e < tb e ∧ tb e < 2 := by
  obtain ⟨h1, h2, h3, -⟩ := table1_nested.2.2 e he
  unfold ta tb
  refine ⟨by positivity, ?_, ?_⟩
  · have : (e.1 : ℝ) < e.2.1 := by exact_mod_cast h2
    exact div_lt_div_of_pos_right this (by positivity)
  · have : (e.2.1 : ℝ) < 2 * 10 ^ 12 := by exact_mod_cast h3
    rw [div_lt_iff₀ (by positivity)]; linarith

lemma list_measure_sum_apply {α : Type*} [MeasurableSpace α] (L : List (Measure α)) (s : Set α) :
    L.sum s = (L.map fun μ => μ s).sum := by
  induction L with
  | nil => simp
  | cons μ L ih => simp [ih]

lemma rho_apply (s : Set ℝ) :
    rho s = (table1.map fun e => ENNReal.ofReal (tc e) * arcsine (ta e) (tb e) s).sum := by
  unfold rho
  rw [list_measure_sum_apply, List.map_map]
  rfl

lemma ofReal_list_sum (L : List ℝ) (hL : ∀ x ∈ L, 0 ≤ x) :
    (L.map ENNReal.ofReal).sum = ENNReal.ofReal L.sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)),
      ENNReal.ofReal_add (hL x List.mem_cons_self)
        (List.sum_nonneg fun y hy => hL y (List.mem_cons_of_mem _ hy))]

theorem rho_univ : rho univ = ENNReal.ofReal Lim.lam := by
  rw [rho_apply]
  have : (table1.map fun e => ENNReal.ofReal (tc e) * arcsine (ta e) (tb e) univ) =
      (table1.map tc).map ENNReal.ofReal := by
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    rw [arcsine_univ _ _ (table1_ab e he).2.1, mul_one]
    rfl
  rw [this, ofReal_list_sum _ (by
    intro x hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    unfold tc; positivity)]
  congr 1
  simp [table1, tc, Lim.lam]
  norm_num

theorem rho_compl : rho (Ioo 0 2)ᶜ = 0 := by
  rw [rho_apply]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h0, hab, h2⟩ := table1_ab e he
  have : arcsine (ta e) (tb e) (Ioo 0 2)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (Ioo_subset_Ioo h0.le h2.le)) (arcsine_compl _ _)
  rw [this, mul_zero]


namespace L61

open Complex in
/-- Joukowski: `‖E - w‖·‖E - w̄‖ = 2‖w‖·|x - cos θ|` for `E = e^{iθ}`, `w² + 1 = 2xw`. -/
lemma joukowski (x θ : ℝ) (w : ℂ) (hw : w ^ 2 + 1 = 2 * x * w) :
    ‖circleMap 0 1 θ - w‖ * ‖circleMap 0 1 θ - (starRingEnd ℂ) w‖ =
      2 * ‖w‖ * |x - Real.cos θ| := by
  set E := circleMap 0 1 θ with hE
  have hE' : E = exp (θ * I) := by rw [hE, circleMap_zero]; simp
  have h1 : E * (starRingEnd ℂ) E = 1 := by
    rw [mul_conj, hE', normSq_eq_norm_sq, norm_exp_ofReal_mul_I]; simp
  have h2 : E + (starRingEnd ℂ) E = 2 * (Real.cos θ : ℂ) := by
    rw [add_conj, hE', exp_ofReal_mul_I_re]; push_cast; ring
  have key : (E - w) * ((starRingEnd ℂ) E - w) = 2 * w * ((x : ℂ) - (Real.cos θ : ℂ)) := by
    linear_combination h1 - w * h2 + hw
  have hn : ‖E - (starRingEnd ℂ) w‖ = ‖(starRingEnd ℂ) E - w‖ := by
    rw [← Complex.norm_conj, map_sub, conj_conj]
  rw [hn, ← norm_mul, key, norm_mul, norm_mul, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  simp

/-- Points of `[0, 2π]` where `cos θ = x`. -/
lemma cos_eq_mem (x θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * Real.pi) (hc : Real.cos θ = x) :
    θ ∈ ({Real.arccos x, 2 * Real.pi - Real.arccos x} : Set ℝ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases le_or_gt θ Real.pi with h | h
  · left; rw [← hc, Real.arccos_cos h0 h]
  · right
    have : Real.arccos x = 2 * Real.pi - θ := by
      rw [← hc, ← Real.cos_two_pi_sub, Real.arccos_cos (by linarith) (by linarith)]
    linarith

lemma ae_not_mem_pair (x : ℝ) :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({Real.arccos x, 2 * Real.pi - Real.arccos x} : Set ℝ) :=
  measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).measure_zero _)

/-- The full-period integral of `log|x - cos θ|`. -/
lemma log_cos_integral (x : ℝ) (w : ℂ) (hw : w ^ 2 + 1 = 2 * x * w) (hw1 : 1 ≤ ‖w‖) :
    IntervalIntegrable (fun θ => Real.log |x - Real.cos θ|) volume 0 (2 * Real.pi) ∧
      ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log |x - Real.cos θ| =
        2 * Real.pi * (Real.log ‖w‖ - Real.log 2) := by
  have hw0 : 0 < ‖w‖ := by linarith
  set A : ℝ → ℝ := fun θ => Real.log ‖circleMap 0 1 θ - w‖
  set B : ℝ → ℝ := fun θ => Real.log ‖circleMap 0 1 θ - (starRingEnd ℂ) w‖
  have hA : IntervalIntegrable A volume 0 (2 * Real.pi) :=
    circleIntegrable_log_norm_sub_const (a := w) (c := 0) 1
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) :=
    circleIntegrable_log_norm_sub_const (a := (starRingEnd ℂ) w) (c := 0) 1
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc 0 (2 * Real.pi) →
      Real.log |x - Real.cos θ| = A θ + B θ - (Real.log 2 + Real.log ‖w‖) := by
    filter_upwards [ae_not_mem_pair x] with θ hθ hI
    rw [uIoc_of_le (by positivity)] at hI
    have hc : Real.cos θ ≠ x := fun hc => hθ (cos_eq_mem x θ hI.1.le hI.2 hc)
    have hne : |x - Real.cos θ| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hc))
    have hJ := joukowski x θ w hw
    have hprod : ‖circleMap 0 1 θ - w‖ * ‖circleMap 0 1 θ - (starRingEnd ℂ) w‖ ≠ 0 := by
      rw [hJ]; positivity
    have hA0 : ‖circleMap 0 1 θ - w‖ ≠ 0 := left_ne_zero_of_mul hprod
    have hB0 : ‖circleMap 0 1 θ - (starRingEnd ℂ) w‖ ≠ 0 := right_ne_zero_of_mul hprod
    have : |x - Real.cos θ| =
        ‖circleMap 0 1 θ - w‖ * ‖circleMap 0 1 θ - (starRingEnd ℂ) w‖ / (2 * ‖w‖) := by
      rw [hJ]; field_simp
    simp only [A, B]
    rw [this, Real.log_div hprod (by positivity), Real.log_mul hA0 hB0,
      Real.log_mul (by norm_num) hw0.ne']
  have hg : IntervalIntegrable (fun θ => A θ + B θ - (Real.log 2 + Real.log ‖w‖)) volume 0
      (2 * Real.pi) := (hA.add hB).sub intervalIntegrable_const
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff] at hg ⊢
    refine hg.congr_fun_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with θ h hI using (h hI).symm
  · rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_sub (hA.add hB)
      intervalIntegrable_const, intervalIntegral.integral_add hA hB]
    have eA : ∫ θ in (0 : ℝ)..2 * Real.pi, A θ = 2 * Real.pi * Real.log ‖w‖ := by
      have := circleAverage_log_norm_sub_const_eq_posLog (a := w)
      rw [Real.circleAverage_def, Real.posLog_eq_log (by rw [abs_of_pos hw0]; exact hw1)] at this
      rw [← this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have eB : ∫ θ in (0 : ℝ)..2 * Real.pi, B θ = 2 * Real.pi * Real.log ‖w‖ := by
      have := circleAverage_log_norm_sub_const_eq_posLog (a := (starRingEnd ℂ) w)
      rw [Real.circleAverage_def, Complex.norm_conj,
        Real.posLog_eq_log (by rw [abs_of_pos hw0]; exact hw1)] at this
      rw [← this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rw [eA, eB, intervalIntegral.integral_const, smul_eq_mul]
    ring

end L61

namespace L61

/-- Half period: `∫_{(0,π)} log|x - cos θ| dθ = π(log‖w‖ - log 2)`. -/
lemma log_cos_half (x : ℝ) (w : ℂ) (hw : w ^ 2 + 1 = 2 * x * w) (hw1 : 1 ≤ ‖w‖) :
    IntegrableOn (fun θ => Real.log |x - Real.cos θ|) (Ioo 0 Real.pi) ∧
      ∫ θ in Ioo 0 Real.pi, Real.log |x - Real.cos θ| = Real.pi * (Real.log ‖w‖ - Real.log 2) := by
  obtain ⟨hint, hval⟩ := log_cos_integral x w hw hw1
  set f : ℝ → ℝ := fun θ => Real.log |x - Real.cos θ| with hf
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have h1 : IntervalIntegrable f volume 0 Real.pi :=
    hint.mono_set (by rw [Set.uIcc_of_le hπ, Set.uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable f volume Real.pi (2 * Real.pi) :=
    hint.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]; exact Icc_subset_Icc hπ le_rfl)
  have hsym : ∫ θ in Real.pi..2 * Real.pi, f θ = ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    have : ∀ θ, f θ = f (2 * Real.pi - θ) := fun θ => by simp [hf, Real.cos_two_pi_sub]
    rw [intervalIntegral.integral_congr (fun θ _ => this θ), intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, hsym] at hval
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hπ] at h1
    exact h1
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπ]
    linarith

/-- A Joukowski parameter for every real `x`. -/
lemma exists_w (x : ℝ) : ∃ w : ℂ, w ^ 2 + 1 = 2 * x * w ∧ 1 ≤ ‖w‖ ∧
    ‖w‖ = if |x| ≤ 1 then 1 else |x| + Real.sqrt (x ^ 2 - 1) := by
  by_cases hx : |x| ≤ 1
  · have hs : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx]
    set s := Real.sqrt (1 - x ^ 2)
    have hs2 : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hs
    refine ⟨x + s * Complex.I, ?_, ?_, ?_⟩
    · have : ((s : ℂ)) ^ 2 = 1 - (x : ℂ) ^ 2 := by exact_mod_cast hs2
      linear_combination (-1 : ℂ) * this + (s : ℂ) ^ 2 * Complex.I_sq
    all_goals rw [Complex.norm_add_mul_I, hs2, show x ^ 2 + (1 - x ^ 2) = 1 by ring, Real.sqrt_one]
    · simp [hx]
  · push Not at hx
    have hx2 : 0 ≤ x ^ 2 - 1 := by nlinarith [one_lt_sq_iff_one_lt_abs x |>.2 hx]
    set s := Real.sqrt (x ^ 2 - 1)
    have hs2 : s ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hx2
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx
      refine ⟨((x + s : ℝ) : ℂ), ?_, ?_, ?_⟩
      · have : ((x + s) ^ 2 + 1 : ℝ) = 2 * x * (x + s) := by nlinarith
        exact_mod_cast this
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), if_neg (by
          rw [abs_of_nonneg h0]; linarith), abs_of_nonneg h0]
    · rw [abs_of_neg h0] at hx
      refine ⟨((x - s : ℝ) : ℂ), ?_, ?_, ?_⟩
      · have : ((x - s) ^ 2 + 1 : ℝ) = 2 * x * (x - s) := by nlinarith
        exact_mod_cast this
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), if_neg (by
          rw [abs_of_neg h0]; linarith), abs_of_neg h0]
        ring

end L61

/-- (A.1): the potential of the unit arcsine measure. -/
theorem arcsine_potential' (a b t : ℝ) (hab : a < b) :
    logPot (arcsine a b) t =
      if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
      else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2) := by
  set r := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set y := ((a + b) / 2 - t) / r with hy
  obtain ⟨w, hw, hw1, hwn⟩ := exists_w y
  obtain ⟨hint, hval⟩ := log_cos_half y w hw hw1
  have hπ := Real.pi_pos
  have hae : ∀ᵐ θ ∂(volume.restrict (Ioo 0 Real.pi)),
      Real.log |t - phi a b θ| = Real.log r + Real.log |y - Real.cos θ| := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [ae_not_mem_pair y] with θ hθ hI
    have hc : Real.cos θ ≠ y := fun hc => hθ (cos_eq_mem y θ hI.1.le (by linarith [hI.2]) hc)
    have hne : |y - Real.cos θ| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hc))
    have : |t - phi a b θ| = r * |y - Real.cos θ| := by
      rw [show t - phi a b θ = -(r * (y - Real.cos θ)) by
        unfold phi; rw [hy]; field_simp; ring, abs_neg, abs_mul, abs_of_pos hr0]
    rw [this, Real.log_mul hr0.ne' hne]
  unfold logPot
  rw [integral_arcsine a b hab, integral_congr_ae hae, integral_add (integrable_const _) hint, hval, setIntegral_const, Real.volume_real_Ioo_of_le hπ.le, sub_zero, smul_eq_mul]
  have hform : 1 / Real.pi * (Real.pi * Real.log r + Real.pi * (Real.log ‖w‖ - Real.log 2)) =
      Real.log r + Real.log ‖w‖ - Real.log 2 := by
    field_simp; ring
  rw [hform]
  have hiff : (a ≤ t ∧ t ≤ b) ↔ |y| ≤ 1 := by
    rw [hy, abs_div, abs_of_pos hr0, div_le_one hr0, abs_le, hr]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [if_pos h, hwn, if_pos (hiff.1 h), Real.log_one, add_zero, ← Real.log_div hr0.ne' (by norm_num),
      hr]
    ring_nf
  · rw [if_neg h, hwn, if_neg (fun h' => h (hiff.2 h'))]
    have hy1 : 1 < |y| := by
      by_contra h'; exact h (hiff.2 (not_lt.1 h'))
    have hsq : 0 ≤ y ^ 2 - 1 := by nlinarith [one_lt_sq_iff_one_lt_abs y |>.2 hy1]
    have hpos : 0 < |y| + Real.sqrt (y ^ 2 - 1) := by positivity
    have key : r * (|y| + Real.sqrt (y ^ 2 - 1)) =
        |t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b)) := by
      have e1 : r * |y| = |t - (a + b) / 2| := by
        rw [show r * |y| = |r * y| by rw [abs_mul, abs_of_pos hr0], hy,
          mul_div_cancel₀ _ hr0.ne', abs_sub_comm]
      have e2 : r * Real.sqrt (y ^ 2 - 1) = Real.sqrt ((t - a) * (t - b)) := by
        rw [← Real.sqrt_sq hr0.le, ← Real.sqrt_mul (sq_nonneg _)]
        congr 1
        have hr' : r ≠ 0 := hr0.ne'
        rw [hy]; field_simp; rw [hr]; ring
      rw [mul_add, e1, e2]
    rw [← key, Real.log_div (show r * (|y| + Real.sqrt (y ^ 2 - 1)) ≠ 0 by positivity)
      (by norm_num : (2 : ℝ) ≠ 0), Real.log_mul hr0.ne' hpos.ne']

theorem arcsine_potential_eq (a b t : ℝ) (hab : a < b) :
    logPot (arcsine a b) t =
      if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
      else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2) :=
  arcsine_potential' a b t hab

/-! ## (A.2): the energy -/

namespace L61

def ent (j : ℕ) : ℕ × ℕ × ℕ := table1.getD j (0, 0, 0)
def A (j : ℕ) : ℝ := ta (ent j)
def B (j : ℕ) : ℝ := tb (ent j)
def Cc (j : ℕ) : ℝ := tc (ent j)

lemma rho_eq : rho = ∑ j ∈ range 16, ENNReal.ofReal (Cc j) • arcsine (A j) (B j) := by
  simp only [rho, table1, Finset.sum_range_succ, Finset.sum_range_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Cc, A, B, ent, ta, tb, tc]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, zero_add, add_zero]
  abel

lemma nested_nat : ∀ j < 16, ∀ k < 16, j ≤ k →
    (ent k).1 ≤ (ent j).1 ∧ (ent j).2.1 ≤ (ent k).2.1 := by
  decide

lemma ent_ab : ∀ j < 16, 0 < (ent j).1 ∧ (ent j).1 < (ent j).2.1 ∧ (ent j).2.1 < 2 * 10 ^ 12 := by
  decide

lemma AB (j : ℕ) (hj : j < 16) : 0 < A j ∧ A j < B j ∧ B j < 2 := by
  obtain ⟨h1, h2, h3⟩ := ent_ab j hj
  unfold A B ta tb
  refine ⟨by have : (0 : ℝ) < (ent j).1 := by exact_mod_cast h1
             positivity, ?_, ?_⟩
  · have : ((ent j).1 : ℝ) < (ent j).2.1 := by exact_mod_cast h2
    exact div_lt_div_of_pos_right this (by positivity)
  · have : ((ent j).2.1 : ℝ) < 2 * 10 ^ 12 := by exact_mod_cast h3
    rw [div_lt_iff₀ (by positivity)]; linarith

lemma nested (j k : ℕ) (hj : j < 16) (hk : k < 16) (hjk : j ≤ k) : A k ≤ A j ∧ B j ≤ B k := by
  obtain ⟨h1, h2⟩ := nested_nat j hj k hk hjk
  unfold A B ta tb
  constructor
  · have : ((ent k).1 : ℝ) ≤ (ent j).1 := by exact_mod_cast h1
    exact div_le_div_of_nonneg_right this (by positivity)
  · have : ((ent j).2.1 : ℝ) ≤ (ent k).2.1 := by exact_mod_cast h2
    exact div_le_div_of_nonneg_right this (by positivity)

lemma Cc_nonneg (j : ℕ) : 0 ≤ Cc j := by unfold Cc tc; positivity

end L61

instance arcsine_isFinite (a b : ℝ) : IsFiniteMeasure (arcsine a b) := by
  rcases lt_or_ge a b with h | h
  · exact ⟨by rw [arcsine_univ a b h]; exact ENNReal.one_lt_top⟩
  · have : arcsine a b = 0 := by
      unfold arcsine
      rw [Ioo_eq_empty (not_lt.2 h), Measure.restrict_empty, withDensity_zero_left]
    rw [this]; infer_instance

/-- Integrability against the arcsine measure via the angle variable. -/
theorem integrable_arcsine (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun θ => f (phi a b θ)) (Ioo 0 Real.pi)) : Integrable f (arcsine a b) := by
  unfold arcsine
  have hmeas : Measurable fun t : ℝ => (1 / (Real.pi * Real.sqrt ((t - a) * (b - t)))).toNNReal := by
    fun_prop
  rw [show (fun t : ℝ => ENNReal.ofReal (1 / (Real.pi * Real.sqrt ((t - a) * (b - t))))) =
      fun t => ((1 / (Real.pi * Real.sqrt ((t - a) * (b - t)))).toNNReal : ENNReal) from rfl,
    integrable_withDensity_iff_integrable_smul hmeas]
  change IntegrableOn _ (Ioo a b)
  rw [← phi_image a b hab, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => phi_hasDeriv a b θ) (phi_injOn a b hab)]
  refine IntegrableOn.congr_fun (show IntegrableOn (fun θ => 1 / Real.pi * f (phi a b θ))
    (Ioo 0 Real.pi) volume from hf.const_mul (1 / Real.pi)) (fun θ hθ => ?_) measurableSet_Ioo
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (by positivity), ← mul_assoc, density_phi a b θ hab hθ]

theorem integrable_log_arcsine (a b t : ℝ) (hab : a < b) :
    Integrable (fun u => Real.log |t - u|) (arcsine a b) := by
  apply integrable_arcsine a b hab
  set r := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set y := ((a + b) / 2 - t) / r with hy
  obtain ⟨w, hw, hw1, -⟩ := L61.exists_w y
  obtain ⟨hint, -⟩ := L61.log_cos_half y w hw hw1
  refine Integrable.congr (show IntegrableOn (fun θ => Real.log r + Real.log |y - Real.cos θ|)
    (Ioo 0 Real.pi) volume from (integrable_const (Real.log r)).add hint) ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [L61.ae_not_mem_pair y] with θ hθ hI
  have hc : Real.cos θ ≠ y := fun hc =>
    hθ (L61.cos_eq_mem y θ hI.1.le (by linarith [hI.2, Real.pi_pos]) hc)
  have hne : |y - Real.cos θ| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hc))
  have : |t - phi a b θ| = r * |y - Real.cos θ| := by
    rw [show t - phi a b θ = -(r * (y - Real.cos θ)) by
      unfold phi; rw [hy]; field_simp; ring, abs_neg, abs_mul, abs_of_pos hr0]
  rw [this, Real.log_mul hr0.ne' hne]

namespace L61

/-- The potential of the `k`-th component and its value on its interval. -/
def Uk (k : ℕ) (t : ℝ) : ℝ := logPot (arcsine (A k) (B k)) t
def Lk (k : ℕ) : ℝ := Real.log ((B k - A k) / 4)

lemma ae_mem_Ioo (a b : ℝ) : ∀ᵐ t ∂(arcsine a b), t ∈ Ioo a b := by
  rw [ae_iff]
  exact arcsine_compl a b

lemma arcsine_real_univ (a b : ℝ) (hab : a < b) : (arcsine a b).real univ = 1 := by
  rw [measureReal_def, arcsine_univ a b hab]; rfl

lemma Uk_eq (k : ℕ) (hk : k < 16) (t : ℝ) : Uk k t =
    if A k ≤ t ∧ t ≤ B k then Lk k
    else Real.log ((|t - (A k + B k) / 2| + Real.sqrt ((t - A k) * (t - B k))) / 2) :=
  arcsine_potential' _ _ t (AB k hk).2.1

lemma Uk_const (k : ℕ) (hk : k < 16) (t : ℝ) (ht : t ∈ Icc (A k) (B k)) : Uk k t = Lk k := by
  rw [Uk_eq k hk, if_pos (show A k ≤ t ∧ t ≤ B k from ht)]

lemma Uk_measurable (k : ℕ) (hk : k < 16) : Measurable (Uk k) := by
  have : Uk k = fun t => if A k ≤ t ∧ t ≤ B k then Lk k
      else Real.log ((|t - (A k + B k) / 2| + Real.sqrt ((t - A k) * (t - B k))) / 2) :=
    funext (Uk_eq k hk)
  rw [this]
  exact Measurable.ite (measurableSet_Icc (a := A k) (b := B k)) measurable_const (by fun_prop)

lemma Uk_bounds (k : ℕ) (hk : k < 16) (t : ℝ) (ht : t ∈ Set.Ioo 0 2) :
    Lk k ≤ Uk k t ∧ Uk k t ≤ Real.log 2 := by
  obtain ⟨h0, hab, h2⟩ := AB k hk
  have hL : Lk k ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  rw [Uk_eq k hk]
  split_ifs with h
  · exact ⟨le_rfl, hL⟩
  · set m := (A k + B k) / 2
    set r := (B k - A k) / 2
    have hout : r < |t - m| := by
      rw [lt_abs]
      by_cases h1 : A k ≤ t
      · left; have : B k < t := by by_contra h3; exact h ⟨h1, not_lt.1 h3⟩
        simp only [m, r]; linarith
      · right; simp only [m, r]; linarith
    have hprod : (t - A k) * (t - B k) = (t - m) ^ 2 - r ^ 2 := by simp only [m, r]; ring
    have hsq : Real.sqrt ((t - A k) * (t - B k)) ≤ |t - m| := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
    have hsq0 := Real.sqrt_nonneg ((t - A k) * (t - B k))
    have hm2 : |t - m| < 2 := by rw [abs_lt]; simp only [m]; constructor <;> linarith [ht.1, ht.2]
    have hr0 : 0 < r := by simp only [r]; linarith
    constructor
    · show Real.log ((B k - A k) / 4) ≤ _
      exact Real.log_le_log (by linarith) (by simp only [r] at hout; linarith)
    · exact Real.log_le_log (by linarith) (by linarith)

lemma abs_log_le (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 2) :
    |Real.log v| ≤ 2 * Real.log 2 - Real.log v := by
  have hl : Real.log v ≤ Real.log 2 := by
    rcases hv0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
    · exact Real.log_le_log h hv
  have h2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [abs_le]; constructor <;> linarith

lemma Uk_integrable (j k : ℕ) (hj : j < 16) (hk : k < 16) :
    Integrable (Uk k) (arcsine (A j) (B j)) := by
  obtain ⟨h0, hab, h2⟩ := AB j hj
  refine Integrable.mono' (integrable_const (|Lk k| + Real.log 2))
    (Uk_measurable k hk).aestronglyMeasurable ?_
  filter_upwards [ae_mem_Ioo (A j) (B j)] with t ht
  have := Uk_bounds k hk t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (Lk k), le_abs_self (Lk k)]

lemma log_prod_integrable (j k : ℕ) (hj : j < 16) (hk : k < 16) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((arcsine (A j) (B j)).prod (arcsine (A k) (B k))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((arcsine (A j) (B j)).prod (arcsine (A k) (B k))) := by
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.log |p.1 - p.2|).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  obtain ⟨hj0, hjab, hj2⟩ := AB j hj
  obtain ⟨hk0, hkab, hk2⟩ := AB k hk
  refine ⟨Filter.Eventually.of_forall fun x => integrable_log_arcsine _ _ x hkab, ?_⟩
  refine Integrable.mono' (integrable_const (2 * Real.log 2 - Lk k))
    hm.norm.integral_prod_right' ?_
  filter_upwards [ae_mem_Ioo (A j) (B j)] with x hx
  have hx2 : x ∈ Set.Ioo 0 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hint := integrable_log_arcsine (A k) (B k) x hkab
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  calc ∫ y, ‖Real.log |x - y|‖ ∂(arcsine (A k) (B k))
      ≤ ∫ y, (2 * Real.log 2 - Real.log |x - y|) ∂(arcsine (A k) (B k)) := by
        refine integral_mono_ae hint.norm ((integrable_const _).sub hint) ?_
        filter_upwards [ae_mem_Ioo (A k) (B k)] with y hy
        rw [Real.norm_eq_abs]
        exact abs_log_le _ (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2, hx2.1, hx2.2])
    _ = 2 * Real.log 2 - Uk k x := by
        rw [integral_sub (integrable_const _) hint, integral_const, arcsine_real_univ _ _ hkab,
          one_smul]
        rfl
    _ ≤ 2 * Real.log 2 - Lk k := by linarith [(Uk_bounds k hk x hx2).1]

lemma Uk_swap (j k : ℕ) (hj : j < 16) (hk : k < 16) :
    ∫ x, Uk k x ∂(arcsine (A j) (B j)) = ∫ y, Uk j y ∂(arcsine (A k) (B k)) := by
  unfold Uk logPot
  rw [integral_integral_swap (f := fun x y => Real.log |x - y|) (log_prod_integrable j k hj hk)]
  simp_rw [abs_sub_comm]

lemma Uk_integral (j k : ℕ) (hj : j < 16) (hk : k < 16) :
    ∫ x, Uk k x ∂(arcsine (A j) (B j)) = Lk (max j k) := by
  rcases le_total j k with h | h
  · rw [max_eq_right h]
    obtain ⟨h1, h2⟩ := nested j k hj hk h
    rw [integral_congr_ae (g := fun _ => Lk k) ?_, integral_const,
      arcsine_real_univ _ _ (AB j hj).2.1, one_smul]
    filter_upwards [ae_mem_Ioo (A j) (B j)] with x hx
    exact Uk_const k hk x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [max_eq_left h, Uk_swap j k hj hk]
    obtain ⟨h1, h2⟩ := nested k j hk hj h
    rw [integral_congr_ae (g := fun _ => Lk j) ?_, integral_const,
      arcsine_real_univ _ _ (AB k hk).2.1, one_smul]
    filter_upwards [ae_mem_Ioo (A k) (B k)] with x hx
    exact Uk_const j hj x ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma logPot_rho (t : ℝ) : logPot rho t = ∑ k ∈ range 16, Cc k * Uk k t := by
  unfold logPot
  rw [rho_eq, integral_finset_sum_measure]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal (Cc_nonneg k), smul_eq_mul]
    rfl
  · intro k hk
    exact (integrable_log_arcsine _ _ t (AB k (Finset.mem_range.1 hk)).2.1).smul_measure
      ENNReal.ofReal_ne_top

lemma logEnergy_rho :
    logEnergy rho = ∑ j ∈ range 16, ∑ k ∈ range 16, Cc j * Cc k * Lk (max j k) := by
  unfold logEnergy
  simp_rw [logPot_rho]
  rw [rho_eq, integral_finset_sum_measure]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [integral_smul_measure, ENNReal.toReal_ofReal (Cc_nonneg j), smul_eq_mul,
      integral_finset_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [integral_const_mul, Uk_integral j k hj' (Finset.mem_range.1 hk)]
      ring
    · intro k hk
      exact (Uk_integrable j k hj' (Finset.mem_range.1 hk)).const_mul _
  · intro j hj
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    exact integrable_finset_sum _ fun k hk =>
      (Uk_integrable j k (Finset.mem_range.1 hj) (Finset.mem_range.1 hk)).const_mul _

/-- Regrouping `∑_{j,k} c_j c_k L_{max(j,k)}` by the maximum. -/
lemma sum_max_regroup (c L : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, ∑ k ∈ range n, c j * c k * L (max j k) =
      ∑ j ∈ range n, ((∑ i ∈ range (j + 1), c i) ^ 2 - (∑ i ∈ range j, c i) ^ 2) * L j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => ((∑ i ∈ range (j + 1), c i) ^ 2 -
      (∑ i ∈ range j, c i) ^ 2) * L j), ← ih]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    have e1 : ∑ j ∈ range n, c j * c n * L (max j n) = (∑ j ∈ range n, c j) * c n * L n := by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j hj => by rw [max_eq_right (Finset.mem_range.1 hj).le]
    have e2 : ∑ k ∈ range n, c n * c k * L (max n k) = c n * (∑ k ∈ range n, c k) * L n := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k hk => by rw [max_eq_left (Finset.mem_range.1 hk).le]
    rw [e1, e2, max_self]
    ring

end L61

namespace L61

lemma take_sum (g : ℕ × ℕ × ℕ → ℝ) (hg : g (0, 0, 0) = 0) :
    ∀ (L : List (ℕ × ℕ × ℕ)) (j : ℕ),
      ((L.take j).map g).sum = ∑ i ∈ range j, g (L.getD i (0, 0, 0))
  | L, 0 => by simp
  | [], j + 1 => by simp [hg]
  | x :: L, j + 1 => by
    rw [List.take_succ_cons, List.map_cons, List.sum_cons, take_sum g hg L j,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma Spart_eq (j : ℕ) : Spart j = ∑ i ∈ range j, Cc i := by
  unfold Spart
  rw [take_sum (fun e => (e.2.2 : ℝ) / 10 ^ 12) (by simp)]
  rfl

end L61

open L61 in
/-- (A.2). -/
theorem energy_A2' :
    logEnergy rho = ∑ j ∈ range 16,
      (Spart (j + 1) ^ 2 - Spart j ^ 2) *
        Real.log ((((table1.getD j (0, 0, 0)).2.1 : ℝ) - (table1.getD j (0, 0, 0)).1)
          / 10 ^ 12 / 4) := by
  rw [logEnergy_rho, sum_max_regroup Cc Lk 16]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Spart_eq, Spart_eq]
  congr 2
  unfold Lk A B ta tb ent
  ring_nf

/-! ## Rigorous logarithm enclosures (A.3) -/

namespace L61

/-- Partial sums of the atanh series. -/
def atS (z : ℝ) (m : ℕ) : ℝ := ∑ k ∈ range m, 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)

/-- (A.3): `S_m(z) ≤ log((1+z)/(1-z)) ≤ S_m(z) + 2z^{2m+1}/((2m+1)(1-z²))` for `0 ≤ z < 1`. -/
lemma log_series_bounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (m : ℕ) :
    atS z m ≤ Real.log ((1 + z) / (1 - z)) ∧
      Real.log ((1 + z) / (1 - z)) ≤ atS z m + 2 * z ^ (2 * m + 1) / ((2 * m + 1) * (1 - z ^ 2)) := by
  have hz : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hz
  rw [← Real.log_div (by linarith) (by linarith)] at hs
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  refine ⟨sum_le_hasSum (range m) (fun k _ => hf0 k) hs, ?_⟩
  have htail := (hasSum_nat_add_iff' m).2 hs
  have hq : z ^ 2 < 1 := by nlinarith
  have hgeom : HasSum (fun k : ℕ => 2 * z ^ (2 * m + 1) / (2 * m + 1) * (z ^ 2) ^ k)
      (2 * z ^ (2 * m + 1) / (2 * m + 1) * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hq).mul_left _
  have hle := hasSum_le (fun k => ?_) htail hgeom
  · have : atS z m = ∑ i ∈ range m, f i := rfl
    rw [this]
    have e : 2 * z ^ (2 * m + 1) / (2 * m + 1) * (1 - z ^ 2)⁻¹ =
        2 * z ^ (2 * m + 1) / ((2 * m + 1) * (1 - z ^ 2)) := by
      field_simp
    linarith
  · simp only [hf]
    have h1 : (1 : ℝ) / (2 * ((k + m : ℕ) : ℝ) + 1) ≤ 1 / (2 * m + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have h2 : z ^ (2 * (k + m) + 1) = z ^ (2 * m + 1) * (z ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [h2]
    have h3 : 0 ≤ z ^ (2 * m + 1) * (z ^ 2) ^ k := by positivity
    calc 2 * (1 / (2 * ((k + m : ℕ) : ℝ) + 1)) * (z ^ (2 * m + 1) * (z ^ 2) ^ k)
        ≤ 2 * (1 / (2 * m + 1)) * (z ^ (2 * m + 1) * (z ^ 2) ^ k) := by gcongr
      _ = _ := by ring

end L61

namespace L61

set_option maxHeartbeats 4000000 in
lemma log2_enc : (6931471805599453094172152 / 10 ^ 25 : ℝ) ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ 6931471805599453094172323 / 10 ^ 25 := by
  have h := log_series_bounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = (2 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 4000000 in
lemma logy_enc_0 : (2639034991761707930494974 / 10 ^ 25 : ℝ) ≤ Real.log (1017189489 / 781250000 : ℝ) ∧ Real.log (1017189489 / 781250000 : ℝ) ≤ 2639034991761707930494975 / 10 ^ 25 := by
  have h := log_series_bounds (235939489 / 1798439489 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (235939489 / 1798439489 : ℝ)) / (1 - (235939489 / 1798439489 : ℝ)) = (1017189489 / 781250000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_0 : Lk 0 = Real.log (1017189489 / 781250000 : ℝ) - 10 * Real.log 2 := by
  have : (B 0 - A 0) / 4 = (1017189489 / 781250000 : ℝ) / 2 ^ 10 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_1 : (5114334076167610199456728 / 10 ^ 25 : ℝ) ≤ Real.log (13028749591 / 7812500000 : ℝ) ∧ Real.log (13028749591 / 7812500000 : ℝ) ≤ 5114334076167610199456729 / 10 ^ 25 := by
  have h := log_series_bounds (5216249591 / 20841249591 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (5216249591 / 20841249591 : ℝ)) / (1 - (5216249591 / 20841249591 : ℝ)) = (13028749591 / 7812500000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_1 : Lk 1 = Real.log (13028749591 / 7812500000 : ℝ) - 9 * Real.log 2 := by
  have : (B 1 - A 1) / 4 = (13028749591 / 7812500000 : ℝ) / 2 ^ 9 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_2 : (4427514000489370722782089 / 10 ^ 25 : ℝ) ≤ Real.log (24327894059 / 15625000000 : ℝ) ∧ Real.log (24327894059 / 15625000000 : ℝ) ≤ 4427514000489370722782090 / 10 ^ 25 := by
  have h := log_series_bounds (8702894059 / 39952894059 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (8702894059 / 39952894059 : ℝ)) / (1 - (8702894059 / 39952894059 : ℝ)) = (24327894059 / 15625000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_2 : Lk 2 = Real.log (24327894059 / 15625000000 : ℝ) - 8 * Real.log 2 := by
  have : (B 2 - A 2) / 4 = (24327894059 / 15625000000 : ℝ) / 2 ^ 8 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_3 : (2722317986562477655062526 / 10 ^ 25 : ℝ) ≤ Real.log (4102785289 / 3125000000 : ℝ) ∧ Real.log (4102785289 / 3125000000 : ℝ) ≤ 2722317986562477655062527 / 10 ^ 25 := by
  have h := log_series_bounds (977785289 / 7227785289 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (977785289 / 7227785289 : ℝ)) / (1 - (977785289 / 7227785289 : ℝ)) = (4102785289 / 3125000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_3 : Lk 3 = Real.log (4102785289 / 3125000000 : ℝ) - 7 * Real.log 2 := by
  have : (B 3 - A 3) / 4 = (4102785289 / 3125000000 : ℝ) / 2 ^ 7 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_4 : (434102579263321756742153 / 10 ^ 25 : ℝ) ≤ Real.log (65272891657 / 62500000000 : ℝ) ∧ Real.log (65272891657 / 62500000000 : ℝ) ≤ 434102579263321756742154 / 10 ^ 25 := by
  have h := log_series_bounds (2772891657 / 127772891657 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (2772891657 / 127772891657 : ℝ)) / (1 - (2772891657 / 127772891657 : ℝ)) = (65272891657 / 62500000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_4 : Lk 4 = Real.log (65272891657 / 62500000000 : ℝ) - 6 * Real.log 2 := by
  have : (B 4 - A 4) / 4 = (65272891657 / 62500000000 : ℝ) / 2 ^ 6 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_5 : (4608086171046564701853377 / 10 ^ 25 : ℝ) ≤ Real.log (99084713271 / 62500000000 : ℝ) ∧ Real.log (99084713271 / 62500000000 : ℝ) ≤ 4608086171046564701853378 / 10 ^ 25 := by
  have h := log_series_bounds (36584713271 / 161584713271 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (36584713271 / 161584713271 : ℝ)) / (1 - (36584713271 / 161584713271 : ℝ)) = (99084713271 / 62500000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_5 : Lk 5 = Real.log (99084713271 / 62500000000 : ℝ) - 6 * Real.log 2 := by
  have : (B 5 - A 5) / 4 = (99084713271 / 62500000000 : ℝ) / 2 ^ 6 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_6 : (1417899108615240211499012 / 10 ^ 25 : ℝ) ≤ Real.log (144041816267 / 125000000000 : ℝ) ∧ Real.log (144041816267 / 125000000000 : ℝ) ≤ 1417899108615240211499013 / 10 ^ 25 := by
  have h := log_series_bounds (19041816267 / 269041816267 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (19041816267 / 269041816267 : ℝ)) / (1 - (19041816267 / 269041816267 : ℝ)) = (144041816267 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_6 : Lk 6 = Real.log (144041816267 / 125000000000 : ℝ) - 5 * Real.log 2 := by
  have : (B 6 - A 6) / 4 = (144041816267 / 125000000000 : ℝ) / 2 ^ 5 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_7 : (4744614610375889389052186 / 10 ^ 25 : ℝ) ≤ Real.log (200893556541 / 125000000000 : ℝ) ∧ Real.log (200893556541 / 125000000000 : ℝ) ≤ 4744614610375889389052187 / 10 ^ 25 := by
  have h := log_series_bounds (75893556541 / 325893556541 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (75893556541 / 325893556541 : ℝ)) / (1 - (75893556541 / 325893556541 : ℝ)) = (200893556541 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_7 : Lk 7 = Real.log (200893556541 / 125000000000 : ℝ) - 5 * Real.log 2 := by
  have : (B 7 - A 7) / 4 = (200893556541 / 125000000000 : ℝ) / 2 ^ 5 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_8 : (739227235165382858563697 / 10 ^ 25 : ℝ) ≤ Real.log (269180899217 / 250000000000 : ℝ) ∧ Real.log (269180899217 / 250000000000 : ℝ) ≤ 739227235165382858563698 / 10 ^ 25 := by
  have h := log_series_bounds (19180899217 / 519180899217 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (19180899217 / 519180899217 : ℝ)) / (1 - (19180899217 / 519180899217 : ℝ)) = (269180899217 / 250000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_8 : Lk 8 = Real.log (269180899217 / 250000000000 : ℝ) - 4 * Real.log 2 := by
  have : (B 8 - A 8) / 4 = (269180899217 / 250000000000 : ℝ) / 2 ^ 4 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_9 : (3277376495783627238092016 / 10 ^ 25 : ℝ) ≤ Real.log (21684762939 / 15625000000 : ℝ) ∧ Real.log (21684762939 / 15625000000 : ℝ) ≤ 3277376495783627238092017 / 10 ^ 25 := by
  have h := log_series_bounds (6059762939 / 37309762939 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (6059762939 / 37309762939 : ℝ)) / (1 - (6059762939 / 37309762939 : ℝ)) = (21684762939 / 15625000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_9 : Lk 9 = Real.log (21684762939 / 15625000000 : ℝ) - 4 * Real.log 2 := by
  have : (B 9 - A 9) / 4 = (21684762939 / 15625000000 : ℝ) / 2 ^ 4 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_10 : (5439396883934419370169222 / 10 ^ 25 : ℝ) ≤ Real.log (430695182301 / 250000000000 : ℝ) ∧ Real.log (430695182301 / 250000000000 : ℝ) ≤ 5439396883934419370169223 / 10 ^ 25 := by
  have h := log_series_bounds (180695182301 / 680695182301 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (180695182301 / 680695182301 : ℝ)) / (1 - (180695182301 / 680695182301 : ℝ)) = (430695182301 / 250000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_10 : Lk 10 = Real.log (430695182301 / 250000000000 : ℝ) - 4 * Real.log 2 := by
  have : (B 10 - A 10) / 4 = (430695182301 / 250000000000 : ℝ) / 2 ^ 4 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_11 : (304623689623510702107029 / 10 ^ 25 : ℝ) ≤ Real.log (128866386789 / 125000000000 : ℝ) ∧ Real.log (128866386789 / 125000000000 : ℝ) ≤ 304623689623510702107030 / 10 ^ 25 := by
  have h := log_series_bounds (3866386789 / 253866386789 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (3866386789 / 253866386789 : ℝ)) / (1 - (3866386789 / 253866386789 : ℝ)) = (128866386789 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_11 : Lk 11 = Real.log (128866386789 / 125000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 11 - A 11) / 4 = (128866386789 / 125000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_12 : (1745631428282761730092773 / 10 ^ 25 : ℝ) ≤ Real.log (595362962907 / 500000000000 : ℝ) ∧ Real.log (595362962907 / 500000000000 : ℝ) ≤ 1745631428282761730092774 / 10 ^ 25 := by
  have h := log_series_bounds (95362962907 / 1095362962907 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (95362962907 / 1095362962907 : ℝ)) / (1 - (95362962907 / 1095362962907 : ℝ)) = (595362962907 / 500000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_12 : Lk 12 = Real.log (595362962907 / 500000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 12 - A 12) / 4 = (595362962907 / 500000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_13 : (2839190749069400025615562 / 10 ^ 25 : ℝ) ≤ Real.log (166040678943 / 125000000000 : ℝ) ∧ Real.log (166040678943 / 125000000000 : ℝ) ≤ 2839190749069400025615563 / 10 ^ 25 := by
  have h := log_series_bounds (41040678943 / 291040678943 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (41040678943 / 291040678943 : ℝ)) / (1 - (41040678943 / 291040678943 : ℝ)) = (166040678943 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_13 : Lk 13 = Real.log (166040678943 / 125000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 13 - A 13) / 4 = (166040678943 / 125000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_14 : (3591927980478393943451068 / 10 ^ 25 : ℝ) ≤ Real.log (716086447547 / 500000000000 : ℝ) ∧ Real.log (716086447547 / 500000000000 : ℝ) ≤ 3591927980478393943451069 / 10 ^ 25 := by
  have h := log_series_bounds (216086447547 / 1216086447547 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (216086447547 / 1216086447547 : ℝ)) / (1 - (216086447547 / 1216086447547 : ℝ)) = (716086447547 / 500000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_14 : Lk 14 = Real.log (716086447547 / 500000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 14 - A 14) / 4 = (716086447547 / 500000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_15 : (4008753303197060018486061 / 10 ^ 25 : ℝ) ≤ Real.log (746565554359 / 500000000000 : ℝ) ∧ Real.log (746565554359 / 500000000000 : ℝ) ≤ 4008753303197060018486062 / 10 ^ 25 := by
  have h := log_series_bounds (246565554359 / 1246565554359 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (246565554359 / 1246565554359 : ℝ)) / (1 - (246565554359 / 1246565554359 : ℝ)) = (746565554359 / 500000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_15 : Lk 15 = Real.log (746565554359 / 500000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 15 - A 15) / 4 = (746565554359 / 500000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma log65_enc : (1823215567939546262117180 / 10 ^ 25 : ℝ) ≤ Real.log (6 / 5 : ℝ) ∧ Real.log (6 / 5 : ℝ) ≤ 1823215567939546262117181 / 10 ^ 25 := by
  have h := log_series_bounds (1 / 11 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (1 / 11 : ℝ)) / (1 - (1 / 11 : ℝ)) = (6 / 5 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 4000000 in
lemma log3720_enc : (6151856390902334509328719 / 10 ^ 25 : ℝ) ≤ Real.log (37 / 20 : ℝ) ∧ Real.log (37 / 20 : ℝ) ≤ 6151856390902334509328721 / 10 ^ 25 := by
  have h := log_series_bounds (17 / 57 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (17 / 57 : ℝ)) / (1 - (17 / 57 : ℝ)) = (37 / 20 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma logEnergy_enc :
    -2126593445148 / 10 ^ 12 < logEnergy rho ∧ logEnergy rho < -2126593445147 / 10 ^ 12 := by
  rw [logEnergy_rho, sum_max_regroup Cc Lk 16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lk_0, Lk_1, Lk_2, Lk_3, Lk_4, Lk_5, Lk_6, Lk_7, Lk_8, Lk_9, Lk_10, Lk_11, Lk_12, Lk_13, Lk_14, Lk_15, Cc, tc, ent, table1]
  norm_num
  constructor <;> linarith [logy_enc_0.1, logy_enc_0.2, logy_enc_1.1, logy_enc_1.2, logy_enc_2.1, logy_enc_2.2, logy_enc_3.1, logy_enc_3.2, logy_enc_4.1, logy_enc_4.2, logy_enc_5.1, logy_enc_5.2, logy_enc_6.1, logy_enc_6.2, logy_enc_7.1, logy_enc_7.2, logy_enc_8.1, logy_enc_8.2, logy_enc_9.1, logy_enc_9.2, logy_enc_10.1, logy_enc_10.2, logy_enc_11.1, logy_enc_11.2, logy_enc_12.1, logy_enc_12.2, logy_enc_13.1, logy_enc_13.2, logy_enc_14.1, logy_enc_14.2, logy_enc_15.1, logy_enc_15.2, log2_enc.1, log2_enc.2]

lemma Cstar_enc : 2653035990340 / 10 ^ 12 < Cstar ∧ Cstar < 2653035990341 / 10 ^ 12 := by
  have ha : Real.log Lim.α = Real.log (6 / 5 : ℝ) - 4 * Real.log 2 := by
    rw [show Lim.α = (6 / 5 : ℝ) / 2 ^ 4 by norm_num [Lim.α], Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have hl : 2 * Lim.lam = (37 / 20 : ℝ) := by norm_num [Lim.lam]
  unfold Cstar
  rw [ha, hl]
  norm_num [Lim.α, Lim.lam]
  constructor <;> nlinarith [log65_enc.1, log65_enc.2, log3720_enc.1, log3720_enc.2, log2_enc.1, log2_enc.2]

end L61

/-- (A.10). -/
theorem enclosures_A10' :
    -2126593445148 / 10 ^ 12 < logEnergy rho ∧ logEnergy rho < -2126593445147 / 10 ^ 12 ∧
      2653035990340 / 10 ^ 12 < Cstar ∧ Cstar < 2653035990341 / 10 ^ 12 :=
  ⟨L61.logEnergy_enc.1, L61.logEnergy_enc.2, L61.Cstar_enc.1, L61.Cstar_enc.2⟩

/-- (6.4). -/
theorem energy_6_4 : Lim.lam * M0 - logEnergy rho + Cstar ≤ U := by
  obtain ⟨h1, -, -, h4⟩ := enclosures_A10'
  have := A10_combination
  have e : ((Lim.lam : ℝ) * (M0 : ℝ)) = ((lam * M0 : ℚ) : ℝ) := by
    push_cast; norm_num [Lim.lam, lam]
  have hU : ((-1366995564511 / 10 ^ 12 : ℚ) : ℝ) < (U : ℝ) := by exact_mod_cast this.2
  have hc : ((lam * M0 : ℚ) : ℝ) + 2126593445148 / 10 ^ 12 + 2653035990341 / 10 ^ 12 =
      -1366995564511 / 10 ^ 12 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) this.1
    push_cast at this ⊢; linarith
  push_cast at hU
  linarith
end Zeta5
