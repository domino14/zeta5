import Zeta5.Section6
import Zeta5.Energy6
import Zeta5.Lemma61Final

/-!
# (6.9): the bound for every configuration

We regularize the configuration by circle measures `ω_i` of radius `ε = 1/(4K²)` around the
points `t_i`, apply Lemma 6.2 (`lemma_6_2'`) to `σ = K⁻¹ ∑ ω_i` and `ρ`, and use the circle
average `⨍ log|z - a| = log max(ε, |c - a|)` (Mathlib). The only property of `ρ` used beyond
Lemma 6.1 is the arcsine mass bound `ρ([x - r, x + r]) ≤ 40√r`, proved from the density.
-/

open Finset MeasureTheory Set Real

noncomputable section

namespace Zeta5
namespace C69

/-! ## The arcsine mass bound -/

/-- `φ(v) = v^{-1/2}` for `v > 0`, and `0` for `v ≤ 0`. -/
def phi (v : ℝ) : ℝ := (max v 0) ^ (-(1 / 2 : ℝ))

lemma phi_nonneg (v : ℝ) : 0 ≤ phi v := Real.rpow_nonneg (le_max_right _ _) _

lemma phi_of_nonpos {v : ℝ} (hv : v ≤ 0) : phi v = 0 := by
  simp [phi, max_eq_right hv]

lemma phi_of_nonneg {v : ℝ} (hv : 0 ≤ v) : phi v = v ^ (-(1 / 2 : ℝ)) := by
  simp [phi, max_eq_left hv]

lemma phi_of_pos {v : ℝ} (hv : 0 < v) : phi v = 1 / √v := by
  rw [phi_of_nonneg hv.le, Real.rpow_neg hv.le, Real.sqrt_eq_rpow]
  exact (one_div _).symm

lemma integral_rpow_half {p q : ℝ} :
    ∫ v in p..q, v ^ (-(1 / 2 : ℝ)) = 2 * (q ^ (1 / 2 : ℝ) - p ^ (1 / 2 : ℝ)) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

lemma phi_ii_zero (q : ℝ) : IntervalIntegrable phi volume 0 q := by
  rcases le_total 0 q with hq | hq
  · refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := q) (r := -(1 / 2 : ℝ))
      (by norm_num)).congr fun v hv => ?_
    rw [Set.uIoc_of_le hq] at hv
    exact (phi_of_nonneg hv.1.le).symm
  · refine (intervalIntegrable_const (c := (0 : ℝ))).congr fun v hv => ?_
    rw [Set.uIoc_of_ge hq] at hv
    exact (phi_of_nonpos hv.2).symm

lemma phi_intervalIntegrable (p q : ℝ) : IntervalIntegrable phi volume p q :=
  (phi_ii_zero p).symm.trans (phi_ii_zero q)

lemma integral_phi_zero {q : ℝ} (hq : 0 ≤ q) : ∫ v in (0 : ℝ)..q, phi v = 2 * √q := by
  rw [intervalIntegral.integral_congr (g := fun v => v ^ (-(1 / 2 : ℝ))) fun v hv => ?_,
    integral_rpow_half, Real.sqrt_eq_rpow, Real.zero_rpow (by norm_num)]
  · ring
  · rw [Set.uIcc_of_le hq] at hv
    exact phi_of_nonneg hv.1

lemma integral_phi_nonpos {p q : ℝ} (hp : p ≤ 0) (hq : q ≤ 0) : ∫ v in p..q, phi v = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun v hv => ?_]
  · simp
  · exact phi_of_nonpos ((Set.mem_uIcc.mp hv).elim (fun h => h.2.trans hq) fun h => h.2.trans hp)

lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

lemma integral_phi_le (p r : ℝ) (hr : 0 ≤ r) : ∫ v in p..p + 2 * r, phi v ≤ 2 * √(2 * r) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (phi_intervalIntegrable p 0)
    (phi_intervalIntegrable 0 (p + 2 * r))
  rcases le_total (p + 2 * r) 0 with h1 | h1
  · rw [integral_phi_nonpos (by linarith) h1]; positivity
  rw [← hsplit, integral_phi_zero h1]
  rcases le_total p 0 with h2 | h2
  · rw [integral_phi_nonpos h2 le_rfl, zero_add]
    gcongr
    linarith
  · have h3 : ∫ v in (0 : ℝ)..p, phi v = 2 * √p := integral_phi_zero h2
    rw [intervalIntegral.integral_symm, h3]
    have := sqrt_add_le' h2 (by linarith : 0 ≤ 2 * r)
    linarith

lemma dens_le {a b u : ℝ} (hau : a < u) (hub : u < b) :
    1 / (π * √((u - a) * (b - u))) ≤ 1 / (π * √((b - a) / 2)) * (phi (u - a) + phi (b - u)) := by
  rw [phi_of_pos (by linarith), phi_of_pos (by linarith),
    Real.sqrt_mul (by linarith : 0 ≤ u - a)]
  have hA : 0 < √(u - a) := Real.sqrt_pos.mpr (by linarith)
  have hB : 0 < √(b - u) := Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < √((b - a) / 2) := Real.sqrt_pos.mpr (by linarith)
  have hπ := Real.pi_pos
  rcases le_total ((b - a) / 2) (b - u) with h | h
  · have hsB : √((b - a) / 2) ≤ √(b - u) := Real.sqrt_le_sqrt h
    calc 1 / (π * (√(u - a) * √(b - u))) ≤ 1 / (π * (√(u - a) * √((b - a) / 2))) :=
          one_div_le_one_div_of_le (by positivity) (by gcongr)
      _ = 1 / (π * √((b - a) / 2)) * (1 / √(u - a)) := by field_simp
      _ ≤ _ := by gcongr; linarith [one_div_pos.mpr hB]
  · have hsA : √((b - a) / 2) ≤ √(u - a) := Real.sqrt_le_sqrt (by linarith)
    calc 1 / (π * (√(u - a) * √(b - u))) ≤ 1 / (π * (√((b - a) / 2) * √(b - u))) :=
          one_div_le_one_div_of_le (by positivity) (by gcongr)
      _ = 1 / (π * √((b - a) / 2)) * (1 / √(b - u)) := by field_simp
      _ ≤ _ := by gcongr; linarith [one_div_pos.mpr hA]

lemma phi_sub_right_ii (a p q : ℝ) : IntervalIntegrable (fun u => phi (u - a)) volume p q := by
  simpa using (phi_intervalIntegrable (p - a) (q - a)).comp_sub_right a

lemma phi_sub_left_ii (b p q : ℝ) : IntervalIntegrable (fun u => phi (b - u)) volume p q := by
  simpa using (phi_intervalIntegrable (b - p) (b - q)).comp_sub_left b

lemma const_eq {a b r : ℝ} (hab : a < b) (hr : 0 ≤ r) :
    1 / (π * √((b - a) / 2)) * (2 * √(2 * r) + 2 * √(2 * r)) = 8 * √r / (π * √(b - a)) := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have hba : 0 < √(b - a) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_div (by linarith : 0 ≤ b - a)]
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- A unit arcsine measure puts mass at most `8√r/(π√(b-a))` on an interval of radius `r`. -/
lemma arcsine_Icc_le {a b : ℝ} (hab : a < b) (x r : ℝ) (hr : 0 ≤ r) :
    arcsine a b (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (8 * √r / (π * √(b - a))) := by
  unfold arcsine
  rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  set c := 1 / (π * √((b - a) / 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  set g : ℝ → ℝ := fun u => c * (phi (u - a) + phi (b - u)) with hg
  have hgii : IntervalIntegrable g volume (x - r) (x + r) :=
    ((phi_sub_right_ii a _ _).add (phi_sub_left_ii b _ _)).const_mul c
  have hxr : x - r ≤ x + r := by linarith
  calc ∫⁻ u in Icc (x - r) (x + r) ∩ Ioo a b,
        ENNReal.ofReal (1 / (π * √((u - a) * (b - u)))) ≤
        ∫⁻ u in Icc (x - r) (x + r) ∩ Ioo a b, ENNReal.ofReal (g u) :=
          setLIntegral_mono' (measurableSet_Icc.inter measurableSet_Ioo) fun u hu =>
            ENNReal.ofReal_le_ofReal (dens_le hu.2.1 hu.2.2)
    _ ≤ ∫⁻ u in Icc (x - r) (x + r), ENNReal.ofReal (g u) := lintegral_mono_set inter_subset_left
    _ = ENNReal.ofReal (∫ u in Icc (x - r) (x + r), g u) :=
          (ofReal_integral_eq_lintegral_ofReal
            ((intervalIntegrable_iff_integrableOn_Icc_of_le hxr).mp hgii)
            (Filter.Eventually.of_forall fun u =>
              mul_nonneg hc0 (add_nonneg (phi_nonneg _) (phi_nonneg _)))).symm
    _ = ENNReal.ofReal (∫ u in (x - r)..(x + r), g u) := by
          rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxr]
    _ ≤ ENNReal.ofReal (8 * √r / (π * √(b - a))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hg, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add (phi_sub_right_ii a _ _) (phi_sub_left_ii b _ _),
            intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_comp_sub_left,
            ← const_eq hab hr]
          gcongr
          · have := integral_phi_le (x - r - a) r hr
            rwa [show x - r - a + 2 * r = x + r - a by ring] at this
          · have := integral_phi_le (b - (x + r)) r hr
            rwa [show b - (x + r) + 2 * r = b - (x - r) by ring] at this

lemma arcsine_Icc_le' {a b : ℝ} (hab : 1 / 225 < b - a) (x r : ℝ) (hr : 0 ≤ r) :
    arcsine a b (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (40 * √r) := by
  refine (arcsine_Icc_le (by linarith) x r hr).trans (ENNReal.ofReal_le_ofReal ?_)
  have h15 : 1 / 15 < √(b - a) := by
    rw [show (1 / 15 : ℝ) = √(1 / 225) by
      rw [show (1 / 225 : ℝ) = (1 / 15) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hab
  have hπ := Real.pi_gt_three
  have hr' := Real.sqrt_nonneg r
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_lt_mul'' hπ h15 (by norm_num) (by norm_num)]

lemma list_bound (l : List (ℕ × ℕ × ℕ))
    (hl : ∀ e ∈ l, e.1 < e.2.1 ∧ 10 ^ 12 < 225 * (e.2.1 - e.1)) (x r : ℝ) (hr : 0 ≤ r) :
    (l.map fun e => ENNReal.ofReal ((e.2.2 : ℝ) / 10 ^ 12) •
      arcsine ((e.1 : ℝ) / 10 ^ 12) ((e.2.1 : ℝ) / 10 ^ 12)).sum (Icc (x - r) (x + r)) ≤
      ENNReal.ofReal ((l.map fun e => (e.2.2 : ℝ) / 10 ^ 12).sum * (40 * √r)) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    obtain ⟨h1, h2⟩ := hl e List.mem_cons_self
    have hba : 1 / 225 < (e.2.1 : ℝ) / 10 ^ 12 - (e.1 : ℝ) / 10 ^ 12 := by
      have : ((10 ^ 12 : ℕ) : ℝ) < ((225 * (e.2.1 - e.1) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast [Nat.cast_sub h1.le] at this
      rw [← sub_div, lt_div_iff₀ (by norm_num)]
      linarith
    have hA := arcsine_Icc_le' hba x r hr
    have hsum : 0 ≤ (l.map fun e => (e.2.2 : ℝ) / 10 ^ 12).sum :=
      List.sum_nonneg fun y hy => by
        obtain ⟨e', -, rfl⟩ := List.mem_map.mp hy
        positivity
    calc ENNReal.ofReal ((e.2.2 : ℝ) / 10 ^ 12) *
            arcsine ((e.1 : ℝ) / 10 ^ 12) ((e.2.1 : ℝ) / 10 ^ 12) (Icc (x - r) (x + r)) +
          (l.map fun e => ENNReal.ofReal ((e.2.2 : ℝ) / 10 ^ 12) •
            arcsine ((e.1 : ℝ) / 10 ^ 12) ((e.2.1 : ℝ) / 10 ^ 12)).sum (Icc (x - r) (x + r)) ≤
          ENNReal.ofReal ((e.2.2 : ℝ) / 10 ^ 12) * ENNReal.ofReal (40 * √r) +
            ENNReal.ofReal ((l.map fun e => (e.2.2 : ℝ) / 10 ^ 12).sum * (40 * √r)) :=
          add_le_add (mul_le_mul_right hA _) (ih fun e he => hl e (List.mem_cons_of_mem _ he))
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), add_mul]

/-- The mass bound for `ρ`: `ρ([x - r, x + r]) ≤ 40√r`. -/
lemma rho_Icc_le (x r : ℝ) (hr : 0 ≤ r) : rho (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (40 * √r) := by
  have hl : ∀ e ∈ table1, e.1 < e.2.1 ∧ 10 ^ 12 < 225 * (e.2.1 - e.1) := by decide
  refine (list_bound table1 hl x r hr).trans (ENNReal.ofReal_le_ofReal ?_)
  have : (table1.map fun e => (e.2.2 : ℝ) / 10 ^ 12).sum = 37 / 40 := by
    norm_num [table1]
  rw [this]
  nlinarith [Real.sqrt_nonneg r]

lemma rho_singleton (x : ℝ) : rho {x} = 0 := by
  have h := rho_Icc_le x 0 le_rfl
  simp only [sub_zero, add_zero, Set.Icc_self, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero,
    nonpos_iff_eq_zero] at h
  exact h

/-! ## Layer cake: logarithmic integrals against a measure with a `√r` mass bound -/

lemma ofReal_max_zero (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

lemma lc_bound (μ : Measure ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hMB : ∀ x r, 0 ≤ r → μ (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (A * √r)) (x R : ℝ)
    (hR : 0 < R) :
    ∫⁻ u, ENNReal.ofReal (Real.log (R / |x - u|)) ∂μ ≤ ENNReal.ofReal (2 * A * √R) := by
  set f : ℝ → ℝ := fun u => max (Real.log (R / |x - u|)) 0 with hf
  have hfm : Measurable f := by
    simp only [hf]
    fun_prop
  have h1 : ∫⁻ u, ENNReal.ofReal (Real.log (R / |x - u|)) ∂μ = ∫⁻ u, ENNReal.ofReal (f u) ∂μ :=
    lintegral_congr fun u => (ofReal_max_zero _).symm
  rw [h1, lintegral_eq_lintegral_meas_lt (f := f) μ
    (Filter.Eventually.of_forall fun u => (le_max_right _ _ : (0 : ℝ) ≤ f u)) hfm.aemeasurable]
  have hint : IntegrableOn (fun t : ℝ => A * √R * Real.exp ((-1 / 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul _
  calc ∫⁻ t in Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (A * √R * Real.exp ((-1 / 2) * t)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        have hsub : {a | t < f a} ⊆ Icc (x - R * Real.exp (-t)) (x + R * Real.exp (-t)) := by
          intro u hu
          simp only [hf, mem_ofPred_eq, lt_max_iff] at hu
          rcases hu with hu | hu
          · have hxu : 0 < |x - u| := by
              rcases (abs_nonneg (x - u)).lt_or_eq with h | h
              · exact h
              · rw [← h, div_zero, Real.log_zero] at hu; linarith
            have hy : 0 < R / |x - u| := div_pos hR hxu
            have := (Real.lt_log_iff_exp_lt hy).mp hu
            rw [lt_div_iff₀ hxu] at this
            have h2 : |x - u| < R * Real.exp (-t) := by
              rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos t)]
              linarith
            rw [abs_lt] at h2
            constructor <;> linarith
          · linarith
        calc μ {a | t < f a} ≤ μ (Icc (x - R * Real.exp (-t)) (x + R * Real.exp (-t))) :=
              measure_mono hsub
          _ ≤ ENNReal.ofReal (A * √(R * Real.exp (-t))) := hMB _ _ (by positivity)
          _ = _ := by
              rw [Real.sqrt_mul hR.le, ← Real.exp_half]
              congr 1
              ring_nf
    _ = ENNReal.ofReal (∫ t in Ioi 0, A * √R * Real.exp ((-1 / 2) * t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun t => by positivity)).symm
    _ = ENNReal.ofReal (2 * A * √R) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
        congr 1
        simp
        ring

/-! ## Circle measures -/

/-- Normalized arclength on the circle of radius `ε` about `c`. -/
def circ (c : ℂ) (ε : ℝ) : Measure ℂ :=
  ENNReal.ofReal (2 * π)⁻¹ • (volume.restrict (Ioc 0 (2 * π))).map (circleMap c ε)

lemma circ_univ (c : ℂ) (ε : ℝ) : circ c ε univ = 1 := by
  rw [circ, Measure.smul_apply, Measure.map_apply (continuous_circleMap c ε).measurable
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), sub_zero, inv_mul_cancel₀ (by positivity),
    ENNReal.ofReal_one]

instance (c : ℂ) (ε : ℝ) : IsProbabilityMeasure (circ c ε) := ⟨circ_univ c ε⟩

lemma integral_circ (c : ℂ) (ε : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂circ c ε = circleAverage f c ε := by
  rw [circ, integral_smul_measure, integral_map (continuous_circleMap c ε).aemeasurable
    hf.aestronglyMeasurable, circleAverage_def, intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_ofReal (by positivity)]

lemma integrable_circ {c : ℂ} {ε : ℝ} {f : ℂ → ℝ} (hf : CircleIntegrable f c ε)
    (hfm : Measurable f) : Integrable f (circ c ε) := by
  rw [circ]
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  rw [integrable_map_measure hfm.aestronglyMeasurable (continuous_circleMap c ε).aemeasurable]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hf

lemma integrable_circ_of_continuous {c : ℂ} {ε : ℝ} (hε : 0 ≤ ε) {f : ℂ → ℝ}
    (hf : Continuous f) : Integrable f (circ c ε) :=
  integrable_circ (hf.continuousOn.circleIntegrable hε) hf.measurable

lemma circ_ae_sphere (c : ℂ) (ε : ℝ) : ∀ᵐ z ∂circ c ε, ‖z - c‖ = |ε| := by
  have hm : MeasurableSet {a : ℂ | ¬‖a - c‖ = |ε|} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet.compl
  rw [ae_iff, circ, Measure.smul_apply, Measure.map_apply (continuous_circleMap c ε).measurable hm]
  have : circleMap c ε ⁻¹' {a | ¬‖a - c‖ = |ε|} = ∅ := by
    ext θ
    simp [circleMap_sub_center, norm_circleMap_zero]
  rw [this, measure_empty, smul_zero]

lemma circ_singleton (c : ℂ) {ε : ℝ} (hε : ε ≠ 0) (a : ℂ) : circ c ε {a} = 0 := by
  rw [circ, Measure.smul_apply, Measure.map_apply (continuous_circleMap c ε).measurable
    (measurableSet_singleton a), Measure.restrict_apply
      ((continuous_circleMap c ε).measurable (measurableSet_singleton a))]
  have hsub : (circleMap c ε ⁻¹' {a} ∩ Ioc 0 (2 * π)).Subsingleton := by
    intro x hx y hy
    have hI : Set.uIoc (0 : ℝ) (2 * π) = Ioc 0 (2 * π) := Set.uIoc_of_le (by positivity)
    refine injOn_circleMap_of_abs_sub_le (c := c) (a := 0) (b := 2 * π) hε
      (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)]) (hI ▸ hx.2) (hI ▸ hy.2) ?_
    rw [hx.1, hy.1]
  rw [hsub.measure_zero, smul_zero]

/-- The circle average of `log|z - a|`: `⨍ log|z - a| dω = log max(ε, |c - a|)`. -/
lemma circ_log (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, Real.log ‖z - a‖ ∂circ c ε = Real.log (max ε ‖c - a‖) := by
  rw [integral_circ _ _ (by fun_prop),
    circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hε.ne']
  rcases le_total ‖c - a‖ ε with h | h
  · rw [max_eq_left h, (posLog_eq_zero_iff _).mpr, add_zero]
    rw [abs_of_nonneg (by positivity)]
    exact inv_mul_le_one_of_le₀ h hε.le
  · rw [max_eq_right h, posLog_eq_log, Real.log_mul (inv_ne_zero hε.ne') (by
      have := hε.trans_le h; positivity), Real.log_inv]
    · ring
    · rw [abs_of_nonneg (by positivity)]
      exact (one_le_inv_mul₀ hε).mpr h

/-! ## Logarithmic integrability -/

lemma ofReal_abs_log_le {y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal |Real.log y| ≤ ENNReal.ofReal y + ENNReal.ofReal (-Real.log y) := by
  rw [← ofReal_max_zero (-Real.log y), ← ENNReal.ofReal_add hy (le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total 0 (Real.log y) with h | h
  · rw [abs_of_nonneg h]
    linarith [Real.log_le_self hy, le_max_right (-Real.log y) 0]
  · rw [abs_of_nonpos h]
    linarith [le_max_left (-Real.log y) 0]

/-- `log|z - w|` is integrable for `μ ⊗ ν` if both are finite, carried by a ball, and the
negative part of the potential of `ν` is uniformly bounded there. -/
lemma integrable_log_prod (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (R C : ℝ)
    (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ R) (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ R)
    (hlog : ∀ z : ℂ, ‖z‖ ≤ R → ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂ν ≤ ENNReal.ofReal C) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν) := by
  have hm : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) := by fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_eq_ofReal_abs]
  rw [lintegral_prod _ (hm.abs.ennreal_ofReal.aemeasurable)]
  calc ∫⁻ z, ∫⁻ w, ENNReal.ofReal |Real.log ‖(z, w).1 - (z, w).2‖| ∂ν ∂μ
      ≤ ∫⁻ _z, (ENNReal.ofReal (2 * R) * ν univ + ENNReal.ofReal C) ∂μ := by
        refine lintegral_mono_ae (hμ.mono fun z hz => ?_)
        calc ∫⁻ w, ENNReal.ofReal |Real.log ‖(z, w).1 - (z, w).2‖| ∂ν
            ≤ ∫⁻ w, (ENNReal.ofReal ‖z - w‖ + ENNReal.ofReal (-Real.log ‖z - w‖)) ∂ν :=
              lintegral_mono fun w => ofReal_abs_log_le (norm_nonneg _)
          _ = ∫⁻ w, ENNReal.ofReal ‖z - w‖ ∂ν + ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂ν :=
              lintegral_add_left (by fun_prop) _
          _ ≤ ENNReal.ofReal (2 * R) * ν univ + ENNReal.ofReal C := by
              gcongr
              · rw [← lintegral_const]
                refine lintegral_mono_ae (hν.mono fun w hw => ENNReal.ofReal_le_ofReal ?_)
                linarith [norm_sub_le z w]
              · exact hlog z hz
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (measure_lt_top _ _), ENNReal.ofReal_lt_top⟩) (measure_lt_top _ _)

/-! ## Facts about `ρ` -/

instance : IsFiniteMeasure rho := ⟨by rw [lemma_6_1.1]; exact ENNReal.ofReal_lt_top⟩

lemma rho_ae_Ioo : ∀ᵐ u ∂rho, u ∈ Ioo (0 : ℝ) 2 := by
  rw [ae_iff]
  exact lemma_6_1.2.1

lemma rho_ae_ne (x : ℝ) : ∀ᵐ u ∂rho, u ≠ x := by
  rw [ae_iff]
  simpa using rho_singleton x

lemma lintegral_neg_log_rho (x : ℝ) :
    ∫⁻ u, ENNReal.ofReal (-Real.log |x - u|) ∂rho ≤ ENNReal.ofReal 80 := by
  have h := lc_bound rho 40 (by norm_num) (fun x r hr => rho_Icc_le x r hr) x 1 one_pos
  simp only [one_div, Real.log_inv, Real.sqrt_one, mul_one] at h
  refine h.trans (le_of_eq ?_)
  norm_num

lemma integrable_log_rho (x : ℝ) : Integrable (fun u => Real.log |x - u|) rho := by
  refine ⟨(by fun_prop : Measurable fun u : ℝ => Real.log |x - u|).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_eq_ofReal_abs]
  calc ∫⁻ u, ENNReal.ofReal (abs (Real.log |x - u|)) ∂rho
      ≤ ∫⁻ u, (ENNReal.ofReal |x - u| + ENNReal.ofReal (-Real.log |x - u|)) ∂rho :=
        lintegral_mono fun u => ofReal_abs_log_le (abs_nonneg _)
    _ = ∫⁻ u, ENNReal.ofReal |x - u| ∂rho + ∫⁻ u, ENNReal.ofReal (-Real.log |x - u|) ∂rho :=
        lintegral_add_left (by fun_prop) _
    _ ≤ ∫⁻ _u, ENNReal.ofReal (|x| + 2) ∂rho + ENNReal.ofReal 80 := by
        refine add_le_add ?_ (lintegral_neg_log_rho x)
        · refine lintegral_mono_ae (rho_ae_Ioo.mono fun u hu => ENNReal.ofReal_le_ofReal ?_)
          have := abs_sub_le x 0 u
          simp only [sub_zero, zero_sub, abs_neg] at this
          rw [abs_of_pos hu.1] at this
          linarith [hu.2]
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (measure_lt_top _ _), ENNReal.ofReal_lt_top⟩

lemma rho_univ_toReal : (rho univ).toReal = Lim.lam := by
  rw [lemma_6_1.1, ENNReal.toReal_ofReal (by norm_num [Lim.lam])]

lemma ofReal_log_max_sub {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    ENNReal.ofReal (Real.log (max ε d) - Real.log d) = ENNReal.ofReal (Real.log (ε / d)) := by
  rcases le_total ε d with h | h
  · rw [max_eq_right h, sub_self, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos]
    exact Real.log_nonpos (by positivity) ((div_le_one hd).mpr h)
  · rw [max_eq_left h, Real.log_div hε.ne' hd.ne']

/-- The regularization error for `ρ`: `∫ log max(ε, |x - u|) dρ(u) ≤ U^ρ(x) + 80√ε`. -/
lemma cross_bound (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ u, Real.log (max ε |x - u|) ∂rho ≤ logPot rho x + 80 * √ε := by
  have hint1 := integrable_log_rho x
  have hint2 : Integrable (fun u => Real.log (max ε |x - u|)) rho := by
    refine Integrable.of_bound
      (by fun_prop : Measurable fun u : ℝ => Real.log (max ε |x - u|)).aestronglyMeasurable
      (|Real.log ε| + ε + |x| + 2)
      (rho_ae_Ioo.mono fun u hu => ?_)
    have hm : 0 < max ε |x - u| := lt_max_of_lt_left hε
    have h1 : Real.log ε ≤ Real.log (max ε |x - u|) := Real.log_le_log hε (le_max_left _ _)
    have h2 : Real.log (max ε |x - u|) ≤ max ε |x - u| := Real.log_le_self hm.le
    have h3 : |x - u| ≤ |x| + 2 := by
      have := abs_sub_le x 0 u
      simp only [sub_zero, zero_sub, abs_neg] at this
      rw [abs_of_pos hu.1] at this
      linarith [hu.2]
    have h4 : max ε |x - u| ≤ ε + |x| + 2 := max_le (by linarith [abs_nonneg x]) (by linarith)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (Real.log ε), le_abs_self (Real.log ε)]
  have hsub : ∫ u, Real.log (max ε |x - u|) ∂rho - logPot rho x =
      ∫ u, (Real.log (max ε |x - u|) - Real.log |x - u|) ∂rho :=
    (integral_sub hint2 hint1).symm
  have hnn : 0 ≤ᵐ[rho] fun u => Real.log (max ε |x - u|) - Real.log |x - u| :=
    (rho_ae_ne x).mono fun u hu => by
      have hd : 0 < |x - u| := abs_pos.mpr (sub_ne_zero.mpr hu.symm)
      simp only [Pi.zero_apply, sub_nonneg]
      exact Real.log_le_log hd (le_max_right _ _)
  have hD : ∫ u, (Real.log (max ε |x - u|) - Real.log |x - u|) ∂rho ≤ 80 * √ε := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn (hint2.sub hint1).aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc ∫⁻ u, ENNReal.ofReal (Real.log (max ε |x - u|) - Real.log |x - u|) ∂rho
        = ∫⁻ u, ENNReal.ofReal (Real.log (ε / |x - u|)) ∂rho :=
          lintegral_congr_ae ((rho_ae_ne x).mono fun u hu =>
            ofReal_log_max_sub hε (abs_pos.mpr (sub_ne_zero.mpr hu.symm)))
      _ ≤ ENNReal.ofReal (2 * 40 * √ε) :=
          lc_bound rho 40 (by norm_num) (fun x r hr => rho_Icc_le x r hr) x ε hε
      _ = ENNReal.ofReal (80 * √ε) := by norm_num
  linarith

/-! ## The modified field bound (6.7) -/

lemma logPot_le_of_two_le {t : ℝ} (ht : 2 ≤ t) : logPot rho t ≤ Lim.lam * Real.log t := by
  unfold logPot
  calc ∫ u, Real.log |t - u| ∂rho ≤ ∫ _u, Real.log t ∂rho :=
        integral_mono_ae (integrable_log_rho t) (integrable_const _)
          (rho_ae_Ioo.mono fun u hu => by
            have h1 : 0 < t - u := by linarith [hu.2]
            show Real.log |t - u| ≤ Real.log t
            rw [abs_of_pos h1]
            exact Real.log_le_log h1 (by linarith [hu.1]))
    _ = Lim.lam * Real.log t := by
        rw [integral_const, smul_eq_mul, Measure.real, rho_univ_toReal]

lemma V_lower {t : ℝ} (ht : 2 ≤ t) :
    2 * π * √t + (1 - 6 * Lim.α) * Real.log t - 2 * Lim.α ^ 3 / t ≤ V t := by
  have ht0 : 0 < t := by linarith
  have hc : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => by positivity
  have h1 : Real.log t ≤ ∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2) := by
    have := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ => Real.log t) volume 0 1)
      (hc.intervalIntegrable 0 1)
      fun u _ => Real.log_le_log ht0 (by nlinarith [sq_nonneg u])
    simpa using this
  have h2 : ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2) ≤
      3 / 40 * Real.log t + (3 / 40) ^ 3 / 3 / t := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 3 / 40)
      (hc.intervalIntegrable 0 (3 / 40))
      ((by fun_prop : Continuous fun u : ℝ => Real.log t + u ^ 2 / t).intervalIntegrable
        (μ := volume) 0 (3 / 40))
      fun u _ => by
        show Real.log (t + u ^ 2) ≤ Real.log t + u ^ 2 / t
        have hpos : 0 < t + u ^ 2 := by positivity
        have := Real.log_le_sub_one_of_pos (div_pos hpos ht0)
        rw [Real.log_div hpos.ne' ht0.ne'] at this
        have e : (t + u ^ 2) / t - 1 = u ^ 2 / t := by field_simp; ring
        linarith
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_add
      (intervalIntegrable_const : IntervalIntegrable (fun _ => Real.log t) volume 0 (3 / 40))
      (((continuous_pow 2).div_const t).intervalIntegrable 0 (3 / 40)),
      intervalIntegral.integral_const,
      intervalIntegral.integral_div, integral_pow]
    norm_num
  have e6 : 6 * ((3 / 40 : ℝ) ^ 3 / 3 / t) = 2 * (3 / 40) ^ 3 / t := by ring
  unfold V
  simp only [Lim.α] at *
  linarith

lemma sqrt_two_bounds : 1.4142 < √2 ∧ √2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- (6.7): `2U^ρ(t) - V(t) + √t/K ≤ M₀ + √2/K` for `t ≥ 0`, `K ≥ 40`. -/
lemma field_bound {K : ℝ} (hK : 40 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    2 * logPot rho t - V t + √t / K ≤ M0 + √2 / K := by
  have hK0 : 0 < K := by linarith
  rcases le_total t 2 with h2 | h2
  · have h62 := lemma_6_1.2.2.1 t ht
    have : √t / K ≤ √2 / K := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h2) hK0.le
    linarith
  · have hU := logPot_le_of_two_le h2
    have hV := V_lower h2
    set s := √t with hs
    have hs2 : √2 ≤ s := Real.sqrt_le_sqrt h2
    have hts : t = s ^ 2 := (Real.sq_sqrt ht).symm
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs2
    obtain ⟨r1, r2⟩ := sqrt_two_bounds
    -- log t = 2 log s ≤ log 2 + √2 s - 2
    have hlog : Real.log t ≤ Real.log 2 + √2 * s - 2 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hspos (by positivity : (0 : ℝ) < √2))
      rw [Real.log_div hspos.ne' (by positivity)] at h
      have hl2 : Real.log √2 = Real.log 2 / 2 := by
        rw [Real.log_sqrt (by norm_num)]
      have ht' : Real.log t = 2 * Real.log s := by
        rw [hts, Real.log_pow]; push_cast; ring
      have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      have : s / √2 = √2 * s / 2 := by field_simp; nlinarith [hsq]
      rw [hl2, this] at h
      rw [ht']
      linarith
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hinv : 2 * Lim.α ^ 3 / t ≤ 2 * Lim.α ^ 3 / 2 :=
      div_le_div_of_nonneg_left (by norm_num [Lim.α]) (by norm_num) h2
    have hsK : s / K ≤ √2 / K + (s - √2) / 40 := by
      rw [show s / K = √2 / K + (s - √2) / K by ring]
      gcongr
    have hπ := Real.pi_gt_d2
    have hl2 := Real.log_two_lt_d9
    have e1 : √2 * s ≤ 1.4143 * s := mul_le_mul_of_nonneg_right r2.le hspos.le
    have e2 : 3.14 * s ≤ π * s := mul_le_mul_of_nonneg_right hπ.le hspos.le
    have e3 : 3.14 * √2 ≤ π * √2 := mul_le_mul_of_nonneg_right hπ.le (by positivity)
    have e4 : π * (s - √2) ≥ 3.14 * (s - √2) :=
      mul_le_mul_of_nonneg_right hπ.le (by linarith)
    simp only [Lim.lam, Lim.α, M0] at *
    push_cast
    nlinarith

/-! ## The regularized configuration `σ = K⁻¹ ∑ ω_i` and `ρ` on `ℂ` -/

lemma circ_neg_log (c : ℂ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) (hc : ‖c‖ + ε ≤ R) (z : ℂ)
    (hz : ‖z‖ ≤ R) :
    ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂circ c ε ≤ ENNReal.ofReal (2 * R - Real.log ε) := by
  have hg : Integrable (fun w => Real.log ‖w - z‖) (circ c ε) :=
    integrable_circ (circleIntegrable_log_norm_sub_const ε) (by fun_prop)
  have hR : 0 ≤ R := le_trans (by positivity) hc
  calc ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂circ c ε
      = ∫⁻ w, ENNReal.ofReal (max (-Real.log ‖w - z‖) 0) ∂circ c ε :=
        lintegral_congr fun w => by rw [ofReal_max_zero, norm_sub_rev]
    _ = ENNReal.ofReal (∫ w, max (-Real.log ‖w - z‖) 0 ∂circ c ε) :=
        (ofReal_integral_eq_lintegral_ofReal hg.neg.pos_part
          (Filter.Eventually.of_forall fun w => le_max_right _ _)).symm
    _ ≤ ENNReal.ofReal (2 * R - Real.log ε) := by
        apply ENNReal.ofReal_le_ofReal
        have e : ∫ w, max (-Real.log ‖w - z‖) 0 ∂circ c ε =
            ∫ w, max (Real.log ‖w - z‖) 0 ∂circ c ε - ∫ w, Real.log ‖w - z‖ ∂circ c ε := by
          rw [← integral_sub hg.pos_part hg]
          congr 1
          ext w
          rcases le_total 0 (Real.log ‖w - z‖) with h | h
          · rw [max_eq_right (by linarith), max_eq_left h]; ring
          · rw [max_eq_left (by linarith), max_eq_right h]; ring
        have h1 : Real.log ε ≤ ∫ w, Real.log ‖w - z‖ ∂circ c ε := by
          rw [circ_log c z hε]
          exact Real.log_le_log hε (le_max_left _ _)
        have h2 : ∫ w, max (Real.log ‖w - z‖) 0 ∂circ c ε ≤ 2 * R := by
          have := integral_mono_ae hg.pos_part (integrable_const (2 * R))
            ((circ_ae_sphere c ε).mono fun w hw => by
              have hw' : ‖w‖ ≤ R := by
                have := norm_le_norm_add_norm_sub' w c
                rw [hw, abs_of_pos hε] at this
                linarith
              refine max_le ?_ (by linarith)
              exact (Real.log_le_self (norm_nonneg _)).trans (by linarith [norm_sub_le w z]))
          simpa using this
        linarith

section Config

variable {n : ℕ} (K : ℕ) (t : Fin n → ℝ) (ε : ℝ)

/-- `σ = K⁻¹ ∑ ω_i`. -/
def sig : Measure ℂ := ENNReal.ofReal (1 / K) • ∑ i, circ (t i) ε

lemma sig_apply (S : Set ℂ) : sig K t ε S = ENNReal.ofReal (1 / K) * ∑ i, circ (t i) ε S := by
  rw [sig, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

lemma sig_univ : sig K t ε univ = ENNReal.ofReal (n / K) := by
  rw [sig_apply]
  simp only [circ_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

instance : IsFiniteMeasure (sig K t ε) := ⟨by rw [sig_univ]; exact ENNReal.ofReal_lt_top⟩

lemma sig_integral {f : ℂ → ℝ} (hf : ∀ i, Integrable f (circ (t i) ε)) :
    ∫ z, f z ∂sig K t ε = (1 / K) * ∑ i, ∫ z, f z ∂circ (t i) ε := by
  rw [sig, integral_smul_measure, integral_finsetSum_measure (fun i _ => hf i),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma sig_lintegral (f : ℂ → ENNReal) :
    ∫⁻ z, f z ∂sig K t ε = ENNReal.ofReal (1 / K) * ∑ i, ∫⁻ z, f z ∂circ (t i) ε := by
  rw [sig, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]

lemma sig_ae {p : ℂ → Prop} (h : ∀ i, ∀ᵐ z ∂circ (t i) ε, p z) : ∀ᵐ z ∂sig K t ε, p z := by
  rw [sig]
  refine Measure.ae_smul_measure ?_ _
  rw [ae_iff, Measure.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => ae_iff.mp (h i)

lemma sig_singleton {ε : ℝ} (hε : ε ≠ 0) (a : ℂ) : sig K t ε {a} = 0 := by
  rw [sig_apply]
  simp [circ_singleton _ hε]

end Config

/-- `ρ` on `ℂ`. -/
def rhoC : Measure ℂ := rho.map ((↑) : ℝ → ℂ)

instance : IsFiniteMeasure rhoC := by unfold rhoC; infer_instance

lemma ofReal_measurableEmbedding : MeasurableEmbedding ((↑) : ℝ → ℂ) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

lemma rhoC_univ : rhoC univ = ENNReal.ofReal Lim.lam := by
  rw [rhoC, Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ, preimage_univ,
    lemma_6_1.1]

lemma rhoC_ae : ∀ᵐ w ∂rhoC, ‖w‖ ≤ 2 := by
  rw [rhoC, ae_map_iff Complex.measurable_ofReal.aemeasurable
    (isClosed_le (by fun_prop) continuous_const).measurableSet]
  exact rho_ae_Ioo.mono fun u hu => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
    exact hu.2.le

lemma rhoC_singleton (a : ℂ) : rhoC {a} = 0 := by
  rw [rhoC, Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton a)]
  refine measure_mono_null (fun u hu => ?_) (rho_singleton a.re)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu ⊢
  rw [← hu, Complex.ofReal_re]

lemma rhoC_neg_log (z : ℂ) :
    ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂rhoC ≤ ENNReal.ofReal 80 := by
  rw [rhoC, lintegral_map (by fun_prop) Complex.measurable_ofReal]
  refine le_trans (lintegral_mono_ae ((rho_ae_ne z.re).mono fun u hu => ?_))
    (lintegral_neg_log_rho z.re)
  have hd : 0 < |z.re - u| := abs_pos.mpr (sub_ne_zero.mpr hu.symm)
  have hle : |z.re - u| ≤ ‖z - (u : ℂ)‖ := by
    have := Complex.abs_re_le_norm (z - (u : ℂ))
    simpa using this
  exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log hd hle))

lemma integral_rhoC (f : ℂ → ℝ) : ∫ w, f w ∂rhoC = ∫ u, f u ∂rho :=
  ofReal_measurableEmbedding.integral_map f

/-! ## The energies -/

lemma pair_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), f i j := by
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm]
  simp_rw [Finset.sum_filter]
  conv_lhs => enter [2, i, 2, j]; rw [hsplit i j]
  simp_rw [Finset.sum_add_distrib]
  rw [h2]
  ring

lemma norm_ofReal_sub (a b : ℝ) : ‖(a : ℂ) - b‖ = |a - b| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma continuous_logmax (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ => Real.log (max ε ‖c - z‖) :=
  Continuous.log (continuous_const.max (continuous_const.sub continuous_id).norm)
    fun z => (lt_max_of_lt_left hε).ne'

lemma integrable_log_sub_circ (c z : ℂ) (ε : ℝ) :
    Integrable (fun w => Real.log ‖z - w‖) (circ c ε) := by
  have : (fun w => Real.log ‖z - w‖) = fun w => Real.log ‖w - z‖ := by
    funext w; rw [norm_sub_rev]
  rw [this]
  exact integrable_circ (circleIntegrable_log_norm_sub_const ε) (by fun_prop)

lemma term_bound {n : ℕ} (t : Fin n → ℝ) (hinj : Function.Injective t) {ε : ℝ} (hε : 0 < ε)
    (i j : Fin n) :
    Real.log |t i - t j| + (if i = j then Real.log ε else 0) ≤
      ∫ z, Real.log (max ε ‖(t j : ℂ) - z‖) ∂circ (t i) ε := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, sub_self, abs_zero, Real.log_zero, zero_add]
    have : ∫ z, Real.log (max ε ‖(t i : ℂ) - z‖) ∂circ (t i) ε = Real.log ε := by
      rw [integral_congr_ae (g := fun _ => Real.log ε) ((circ_ae_sphere _ _).mono fun z hz => by
        simp only
        rw [norm_sub_rev, hz, abs_of_pos hε, max_self])]
      simp
    rw [this]
  · rw [if_neg hij, add_zero]
    have hne : t i ≠ t j := fun h => hij (hinj h)
    have hd : 0 < |t i - t j| := abs_pos.mpr (sub_ne_zero.mpr hne)
    calc Real.log |t i - t j| ≤ Real.log (max ε ‖(t i : ℂ) - t j‖) := by
          rw [norm_ofReal_sub]; exact Real.log_le_log hd (le_max_right _ _)
      _ = ∫ z, Real.log ‖z - t j‖ ∂circ (t i) ε := (circ_log _ _ hε).symm
      _ ≤ ∫ z, Real.log (max ε ‖(t j : ℂ) - z‖) ∂circ (t i) ε := by
          refine integral_mono_ae (integrable_circ (circleIntegrable_log_norm_sub_const ε)
            (by fun_prop)) (integrable_circ_of_continuous hε.le (continuous_logmax _ hε)) ?_
          have hae : ∀ᵐ z ∂circ (t i) ε, z ≠ (t j : ℂ) := by
            rw [ae_iff]; simpa using circ_singleton (t i) hε.ne' (t j : ℂ)
          refine hae.mono fun z hz => ?_
          have hpos : 0 < ‖z - (t j : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
          show Real.log ‖z - (t j : ℂ)‖ ≤ Real.log (max ε ‖(t j : ℂ) - z‖)
          rw [norm_sub_rev z]
          rw [norm_sub_rev z] at hpos
          exact Real.log_le_log hpos (le_max_right _ _)

section Energies

variable {n : ℕ} (K : ℕ) (t : Fin n → ℝ) {ε : ℝ}

lemma inner_sig (hε : 0 < ε) (z : ℂ) :
    ∫ w, Real.log ‖z - w‖ ∂sig K t ε = (1 / K) * ∑ j, Real.log (max ε ‖(t j : ℂ) - z‖) := by
  rw [sig_integral K t ε fun j => integrable_log_sub_circ _ z ε]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← circ_log _ z hε]
  congr 1
  funext w
  rw [norm_sub_rev]

lemma energy_sig_ge (hinj : Function.Injective t) (hε : 0 < ε) :
    (1 / K) ^ 2 * (∑ i, ∑ j, Real.log |t i - t j| + n * Real.log ε) ≤
      logEnergyC (sig K t ε) (sig K t ε) := by
  unfold logEnergyC
  simp_rw [inner_sig K t hε]
  have hint : ∀ j, Integrable (fun z => Real.log (max ε ‖(t j : ℂ) - z‖)) (circ (t j) ε) :=
    fun j => integrable_circ_of_continuous hε.le (continuous_logmax _ hε)
  rw [sig_integral K t ε fun i => ((integrable_finsetSum _ fun j _ =>
    integrable_circ_of_continuous hε.le (continuous_logmax _ hε)).const_mul (1 / K))]
  simp_rw [integral_const_mul]
  have hsum : ∑ i, ∑ j, Real.log |t i - t j| + n * Real.log ε =
      ∑ i, ∑ j, (Real.log |t i - t j| + (if i = j then Real.log ε else 0)) := by
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
  rw [hsum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (1 / (K : ℝ)) ^ 2 * ∑ j, (Real.log |t i - t j| + (if i = j then Real.log ε else 0))
      ≤ (1 / (K : ℝ)) ^ 2 * ∑ j, ∫ z, Real.log (max ε ‖(t j : ℂ) - z‖) ∂circ (t i) ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => term_bound t hinj hε i j)
          (by positivity)
    _ = _ := by
        rw [integral_finsetSum _ fun j _ =>
          integrable_circ_of_continuous hε.le (continuous_logmax _ hε)]
        ring

end Energies

section Energies2

variable {n : ℕ} (K : ℕ) (t : Fin n → ℝ) {ε : ℝ}

/-- The radius `R₀ = ∑ tᵢ + 3` carrying everything. -/
def R0 : ℝ := ∑ i, t i + 3

lemma circ_center_le (ht : ∀ i, 0 ≤ t i) (hε1 : ε ≤ 1) (i : Fin n) :
    ‖(t i : ℂ)‖ + ε ≤ R0 t := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht i), R0]
  have := Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)
  linarith

lemma circ_ae_le (ht : ∀ i, 0 ≤ t i) (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin n) :
    ∀ᵐ w ∂circ (t i) ε, ‖w‖ ≤ R0 t :=
  (circ_ae_sphere _ _).mono fun w hw => by
    have := norm_le_norm_add_norm_sub' w (t i : ℂ)
    rw [hw, abs_of_pos hε] at this
    linarith [circ_center_le t ht hε1 i]

lemma R0_ge (ht : ∀ i, 0 ≤ t i) : 3 ≤ R0 t := by
  rw [R0]; linarith [Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => ht j]

lemma rhoC_ae_le (ht : ∀ i, 0 ≤ t i) : ∀ᵐ w ∂rhoC, ‖w‖ ≤ R0 t :=
  rhoC_ae.mono fun w hw => by linarith [R0_ge t ht]

lemma integrable_circ_rhoC (ht : ∀ i, 0 ≤ t i) (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin n) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circ (t i) ε).prod rhoC) :=
  integrable_log_prod _ _ (R0 t) 80 (circ_ae_le t ht hε hε1 i) (rhoC_ae_le t ht)
    fun z _ => rhoC_neg_log z

lemma energy_cross_le (ht : ∀ i, 0 ≤ t i) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    logEnergyC (sig K t ε) rhoC ≤ (1 / K) * ∑ i, (logPot rho (t i) + 80 * √ε) := by
  unfold logEnergyC
  rw [sig_integral K t ε fun i => (integrable_circ_rhoC t ht hε hε1 i).integral_prod_left]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  rw [integral_integral_swap (integrable_circ_rhoC t ht hε hε1 i)]
  simp_rw [circ_log _ _ hε]
  rw [integral_rhoC]
  simp_rw [norm_ofReal_sub]
  exact cross_bound (t i) hε

lemma energy_rhoC : logEnergyC rhoC rhoC = logEnergy rho := by
  unfold logEnergyC logEnergy logPot
  rw [integral_rhoC]
  simp_rw [integral_rhoC, norm_ofReal_sub]

/-- The total measure `σ + ρ`. -/
def Tm : Measure ℂ := sig K t ε + rhoC

instance : IsFiniteMeasure (Tm K t (ε := ε)) := by unfold Tm; infer_instance

lemma Tm_ae_le (ht : ∀ i, 0 ≤ t i) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ w ∂Tm K t (ε := ε), ‖w‖ ≤ R0 t := by
  rw [Tm, ae_add_measure_iff]
  exact ⟨sig_ae K t ε (circ_ae_le t ht hε hε1), rhoC_ae_le t ht⟩

lemma Tm_neg_log (ht : ∀ i, 0 ≤ t i) (hK : 0 < K) (hε : 0 < ε) (hε1 : ε ≤ 1) (z : ℂ)
    (hz : ‖z‖ ≤ R0 t) :
    ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂Tm K t (ε := ε) ≤
      ENNReal.ofReal (n * (2 * R0 t - Real.log ε) + 80) := by
  have hC : 0 ≤ 2 * R0 t - Real.log ε := by
    linarith [R0_ge t ht, Real.log_nonpos hε.le hε1]
  rw [Tm, lintegral_add_measure, sig_lintegral,
    ENNReal.ofReal_add (by positivity) (by norm_num)]
  refine add_le_add ?_ (rhoC_neg_log z)
  have hK1 : ENNReal.ofReal (1 / K) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    rw [div_le_one (by exact_mod_cast hK)]
    exact_mod_cast hK
  calc ENNReal.ofReal (1 / K) * ∑ i, ∫⁻ w, ENNReal.ofReal (-Real.log ‖z - w‖) ∂circ (t i) ε
      ≤ 1 * ∑ _i : Fin n, ENNReal.ofReal (2 * R0 t - Real.log ε) :=
        mul_le_mul' hK1 (Finset.sum_le_sum fun i _ =>
          circ_neg_log _ hε _ (circ_center_le t ht hε1 i) z hz)
    _ = ENNReal.ofReal (n * (2 * R0 t - Real.log ε)) := by
        rw [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

lemma Tm_integrable (ht : ∀ i, 0 ≤ t i) (hK : 0 < K) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((Tm K t (ε := ε)).prod (Tm K t (ε := ε))) :=
  integrable_log_prod _ _ (R0 t) _ (Tm_ae_le K t ht hε hε1) (Tm_ae_le K t ht hε hε1)
    (Tm_neg_log K t ht hK hε hε1)

lemma Tm_diag (hε : 0 < ε) :
    ((Tm K t (ε := ε)).prod (Tm K t (ε := ε))) {p : ℂ × ℂ | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have : ∀ z : ℂ, Prod.mk z ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {z} := by
    intro z; ext w; simp [eq_comm]
  simp_rw [this, Tm, Measure.add_apply, sig_singleton K t hε.ne', rhoC_singleton, add_zero]
  simp

end Energies2

end C69

open C69 in
/-- **(6.9)**: for every configuration `0 ≤ t₁, …, t_h` of distinct points,
`2∑_{i<j} log|t_i - t_j| - K∑V(t_i) + ∑√t_i ≤ (λM₀ - I(ρ))K² + (120 + √2)h + 2h log K`. -/
theorem config_bound_6_9' (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) (t : Fin (hof K) → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective t) :
    2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), Real.log |t i - t j|
      - K * ∑ i, V (t i) + ∑ i, Real.sqrt (t i) ≤
      (Lim.lam * M0 - logEnergy rho) * (K : ℝ) ^ 2 + (120 + Real.sqrt 2) * hof K
        + 2 * hof K * Real.log K := by
  have hKr : (40 : ℝ) ≤ K := by
    obtain ⟨m, rfl⟩ := hK
    have : 1 ≤ m := by omega
    push_cast
    have : (1 : ℝ) ≤ m := by exact_mod_cast this
    linarith
  have hKp : (0 : ℝ) < K := by linarith
  have hn : ((hof K : ℕ) : ℝ) = Lim.lam * K := by
    obtain ⟨m, rfl⟩ := hK
    have : hof (40 * m) = 37 * m := by unfold hof; omega
    rw [this]
    push_cast
    simp only [Lim.lam]
    ring
  set ε : ℝ := (1 / (2 * K)) ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef]
    have : 1 / (2 * (K : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith [show (0 : ℝ) ≤ 1 / (2 * K) by positivity]
  have hsε : √ε = 1 / (2 * K) := Real.sqrt_sq (by positivity)
  have hlogε : Real.log ε = -(2 * Real.log 2 + 2 * Real.log K) := by
    rw [hεdef, Real.log_pow, one_div, Real.log_inv, Real.log_mul (by norm_num) hKp.ne']
    push_cast
    ring
  have hmass : sig K t ε univ = rhoC univ := by
    rw [sig_univ, rhoC_univ, hn, mul_div_assoc, div_self hKp.ne', mul_one]
  have L := lemma_6_2' (sig K t ε) rhoC hmass (Tm_integrable K t ht hK0 hε hε1)
    (Tm_diag K t hε)
  rw [energy_rhoC] at L
  have A := energy_sig_ge K t hinj hε
  have B := energy_cross_le K t ht hε hε1
  have P := pair_sum (fun i j => Real.log |t i - t j|) (fun i j => by rw [abs_sub_comm])
    (fun i => by simp)
  rw [P] at A
  set S := ∑ i, ∑ j ∈ univ.filter (fun j => i < j), Real.log |t i - t j| with hS
  set SU := ∑ i, logPot rho (t i) with hSU
  set SV := ∑ i, V (t i) with hSV
  set SQ := ∑ i, √(t i) with hSQ
  set I := logEnergy rho with hI
  have hB : ∑ i, (logPot rho (t i) + 80 * √ε) = SU + (hof K : ℝ) * (80 * √ε) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hB] at B
  have Dsum : 2 * SU - SV + SQ / K ≤ (hof K : ℝ) * (M0 + √2 / K) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin (hof K)))) => field_bound hKr (ht i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_div] at this
    linarith
  have L' : (1 / K) ^ 2 * (2 * S + (hof K : ℝ) * Real.log ε) -
      2 * ((1 / K) * (SU + (hof K : ℝ) * (80 * √ε))) + I ≤ 0 := by linarith
  have M := mul_le_mul_of_nonneg_left L' (sq_nonneg (K : ℝ))
  have eM : (K : ℝ) ^ 2 * ((1 / K) ^ 2 * (2 * S + (hof K : ℝ) * Real.log ε) -
      2 * ((1 / K) * (SU + (hof K : ℝ) * (80 * √ε))) + I) =
      2 * S + (hof K : ℝ) * Real.log ε - 2 * K * (SU + (hof K : ℝ) * (80 * √ε)) + K ^ 2 * I := by
    field_simp
  rw [eM, mul_zero] at M
  have D' := mul_le_mul_of_nonneg_left Dsum hKp.le
  have eD : (K : ℝ) * (2 * SU - SV + SQ / K) = 2 * K * SU - K * SV + SQ := by
    field_simp
  have eD2 : (K : ℝ) * ((hof K : ℝ) * (M0 + √2 / K)) = (hof K : ℝ) * K * M0 + (hof K : ℝ) * √2 := by
    field_simp
  rw [eD, eD2] at D'
  have h80 : (K : ℝ) * (80 * √ε) = 40 := by rw [hsε]; field_simp; ring
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hn0 : (0 : ℝ) ≤ (hof K : ℝ) := by positivity
  have hnK : (hof K : ℝ) * K * M0 = Lim.lam * M0 * K ^ 2 := by rw [hn]; ring
  rw [hlogε] at M
  have e80 : 2 * K * (SU + (hof K : ℝ) * (80 * √ε)) = 2 * K * SU + 2 * (hof K : ℝ) * (K * (80 * √ε)) := by ring
  rw [e80, h80] at M
  nlinarith [mul_le_mul_of_nonneg_left hl2 hn0]


/-- (6.9): for every configuration `t₁, …, t_h ≥ 0`,
`2∑_{i<j} log|t_i - t_j| - K∑V(t_i) + ∑√t_i ≤ (λM₀ - I(ρ))K² + (120 + √2)h + 2h log K`. -/
theorem config_bound_6_9 (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) (t : Fin (hof K) → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective t) :
    2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), Real.log |t i - t j|
      - K * ∑ i, V (t i) + ∑ i, Real.sqrt (t i) ≤
      (Lim.lam * M0 - logEnergy rho) * (K : ℝ) ^ 2 + (120 + Real.sqrt 2) * hof K
        + 2 * hof K * Real.log K := by
  exact config_bound_6_9' K hK hK0 t ht hinj

end Zeta5
