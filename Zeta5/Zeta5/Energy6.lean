import Zeta5.Section6

/-!
# §6: the weight bound (6.11) and the zero-mass energy lemma (Lemma 6.2)
-/

open Polynomial Finset MeasureTheory

noncomputable section

namespace Zeta5

theorem pow4_le_choose (l : ℕ) : ((l + 1 : ℕ) : ℝ) ^ 4 ≤ 24 * ((l + 4).choose 4 : ℝ) := by
  have h : (l + 4).descFactorial 4 = Nat.factorial 4 * (l + 4).choose 4 := Nat.descFactorial_eq_factorial_mul_choose _ _
  have hd : (l + 4).descFactorial 4 = (l + 4) * (l + 3) * (l + 2) * (l + 1) := by
    simp [Nat.descFactorial]; ring
  have h2 : ((l + 4).choose 4 : ℝ) * 24 = ((l + 4) * (l + 3) * (l + 2) * (l + 1) : ℕ) := by
    rw [← hd, h]; push_cast; simp [Nat.factorial]; ring
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  push_cast at h2 ⊢
  nlinarith [mul_nonneg hl hl, mul_nonneg (mul_nonneg hl hl) hl]

/-- **(6.11)**: `w(y) ≤ 8192 (1 + y)⁵ e^{-2πy}`. -/
theorem weight_le' (y : ℝ) (hy : 0 < y) :
    weight y ≤ 8192 * (1 + y) ^ 5 * Real.exp (-2 * Real.pi * y) := by
  set u := 2 * Real.pi * y with hu
  have hu0 : 0 < u := by positivity
  set q := Real.exp (-u) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq]; calc Real.exp (-u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hterm : ∀ l : ℕ, ((l + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-2 * Real.pi * (l + 1) * y) =
      ((l + 1 : ℕ) : ℝ) ^ 4 * q ^ (l + 1) := by
    intro l; rw [hq, ← Real.exp_nat_mul]; congr 1; rw [hu]; push_cast; ring_nf
  -- comparison with the binomial series
  have hgeom := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 4
    (r := q) (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have hbig : HasSum (fun l : ℕ => 24 * q * (((l + 4).choose 4 : ℝ) * q ^ l))
      (24 * q * (1 / (1 - q) ^ 5)) := hgeom.mul_left (24 * q)
  have hle : ∀ l : ℕ, ((l + 1 : ℕ) : ℝ) ^ 4 * q ^ (l + 1) ≤
      24 * q * (((l + 4).choose 4 : ℝ) * q ^ l) := by
    intro l
    have := pow4_le_choose l
    calc ((l + 1 : ℕ) : ℝ) ^ 4 * q ^ (l + 1) = ((l + 1 : ℕ) : ℝ) ^ 4 * (q ^ l * q) := by
          ring
      _ ≤ 24 * ((l + 4).choose 4 : ℝ) * (q ^ l * q) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hsum_le : ∑' l : ℕ, ((l + 1 : ℕ) : ℝ) ^ 4 * q ^ (l + 1) ≤ 24 * q * (1 / (1 - q) ^ 5) := by
    have hs : Summable (fun l : ℕ => ((l + 1 : ℕ) : ℝ) ^ 4 * q ^ (l + 1)) :=
      Summable.of_nonneg_of_le (fun l => by positivity) hle hbig.summable
    exact hasSum_le hle hs.hasSum hbig
  -- 1 - q ≥ u / (1 + u)
  have h1q : u / (1 + u) ≤ 1 - q := by
    have hq' : q ≤ 1 / (1 + u) := by
      rw [hq, Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp u])
    calc u / (1 + u) = 1 - 1 / (1 + u) := by field_simp; ring
      _ ≤ 1 - q := by linarith
  have hinv : 1 / (1 - q) ^ 5 ≤ ((1 + u) / u) ^ 5 := by
    rw [div_pow, one_div]
    apply inv_le_of_inv_le₀ (by positivity)
    rw [inv_div, ← div_pow]
    exact pow_le_pow_left₀ (by positivity) h1q 5
  have hw : weight y ≤ (2 * Real.pi) ^ 4 * y ^ 5 / 12 * (24 * q * ((1 + u) / u) ^ 5) := by
    unfold weight
    rw [tsum_congr hterm]
    gcongr
    exact hsum_le.trans (by gcongr)
  refine hw.trans ?_
  -- algebra: the right-hand side is q (1+u)^5 / π
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmid : (2 * Real.pi) ^ 4 * y ^ 5 / 12 * (24 * q * ((1 + u) / u) ^ 5) =
      q * (1 + u) ^ 5 / Real.pi := by
    rw [hu]; field_simp; ring
  rw [hmid]
  have h1u : 1 + u ≤ 2 * Real.pi * (1 + y) := by
    rw [hu]; nlinarith [Real.pi_gt_three]
  have hpow : (1 + u) ^ 5 ≤ (2 * Real.pi) ^ 5 * (1 + y) ^ 5 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1u 5
  have hpi4 : Real.pi ^ 4 ≤ 256 := by
    have := Real.pi_le_four
    calc Real.pi ^ 4 ≤ 4 ^ 4 := pow_le_pow_left₀ hpi.le this 4
      _ = 256 := by norm_num
  have hexp : Real.exp (-2 * Real.pi * y) = q := by rw [hq, hu]; ring_nf
  rw [hexp, div_le_iff₀ hpi]
  calc q * (1 + u) ^ 5 ≤ q * ((2 * Real.pi) ^ 5 * (1 + y) ^ 5) :=
        mul_le_mul_of_nonneg_left hpow hq0.le
    _ = 32 * Real.pi ^ 4 * ((1 + y) ^ 5 * q) * Real.pi := by ring
    _ ≤ 32 * 256 * ((1 + y) ^ 5 * q) * Real.pi := by gcongr
    _ = 8192 * (1 + y) ^ 5 * q * Real.pi := by ring

/-! ## Lemma 6.2 (zero-mass logarithmic energy)

Proof: the Gaussian kernels `e^{-s|z-w|²}` are positive definite (a Gaussian convolution
identity plus Fubini); a truncated Frullani representation
`log r ≈ ½ ∫_{1/(n+1)}^{n+1} (e^{-s} - e^{-s r²}) ds/s` then gives `E(K_n) ≤ 0`, and dominated
convergence passes to `log`. -/

section Energy

open Real Set

theorem gauss_integral_C {b : ℝ} (hb : 0 < b) : ∫ v : ℂ, Real.exp (-b * ‖v‖ ^ 2) = π / b := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hb
  rw [this, Complex.finrank_real_complex]; norm_num

theorem norm_sq_parallelogram (z w u : ℂ) :
    ‖z - u‖ ^ 2 + ‖w - u‖ ^ 2 = 2 * ‖u - (z + w) / 2‖ ^ 2 + ‖z - w‖ ^ 2 / 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im]
  norm_num; ring

/-- `∫ e^{-2s|z-u|²} e^{-2s|w-u|²} du = (π/(4s)) e^{-s|z-w|²}`. -/
theorem gauss_conv {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ∫ u : ℂ, Real.exp (-2 * s * ‖z - u‖ ^ 2) * Real.exp (-2 * s * ‖w - u‖ ^ 2) =
      π / (4 * s) * Real.exp (-s * ‖z - w‖ ^ 2) := by
  have e : ∀ u : ℂ, Real.exp (-2 * s * ‖z - u‖ ^ 2) * Real.exp (-2 * s * ‖w - u‖ ^ 2) =
      Real.exp (-s * ‖z - w‖ ^ 2) * Real.exp (-(4 * s) * ‖u - (z + w) / 2‖ ^ 2) := by
    intro u
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have := norm_sq_parallelogram z w u
    linear_combination (-2 * s) * this
  simp_rw [e]
  rw [integral_const_mul, integral_sub_right_eq_self (fun u => Real.exp (-(4 * s) * ‖u‖ ^ 2)),
    gauss_integral_C (by positivity)]
  ring

/-- `Φ_s μ (u) = ∫ e^{-2s|z-u|²} dμ(z)`. -/
def gPhi (s : ℝ) (μ : Measure ℂ) (u : ℂ) : ℝ := ∫ z, Real.exp (-2 * s * ‖z - u‖ ^ 2) ∂μ

theorem gauss_conv_integrable {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    Integrable (fun u : ℂ => Real.exp (-2 * s * ‖z - u‖ ^ 2) * Real.exp (-2 * s * ‖w - u‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gauss_conv hs]; positivity

theorem gPhi_le {s : ℝ} (hs : 0 ≤ s) (μ : Measure ℂ) [IsFiniteMeasure μ] (u : ℂ) :
    |gPhi s μ u| ≤ μ.real Set.univ := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun z => Real.exp (-2 * s * ‖z - u‖ ^ 2))
    (C := 1) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := sq_nonneg ‖z - u‖; nlinarith)
  simpa [gPhi] using this

theorem gPhi_sm (s : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] : StronglyMeasurable (gPhi s μ) := by
  have : StronglyMeasurable (Function.uncurry fun (u z : ℂ) => Real.exp (-2 * s * ‖z - u‖ ^ 2)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  exact this.integral_prod_right

theorem gauss_pair {s : ℝ} (hs : 0 < s) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ p, Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂(μ.prod ν) =
      4 * s / π * ∫ u, gPhi s μ u * gPhi s ν u := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [integral_prod _ (Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := sq_nonneg ‖p.1 - p.2‖; nlinarith))]
  set φ : ℂ → ℂ → ℝ := fun z u => Real.exp (-2 * s * ‖z - u‖ ^ 2) with hφ
  have hg : ∀ z w : ℂ, Real.exp (-s * ‖z - w‖ ^ 2) = 4 * s / π * ∫ u, φ z u * φ w u := by
    intro z w; rw [hφ, gauss_conv hs]; field_simp
  simp only [hg, integral_const_mul]
  congr 1
  -- inner swap
  have h1 : ∀ z, ∫ w, ∫ u, φ z u * φ w u ∂volume ∂ν = ∫ u, φ z u * gPhi s ν u := by
    intro z
    rw [integral_integral_swap]
    · congr 1; ext u; rw [gPhi, ← integral_const_mul]
    · have hm : AEStronglyMeasurable (Function.uncurry fun w u => φ z u * φ w u) (ν.prod volume) :=
        (by rw [hφ]; fun_prop : Continuous _).aestronglyMeasurable
      rw [integrable_prod_iff hm]
      refine ⟨Filter.Eventually.of_forall fun w => gauss_conv_integrable hs z w, ?_⟩
      have he : (fun w => ∫ u, ‖Function.uncurry (fun w u => φ z u * φ w u) (w, u)‖) =
          fun w => π / (4 * s) * Real.exp (-s * ‖z - w‖ ^ 2) := by
        ext w
        simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), hφ]
        exact gauss_conv hs z w
      rw [he]
      refine Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable (π / (4 * s))
        (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : Real.exp (-s * ‖z - w‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := sq_nonneg ‖z - w‖; nlinarith
      have : 0 < π / (4 * s) := by positivity
      nlinarith
  simp only [h1]
  rw [integral_integral_swap]
  · congr 1; ext u; rw [integral_mul_const]; rfl
  · have hm : AEStronglyMeasurable (Function.uncurry fun z u => φ z u * gPhi s ν u)
        (μ.prod volume) :=
      ((by rw [hφ]; fun_prop : Continuous (Function.uncurry φ)).stronglyMeasurable.mul
        ((gPhi_sm s ν).comp_measurable measurable_snd)).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    have hφi : ∀ z, Integrable (fun u => φ z u) := fun z =>
      (Integrable.of_integral_ne_zero (f := fun v : ℂ => Real.exp (-(2 * s) * ‖v‖ ^ 2))
        (by rw [gauss_integral_C (by positivity)]; positivity)).comp_sub_left z |>.congr
        (Filter.Eventually.of_forall fun u => by simp [hφ])
    have hb : ∀ z u, ‖φ z u * gPhi s ν u‖ ≤ φ z u * ν.real Set.univ := by
      intro z u
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (gPhi_le hs.le ν u) (Real.exp_pos _).le
    constructor
    · refine Filter.Eventually.of_forall fun z => ?_
      exact Integrable.mono' ((hφi z).mul_const _)
        ((by rw [hφ]; fun_prop : Continuous (φ z)).aestronglyMeasurable.mul
          (gPhi_sm s ν).aestronglyMeasurable) (Filter.Eventually.of_forall (hb z))
    · have hint : ∀ z, ∫ u, φ z u = π / (2 * s) := by
        intro z
        have := integral_sub_left_eq_self (fun v : ℂ => Real.exp (-(2 * s) * ‖v‖ ^ 2))
          (μ := volume) z
        rw [gauss_integral_C (by positivity)] at this
        rw [← this]; simp [hφ]
      refine Integrable.of_bound ?_ (π / (2 * s) * ν.real Set.univ)
        (Filter.Eventually.of_forall fun z => ?_)
      · exact hm.norm.integral_prod_right'
      · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hint z,
          ← integral_mul_const]
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((hφi z).mul_const _) (Filter.Eventually.of_forall (hb z))

theorem gPhi_integrable {s : ℝ} (hs : 0 < s) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (gPhi s μ) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.exp (-2 * s * ‖p.1 - p.2‖ ^ 2))
      (μ.prod volume) := (by fun_prop : Continuous _).aestronglyMeasurable
  have hint : ∀ z : ℂ, ∫ u, Real.exp (-2 * s * ‖z - u‖ ^ 2) = π / (2 * s) := by
    intro z
    have := integral_sub_left_eq_self (fun v : ℂ => Real.exp (-(2 * s) * ‖v‖ ^ 2))
      (μ := volume) z
    rw [gauss_integral_C (by positivity)] at this
    rw [← this]; simp
  have hi : Integrable (fun p : ℂ × ℂ => Real.exp (-2 * s * ‖p.1 - p.2‖ ^ 2)) (μ.prod volume) := by
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
    · exact Integrable.of_integral_ne_zero (by rw [hint]; have := Real.pi_pos; positivity)
    · simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hint]
      exact integrable_const _
  exact hi.integral_prod_right

theorem gPhi_mul_integrable {s : ℝ} (hs : 0 < s) (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : Integrable (fun u => gPhi s μ u * gPhi s ν u) := by
  refine Integrable.mono' ((gPhi_integrable hs μ).norm.mul_const (ν.real Set.univ))
    ((gPhi_sm s μ).aestronglyMeasurable.mul (gPhi_sm s ν).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (gPhi_le hs.le ν u) (norm_nonneg _)

/-- The quadratic form `E(k) = ∫k d(ν₁⊗ν₁) - 2∫k d(ν₁⊗ν₂) + ∫k d(ν₂⊗ν₂)`. -/
def Eform (ν₁ ν₂ : Measure ℂ) (k : ℂ × ℂ → ℝ) : ℝ :=
  ∫ p, k p ∂(ν₁.prod ν₁) - 2 * ∫ p, k p ∂(ν₁.prod ν₂) + ∫ p, k p ∂(ν₂.prod ν₂)

theorem Eform_gauss_nonneg {s : ℝ} (hs : 0 < s) (ν₁ ν₂ : Measure ℂ) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] : 0 ≤ Eform ν₁ ν₂ (fun p => Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) := by
  have hπ := Real.pi_pos
  have key : Eform ν₁ ν₂ (fun p => Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) =
      4 * s / π * ∫ u, (gPhi s ν₁ u - gPhi s ν₂ u) ^ 2 := by
    rw [Eform, gauss_pair hs, gauss_pair hs, gauss_pair hs]
    have e : ∀ u, (gPhi s ν₁ u - gPhi s ν₂ u) ^ 2 = gPhi s ν₁ u * gPhi s ν₁ u -
        2 * (gPhi s ν₁ u * gPhi s ν₂ u) + gPhi s ν₂ u * gPhi s ν₂ u := fun u => by ring
    simp_rw [e]
    rw [integral_add _ (gPhi_mul_integrable hs _ _), integral_sub (gPhi_mul_integrable hs _ _)
      ((gPhi_mul_integrable hs _ _).const_mul 2), integral_const_mul]
    · ring
    · exact (gPhi_mul_integrable hs _ _).sub ((gPhi_mul_integrable hs _ _).const_mul 2)
  rw [key]
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)

theorem expdiv_contOn : ContinuousOn (fun u : ℝ => Real.exp (-u) / u) (Ioi 0) :=
  (by fun_prop : Continuous fun u : ℝ => Real.exp (-u)).continuousOn.div continuousOn_id
    fun u hu => ne_of_gt hu

theorem expdiv_ii {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume x y :=
  (expdiv_contOn.mono fun u hu => by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h] at hu; exact lt_of_lt_of_le hx hu.1
    · rw [uIcc_of_ge h] at hu; exact lt_of_lt_of_le hy hu.1).intervalIntegrable

theorem abs_int_le_log_aux {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {f : ℝ → ℝ}
    (hf0 : ∀ u, 0 < u → 0 ≤ f u) (hf1 : ∀ u, 0 < u → f u ≤ u⁻¹)
    (hfi : IntervalIntegrable f volume x y) :
    |∫ u in x..y, f u| ≤ |Real.log (y / x)| := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h0 : 0 ≤ ∫ u in x..y, f u :=
    intervalIntegral.integral_nonneg hxy fun u hu => hf0 u (lt_of_lt_of_le hx hu.1)
  have h1 : ∫ u in x..y, f u ≤ ∫ u in x..y, u⁻¹ :=
    intervalIntegral.integral_mono_on hxy hfi
      (intervalIntegral.intervalIntegrable_inv (fun u hu => by
        rw [uIcc_of_le hxy] at hu; exact (lt_of_lt_of_le hx hu.1).ne') continuousOn_id)
      fun u hu => hf1 u (lt_of_lt_of_le hx hu.1)
  rw [integral_inv_of_pos hx hy] at h1
  rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _)

theorem abs_int_le_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {f : ℝ → ℝ}
    (hf0 : ∀ u, 0 < u → 0 ≤ f u) (hf1 : ∀ u, 0 < u → f u ≤ u⁻¹)
    (hfi : IntervalIntegrable f volume x y) :
    |∫ u in x..y, f u| ≤ |Real.log (y / x)| := by
  rcases le_total x y with h | h
  · exact abs_int_le_log_aux hx h hf0 hf1 hfi
  · rw [intervalIntegral.integral_symm, abs_neg]
    have := abs_int_le_log_aux hy h hf0 hf1 hfi.symm
    rw [Real.log_div hy.ne' hx.ne', Real.log_div hx.ne' hy.ne'] at *
    rwa [abs_sub_comm]

/-- `∫_a^b e^{-s}/s - ∫_a^b e^{-st}/s = ∫_a^{at} e^{-u}/u - ∫_b^{bt} e^{-u}/u`. -/
theorem J_eq {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    (∫ s in a..b, Real.exp (-s) / s) - ∫ s in a..b, Real.exp (-s * t) / s =
      (∫ u in a..a * t, Real.exp (-u) / u) - ∫ u in b..b * t, Real.exp (-u) / u := by
  have hsub : ∫ s in a..b, Real.exp (-s * t) / s = ∫ u in a * t..b * t, Real.exp (-u) / u := by
    have := intervalIntegral.integral_comp_mul_right (a := a) (b := b)
      (fun u : ℝ => Real.exp (-u) / u) ht.ne'
    simp only [smul_eq_mul] at this
    rw [← mul_right_inj' (inv_ne_zero ht.ne'), ← this, ← intervalIntegral.integral_const_mul]
    congr 1; ext s
    rw [neg_mul]; field_simp
  have hat : 0 < a * t := by positivity
  have hbt : 0 < b * t := by positivity
  rw [hsub, ← intervalIntegral.integral_add_adjacent_intervals (expdiv_ii ha hat)
      (expdiv_ii hat hb),
    ← intervalIntegral.integral_add_adjacent_intervals (expdiv_ii hat hbt) (expdiv_ii hbt hb),
    intervalIntegral.integral_symm (b * t) b]
  ring

theorem pos_of_mem_uIoc {x y u : ℝ} (hx : 0 < x) (hy : 0 < y) (hu : u ∈ Set.uIoc x y) : 0 < u :=
  lt_trans (lt_min hx hy) hu.1

theorem J_sub_log_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    |((∫ u in a..a * t, Real.exp (-u) / u) - ∫ u in b..b * t, Real.exp (-u) / u) - Real.log t| ≤
      a * |t - 1| + |t - 1| / (b * min 1 t ^ 2) := by
  have hat : 0 < a * t := by positivity
  have hbt : 0 < b * t := by positivity
  have hm : 0 < min 1 t := lt_min one_pos ht
  -- first piece
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume a (a * t) :=
    intervalIntegral.intervalIntegrable_inv (fun u hu => by
      rcases le_total a (a * t) with h | h
      · rw [uIcc_of_le h] at hu; exact (lt_of_lt_of_le ha hu.1).ne'
      · rw [uIcc_of_ge h] at hu; exact (lt_of_lt_of_le hat hu.1).ne') continuousOn_id
  have e1 : ∫ u in a..a * t, Real.exp (-u) / u =
      Real.log t - ∫ u in a..a * t, (u⁻¹ - Real.exp (-u) / u) := by
    rw [intervalIntegral.integral_sub hinv (expdiv_ii ha hat), integral_inv_of_pos ha hat,
      mul_div_cancel_left₀ _ ha.ne']
    ring
  have b1 : |∫ u in a..a * t, (u⁻¹ - Real.exp (-u) / u)| ≤ 1 * |a * t - a| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    have hu0 := pos_of_mem_uIoc ha hat hu
    have h1 := Real.add_one_le_exp (-u)
    have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hv := inv_pos.mpr hu0
    have hv1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0.ne'
    rw [Real.norm_eq_abs, abs_le, div_eq_mul_inv]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right h3 hv.le]
  have b2 : |∫ u in b..b * t, Real.exp (-u) / u| ≤ 1 / (b * min 1 t) ^ 2 * |b * t - b| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    have hu0 := pos_of_mem_uIoc hb hbt hu
    have hbm : b * min 1 t < u := by
      refine lt_of_le_of_lt ?_ hu.1
      rw [mul_min_of_nonneg _ _ hb.le, mul_one]
    have hbm0 : 0 < b * min 1 t := by positivity
    have h1 := Real.add_one_le_exp u
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hu0), div_le_iff₀ hu0,
      Real.exp_neg]
    calc (Real.exp u)⁻¹ ≤ u⁻¹ := inv_anti₀ hu0 (by linarith)
      _ = u⁻¹ * u ^ 2 / u ^ 2 := by field_simp
      _ = u / u ^ 2 := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hu0.ne', one_mul]
      _ ≤ u / (b * min 1 t) ^ 2 :=
        div_le_div_of_nonneg_left hu0.le (by positivity) (pow_le_pow_left₀ hbm0.le hbm.le 2)
      _ = _ := by ring
  have hm2 : 0 < b * min 1 t ^ 2 := by positivity
  rw [e1]
  calc |Real.log t - (∫ u in a..a * t, (u⁻¹ - Real.exp (-u) / u)) -
        (∫ u in b..b * t, Real.exp (-u) / u) - Real.log t|
      = |(∫ u in a..a * t, (u⁻¹ - Real.exp (-u) / u)) + ∫ u in b..b * t, Real.exp (-u) / u| := by
        rw [← abs_neg]; ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 1 * |a * t - a| + 1 / (b * min 1 t) ^ 2 * |b * t - b| := add_le_add b1 b2
    _ = a * |t - 1| + |t - 1| / (b * min 1 t ^ 2) := by
      rw [← mul_sub_one, ← mul_sub_one, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
      field_simp

/-- `e^{-s' t}/s'` with `s' = max s a`: bounded and continuous, equal to `e^{-st}/s` for `s ≥ a`. -/
def gtk (a s t : ℝ) : ℝ := Real.exp (-max s a * t) / max s a

theorem gt_cont {a : ℝ} (ha : 0 < a) : Continuous fun q : ℝ × ℝ => gtk a q.1 q.2 := by
  unfold gtk
  exact (by fun_prop : Continuous fun q : ℝ × ℝ => Real.exp (-max q.1 a * q.2)).div
    (by fun_prop) fun q => (lt_of_lt_of_le ha (le_max_right _ _)).ne'

theorem gt_le {a : ℝ} (ha : 0 < a) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) : ‖gtk a s t‖ ≤ a⁻¹ := by
  have hm : a ≤ max s a := le_max_right _ _
  have hm0 : 0 < max s a := lt_of_lt_of_le ha hm
  rw [gtk, Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hm0), div_eq_mul_inv]
  have h1 : Real.exp (-max s a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : (max s a)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hm
  nlinarith [inv_pos.mpr hm0, Real.exp_pos (-max s a * t)]

/-- `H(p) = ∫_{(a,b]} e^{-s|z-w|²}/s ds`. -/
def Hk (a b : ℝ) (p : ℂ × ℂ) : ℝ := ∫ s in Ioc a b, gtk a s (‖p.1 - p.2‖ ^ 2)

theorem Hk_swap {a : ℝ} (ha : 0 < a) (b : ℝ) (P : Measure (ℂ × ℂ)) [IsFiniteMeasure P] :
    (Integrable (fun s => ∫ p, gtk a s (‖p.1 - p.2‖ ^ 2) ∂P) (volume.restrict (Ioc a b))) ∧
    ∫ p, Hk a b p ∂P = ∫ s in Ioc a b, ∫ p, gtk a s (‖p.1 - p.2‖ ^ 2) ∂P := by
  have hi : Integrable (Function.uncurry fun (p : ℂ × ℂ) (s : ℝ) => gtk a s (‖p.1 - p.2‖ ^ 2))
      (P.prod (volume.restrict (Ioc a b))) := by
    refine Integrable.of_bound ?_ a⁻¹ (Filter.Eventually.of_forall fun q => gt_le ha _ (by positivity))
    exact ((gt_cont ha).comp (by fun_prop : Continuous fun q : (ℂ × ℂ) × ℝ =>
      (q.2, ‖q.1.1 - q.1.2‖ ^ 2))).aestronglyMeasurable
  exact ⟨hi.integral_prod_right, integral_integral_swap hi⟩

theorem Hk_integrable {a : ℝ} (ha : 0 < a) (b : ℝ) (P : Measure (ℂ × ℂ)) [IsFiniteMeasure P] :
    Integrable (Hk a b) P := by
  refine Integrable.of_bound ?_ (a⁻¹ * (volume.restrict (Ioc a b)).real univ)
    (Filter.Eventually.of_forall fun p => ?_)
  · have : StronglyMeasurable (Function.uncurry fun (p : ℂ × ℂ) (s : ℝ) => gtk a s (‖p.1 - p.2‖ ^ 2)) :=
      ((gt_cont ha).comp (by fun_prop : Continuous fun q : (ℂ × ℂ) × ℝ =>
        (q.2, ‖q.1.1 - q.1.2‖ ^ 2))).stronglyMeasurable
    exact (this.integral_prod_right (ν := volume.restrict (Ioc a b))).aestronglyMeasurable
  · have : IsFiniteMeasure (volume.restrict (Ioc a b)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun s => gt_le ha s (by positivity))

theorem Eform_Hk_nonneg {a : ℝ} (ha : 0 < a) (b : ℝ) (ν₁ ν₂ : Measure ℂ) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] : 0 ≤ Eform ν₁ ν₂ (Hk a b) := by
  obtain ⟨i11, e11⟩ := Hk_swap ha b (ν₁.prod ν₁)
  obtain ⟨i12, e12⟩ := Hk_swap ha b (ν₁.prod ν₂)
  obtain ⟨i22, e22⟩ := Hk_swap ha b (ν₂.prod ν₂)
  rw [Eform, e11, e12, e22, ← integral_const_mul, ← integral_sub i11 (i12.const_mul 2),
    ← integral_add (f := fun s => ∫ p, gtk a s (‖p.1 - p.2‖ ^ 2) ∂(ν₁.prod ν₁) -
      2 * ∫ p, gtk a s (‖p.1 - p.2‖ ^ 2) ∂(ν₁.prod ν₂)) (i11.sub (i12.const_mul 2)) i22]
  refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 < s := lt_trans ha hs.1
  have hmax : max s a = s := max_eq_left hs.1.le
  simp only [gtk, hmax, integral_div]
  have := Eform_gauss_nonneg hs0 ν₁ ν₂
  rw [Eform] at this
  have e : ∀ Q : Measure (ℂ × ℂ), ∫ p, Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂Q =
    ∫ p, Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂Q := fun _ => rfl
  have h := div_nonneg this hs0.le
  convert h using 1
  ring

/-- The truncated logarithmic kernel
`K_n = ½ (∫_{a}^{b} e^{-s}/s ds - ∫_{a}^{b} e^{-s|z-w|²}/s ds)`, `a = 1/(n+1)`, `b = n+1`. -/
def Kn (n : ℕ) (p : ℂ × ℂ) : ℝ :=
  ((∫ s in Ioc ((n + 1 : ℝ)⁻¹) (n + 1), Real.exp (-s) / s) - Hk ((n + 1 : ℝ)⁻¹) (n + 1) p) / 2

theorem Kn_eq (n : ℕ) (p : ℂ × ℂ) (ht : 0 < ‖p.1 - p.2‖ ^ 2) :
    2 * Kn n p = (∫ u in (n + 1 : ℝ)⁻¹..(n + 1 : ℝ)⁻¹ * ‖p.1 - p.2‖ ^ 2, Real.exp (-u) / u) -
      ∫ u in (n + 1 : ℝ)..(n + 1) * ‖p.1 - p.2‖ ^ 2, Real.exp (-u) / u := by
  set t := ‖p.1 - p.2‖ ^ 2
  have ha : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
  have hb : (0 : ℝ) < n + 1 := by positivity
  have hab : (n + 1 : ℝ)⁻¹ ≤ n + 1 := by
    have : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (inv_le_one_of_one_le₀ this).trans this
  have hH : Hk (n + 1 : ℝ)⁻¹ (n + 1) p = ∫ s in Ioc (n + 1 : ℝ)⁻¹ (n + 1), Real.exp (-s * t) / s :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by simp only [gtk, max_eq_left hs.1.le, t]
  rw [← J_eq ha hb ht, Kn, hH, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  ring

theorem expdiv_bounds (u : ℝ) (hu : 0 < u) : 0 ≤ Real.exp (-u) / u ∧ Real.exp (-u) / u ≤ u⁻¹ := by
  refine ⟨(div_pos (Real.exp_pos _) hu).le, ?_⟩
  rw [div_eq_mul_inv]
  have : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith [inv_pos.mpr hu]

theorem Kn_bound (n : ℕ) (p : ℂ × ℂ) (ht : 0 < ‖p.1 - p.2‖ ^ 2) :
    ‖Kn n p‖ ≤ 2 * |Real.log ‖p.1 - p.2‖| := by
  set t := ‖p.1 - p.2‖ ^ 2 with htdef
  have ha : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
  have hb : (0 : ℝ) < n + 1 := by positivity
  have h2 := Kn_eq n p ht
  have e : ∀ x : ℝ, 0 < x → |∫ u in x..x * t, Real.exp (-u) / u| ≤ |Real.log t| := by
    intro x hx
    have := abs_int_le_log hx (by positivity : 0 < x * t)
      (fun u hu => (expdiv_bounds u hu).1) (fun u hu => (expdiv_bounds u hu).2)
      (expdiv_ii hx (by positivity))
    rwa [mul_div_cancel_left₀ _ hx.ne'] at this
  have hlog : Real.log t = 2 * Real.log ‖p.1 - p.2‖ := by rw [htdef, Real.log_pow]; norm_num
  rw [Real.norm_eq_abs]
  have := abs_sub (∫ u in (n + 1 : ℝ)⁻¹..(n + 1 : ℝ)⁻¹ * t, Real.exp (-u) / u)
    (∫ u in (n + 1 : ℝ)..(n + 1) * t, Real.exp (-u) / u)
  rw [← h2, abs_mul] at this
  have := e _ ha; have := e _ hb
  rw [hlog, abs_mul] at *
  norm_num at *
  linarith

theorem Kn_tendsto (p : ℂ × ℂ) (ht : 0 < ‖p.1 - p.2‖ ^ 2) :
    Filter.Tendsto (fun n => Kn n p) Filter.atTop (nhds (Real.log ‖p.1 - p.2‖)) := by
  set t := ‖p.1 - p.2‖ ^ 2 with htdef
  have hlog : Real.log t = 2 * Real.log ‖p.1 - p.2‖ := by rw [htdef, Real.log_pow]; norm_num
  set K := |t - 1| + |t - 1| / min 1 t ^ 2
  have hbd : ∀ n : ℕ, |Kn n p - Real.log ‖p.1 - p.2‖| ≤ K / 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have ha : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
    have hb : (0 : ℝ) < n + 1 := by positivity
    have := J_sub_log_le ha hb ht
    rw [← Kn_eq n p ht, hlog] at this
    have e : 2 * Kn n p - 2 * Real.log ‖p.1 - p.2‖ = 2 * (Kn n p - Real.log ‖p.1 - p.2‖) := by ring
    rw [e, abs_mul] at this
    have e2 : (n + 1 : ℝ)⁻¹ * |t - 1| + |t - 1| / ((n + 1) * min 1 t ^ 2) =
      K * (1 / ((n : ℝ) + 1)) := by simp only [K]; field_simp
    rw [e2] at this
    norm_num at this
    rw [one_div]; linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (K / 2)

theorem prod_real_univ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ.prod ν).real univ = μ.real univ * ν.real univ := by
  simp [measureReal_def, ← univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

theorem Eform_Kn_nonpos (n : ℕ) (ν₁ ν₂ : Measure ℂ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hmass : ν₁ univ = ν₂ univ) : Eform ν₁ ν₂ (Kn n) ≤ 0 := by
  have ha : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
  have hm : ν₁.real univ = ν₂.real univ := by simp [measureReal_def, hmass]
  have e : ∀ P : Measure (ℂ × ℂ), IsFiniteMeasure P → ∫ p, Kn n p ∂P =
      ((∫ s in Ioc ((n + 1 : ℝ)⁻¹) (n + 1), Real.exp (-s) / s) * P.real univ -
        ∫ p, Hk ((n + 1 : ℝ)⁻¹) (n + 1) p ∂P) / 2 := by
    intro P _
    unfold Kn
    rw [integral_div, integral_sub (integrable_const _) (Hk_integrable ha _ P), integral_const,
      smul_eq_mul, mul_comm]
  have hH := Eform_Hk_nonneg ha (n + 1) ν₁ ν₂
  rw [Eform] at hH ⊢
  rw [e _ inferInstance, e _ inferInstance, e _ inferInstance, prod_real_univ, prod_real_univ,
    prod_real_univ, hm]
  linarith

theorem Kn_integral_tendsto (P Q : Measure (ℂ × ℂ)) [IsFiniteMeasure P] (hPQ : P ≤ Q)
    (hint : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) Q)
    (hdiag : Q {p : ℂ × ℂ | p.1 = p.2} = 0) :
    Filter.Tendsto (fun n => ∫ p, Kn n p ∂P) Filter.atTop
      (nhds (∫ p, Real.log ‖p.1 - p.2‖ ∂P)) := by
  have hne : ∀ᵐ p ∂P, 0 < ‖p.1 - p.2‖ ^ 2 := by
    have h0 : P {p : ℂ × ℂ | p.1 = p.2} = 0 := le_antisymm ((Measure.le_iff'.mp hPQ _).trans hdiag.le) (zero_le)
    refine ae_iff.mpr (measure_mono_null (fun p hp => ?_) h0)
    simp only [mem_ofPred_eq, not_lt] at hp ⊢
    have := norm_nonneg (p.1 - p.2)
    have h2 : ‖p.1 - p.2‖ = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  refine tendsto_integral_of_dominated_convergence (fun p => 2 * |Real.log ‖p.1 - p.2‖|)
    (fun n => ?_) ((hint.mono_measure hPQ).abs.const_mul 2) (fun n => ?_) ?_
  · have ha : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
    exact (((integrable_const _).sub (Hk_integrable ha (n + 1) P)).div_const 2).aestronglyMeasurable
  · exact hne.mono fun p hp => Kn_bound n p hp
  · exact hne.mono fun p hp => Kn_tendsto p hp

theorem prod_le_sum_prod (ν₁ ν₂ : Measure ℂ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    ν₁.prod ν₁ ≤ (ν₁ + ν₂).prod (ν₁ + ν₂) ∧ ν₁.prod ν₂ ≤ (ν₁ + ν₂).prod (ν₁ + ν₂) ∧
      ν₂.prod ν₂ ≤ (ν₁ + ν₂).prod (ν₁ + ν₂) := by
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  exact ⟨Measure.le_add_right (Measure.le_add_right le_rfl),
    Measure.le_add_right (Measure.le_add_left le_rfl),
    Measure.le_add_left (Measure.le_add_left le_rfl)⟩

theorem logEnergyC_eq (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν)) :
    logEnergyC μ ν = ∫ p, Real.log ‖p.1 - p.2‖ ∂(μ.prod ν) :=
  (integral_prod _ h).symm

/-- **Lemma 6.2** (corrected). With Lean's `log 0 = 0` the statement `lemma_6_2` is false when
the measures have atoms (e.g. `ν₁ = δ₀`, `ν₂ = δ_{1/2}` gives `2 log 2 > 0`); we add the
hypothesis that the diagonal is null for `(ν₁+ν₂) ⊗ (ν₁+ν₂)` (true for atomless measures).
The compact-support hypothesis is not needed. -/
theorem lemma_6_2' (ν₁ ν₂ : Measure ℂ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hmass : ν₁ Set.univ = ν₂ Set.univ)
    (hint : Integrable (fun zw : ℂ × ℂ => Real.log ‖zw.1 - zw.2‖) ((ν₁ + ν₂).prod (ν₁ + ν₂)))
    (hdiag : ((ν₁ + ν₂).prod (ν₁ + ν₂)) {zw : ℂ × ℂ | zw.1 = zw.2} = 0) :
    logEnergyC ν₁ ν₁ - 2 * logEnergyC ν₁ ν₂ + logEnergyC ν₂ ν₂ ≤ 0 := by
  obtain ⟨h11, h12, h22⟩ := prod_le_sum_prod ν₁ ν₂
  rw [logEnergyC_eq _ _ (hint.mono_measure h11), logEnergyC_eq _ _ (hint.mono_measure h12),
    logEnergyC_eq _ _ (hint.mono_measure h22)]
  have t11 := Kn_integral_tendsto _ _ h11 hint hdiag
  have t12 := Kn_integral_tendsto _ _ h12 hint hdiag
  have t22 := Kn_integral_tendsto _ _ h22 hint hdiag
  have hlim := (t11.sub (t12.const_mul 2)).add t22
  exact le_of_tendsto' hlim fun n => Eform_Kn_nonpos n ν₁ ν₂ hmass

/-- The original `lemma_6_2` fails for atoms: `ν₁ = δ₀`, `ν₂ = δ_{1/2}`. -/
theorem lemma_6_2_counterexample :
    ¬ (logEnergyC (Measure.dirac 0) (Measure.dirac 0) -
        2 * logEnergyC (Measure.dirac 0) (Measure.dirac (1 / 2 : ℂ)) +
        logEnergyC (Measure.dirac (1 / 2 : ℂ)) (Measure.dirac (1 / 2 : ℂ)) ≤ 0) := by
  simp only [logEnergyC, integral_dirac, sub_self, norm_zero, Real.log_zero]
  norm_num
  exact Real.log_neg (by norm_num) (by norm_num)

end Energy

end Zeta5
