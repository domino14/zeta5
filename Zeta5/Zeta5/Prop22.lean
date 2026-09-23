import Zeta5.Section2

/-!
# Proposition 2.2: the positive integral representation of `µ_{ζ(5)}`

* `weight_pos'`: the weight `w` is positive on `(0, ∞)`.
* `moment'`: `∫₀^∞ y^{2e} w(y) dy = µ(tᵉ)` (Euler's formula for `ζ(2e+2)`).
* `pole'`: `∫₀^∞ w(y)/(y² + j²) dy = j⁴(ζ(5) - H_j) - 1/4 + 1/(2j)`. Instead of Hermite's formula
  we use the symmetry `c⁴ Φ(a, c) = a⁴ Φ(c, a)` of `Φ(a, c) = ∫ y⁵ e^{-cy}/(y² + a²) dy` and the
  Mittag-Leffler expansion of `coth`.
* `prop_2_2'`, `G_zeta5_posDef'`, `Delta_zeta5_pos'`.
-/

open Polynomial Finset MeasureTheory Set Real
open scoped Nat

noncomputable section

namespace Zeta5

namespace P22

/-! ## Gamma integrals and nonnegative interchange -/

lemma gam_integrable (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ n * exp (-(c * y))) (Ioi 0) := by
  have hk : (0 : ℝ) < ↑n + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  have hint : IntegrableOn (fun x ↦ x ^ ((↑n + 1 : ℝ) - 1) * rexp (-(c * x))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  simpa [add_sub_cancel_right, rpow_natCast] using hint

lemma gam (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), y ^ n * exp (-(c * y)) = n ! / c ^ (n + 1) := by
  have hk : (0 : ℝ) < ↑n + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  simp only [add_sub_cancel_right, rpow_natCast] at key
  rw [key, Gamma_nat_eq_factorial, div_eq_mul_inv, one_mul, mul_comm, inv_rpow hc.le,
    ← rpow_natCast]
  norm_cast

/-- Interchange of `∫` and `∑'` for nonnegative integrable terms with summable integrals. -/
lemma integral_tsum_nn {f : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hint : ∀ n, IntegrableOn (f n) s) (hnn : ∀ n, ∀ x ∈ s, 0 ≤ f n x)
    (hps : ∀ x ∈ s, Summable fun n => f n x) {T : ℝ}
    (hsum : HasSum (fun n => ∫ x in s, f n x) T) :
    IntegrableOn (fun x => ∑' n, f n x) s ∧ ∫ x in s, ∑' n, f n x = T := by
  have hnorm : ∀ n, ∫ x in s, ‖f n x‖ = ∫ x in s, f n x := fun n =>
    setIntegral_congr_fun hs fun x hx => Real.norm_of_nonneg (hnn n x hx)
  have hs' : Summable fun n => ∫ x in s, ‖f n x‖ := by
    simp_rw [hnorm]; exact hsum.summable
  have h := hasSum_integral_of_summable_integral_norm hint hs'
  refine ⟨?_, (h.unique hsum)⟩
  -- integrability via lintegral
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict s) := fun n => (hint n).1
  have hm : AEStronglyMeasurable (fun x => ∑' n, f n x) (volume.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun N x => ∑ n ∈ range N, f n x) (fun N => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ fun n _ => hmeas n
    · filter_upwards [ae_restrict_mem hs] with x hx
      exact (hps x hx).hasSum.tendsto_sum_nat
  refine ⟨hm, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x in s, ‖∑' n, f n x‖ₑ ≤ ∫⁻ x in s, ∑' n, ‖f n x‖ₑ :=
        lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ x in s, ‖f n x‖ₑ := lintegral_tsum fun n => (hmeas n).enorm
    _ = ∑' n, ENNReal.ofReal (∫ x in s, ‖f n x‖) := by
        congr 1; ext n; rw [ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    _ = ENNReal.ofReal (∑' n, ∫ x in s, ‖f n x‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hs').symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ## The weight -/

lemma wsum_summable {y : ℝ} (hy : 0 < y) :
    Summable fun l : ℕ => ((l + 1 : ℕ) : ℝ) ^ 4 * exp (-2 * π * (l + 1) * y) := by
  have h := summable_pow_mul_exp_neg_nat_mul 4 (r := 2 * π * y) (by positivity)
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr fun l => ?_
  push_cast; ring_nf

lemma weight_eq (y : ℝ) : weight y =
    (2 * π) ^ 4 * y ^ 5 / 12 * ∑' l : ℕ, ((l + 1 : ℕ) : ℝ) ^ 4 * exp (-2 * π * (l + 1) * y) := rfl

/-! ## Mittag-Leffler for `coth` -/

lemma coth_series {v : ℝ} (hv : 0 < v) :
    HasSum (fun n : ℕ => 2 * v / (v ^ 2 + ((n : ℝ) + 1) ^ 2))
      (π * Real.cosh (π * v) / Real.sinh (π * v) - 1 / v) := by
  set x : ℂ := (v : ℂ) * Complex.I with hx
  have hxim : x.im = v := by simp [hx]
  have hxZ : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp only [Complex.intCast_im] at this
    rw [hxim] at this; linarith
  have H : HasSum (fun n : ℕ => cotTerm x n) (π * Complex.cot (π * x) - 1 / x) := by
    rw [cot_series_rep' hxZ]; exact (summable_cotTerm hxZ).hasSum
  have H2 := H.mul_left Complex.I
  rw [← Complex.hasSum_ofReal]
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  convert H2 using 1
  · ext n
    simp only [cotTerm, hx]
    have h1 : (v : ℂ) * Complex.I - ((n : ℂ) + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have h2 : (v : ℂ) * Complex.I + ((n : ℂ) + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have h3 : ((v : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2) ≠ 0 := by
      have : (0 : ℝ) < v ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
      exact_mod_cast this.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  · have hs : Real.sinh (π * v) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    have hsC : Complex.sinh ((π : ℂ) * v) ≠ 0 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]; exact_mod_cast hs
    rw [hx, Complex.cot_eq_cos_div_sin, show (π : ℂ) * (↑v * Complex.I) = (π * v) * Complex.I by ring,
      Complex.cos_mul_I, Complex.sin_mul_I]
    push_cast
    field_simp

lemma S_series {u : ℝ} (hu : 0 < u) :
    HasSum (fun l : ℕ => u / (u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2))
      (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u)) := by
  have hv : 0 < u / (2 * π) := by positivity
  have h := (coth_series hv).mul_left (1 / (4 * π))
  convert h using 1
  · ext n
    field_simp
    ring
  · have ht : 1 < exp (u / 2) := Real.one_lt_exp_iff.mpr (by linarith)
    have hu2 : exp u = exp (u / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [show π * (u / (2 * π)) = u / 2 by field_simp, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, hu2]
    set t := exp (u / 2)
    have h1 : t ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : t - t⁻¹ ≠ 0 := by
      have : 0 < t := by linarith
      rw [sub_ne_zero]; intro h; field_simp at h; nlinarith
    field_simp
    ring

/-! ## The symmetry `c⁴ Φ(a, c) = a⁴ Φ(c, a)` -/

lemma exp_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn (fun u : ℝ => exp (-(a * u))) (Ioi 0) := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 ha

lemma laplace_sin_integrable {a : ℝ} (ha : 0 < a) (y : ℝ) :
    IntegrableOn (fun u => exp (-(a * u)) * sin (y * u)) (Ioi 0) := by
  refine (exp_integrable ha).mono' (by fun_prop) ?_
  filter_upwards with u
  rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le]
  exact mul_le_of_le_one_right (exp_pos _).le (Real.abs_sin_le_one _)

lemma laplace_sin {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ∫ u in Ioi (0 : ℝ), exp (-(a * u)) * sin (y * u) = y / (y ^ 2 + a ^ 2) := by
  set z : ℂ := -(a : ℂ) + y * Complex.I with hz
  have hzre : z.re < 0 := by simp [hz]; linarith
  have hI := integral_exp_mul_complex_Ioi hzre 0
  have hint := integrableOn_exp_mul_complex_Ioi hzre 0
  have him := integral_im hint
  rw [hI] at him
  have hpt : ∀ u : ℝ, (Complex.exp (z * u)).im = exp (-(a * u)) * sin (y * u) := by
    intro u
    rw [Complex.exp_im]
    simp [hz]
  simp only [RCLike.im_eq_complex_im, hpt] at him
  rw [him]
  have hne : (a : ℝ) ^ 2 + y ^ 2 ≠ 0 := by positivity
  simp [hz, Complex.div_im, Complex.normSq]
  field_simp
  ring

/-- `Ψ(a, c) = ∫₀^∞ e^{-cy} y/(y² + a²) dy`. -/
def Psi (a c : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), exp (-(c * y)) * (y / (y ^ 2 + a ^ 2))

lemma psi_integrable {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun y => exp (-(c * y)) * (y / (y ^ 2 + a ^ 2))) (Ioi 0) := by
  refine ((exp_integrable hc).mul_const (1 / (2 * a))).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy : (0 : ℝ) < y := hy
  rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (y - a)]

lemma psi_symm {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : Psi a c = Psi c a := by
  set F : ℝ → ℝ → ℝ := fun y u => exp (-(c * y)) * (exp (-(a * u)) * sin (y * u)) with hF
  have h1 : Psi a c = ∫ y in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F y u := by
    unfold Psi
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [hF]; simp only
    rw [integral_const_mul, laplace_sin ha]
  have h2 : Psi c a = ∫ u in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), F y u := by
    unfold Psi
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [hF]; simp only
    simp_rw [show ∀ y, exp (-(c * y)) * (exp (-(a * u)) * sin (y * u)) =
      exp (-(a * u)) * (exp (-(c * y)) * sin (u * y)) from fun y => by rw [mul_comm y u]; ring]
    rw [integral_const_mul, laplace_sin hc]
  rw [h1, h2]
  apply integral_integral_swap
  refine ((exp_integrable hc).mul_prod (exp_integrable ha)).mono' ?_ ?_
  · exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable
  · filter_upwards with p
    simp only [Function.uncurry, hF, norm_mul, Real.norm_of_nonneg (exp_pos _).le]
    rw [← mul_assoc]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

/-- `Φ(a, c) = ∫₀^∞ y⁵ e^{-cy}/(y² + a²) dy`. -/
def Phi (a c : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), y ^ 5 * exp (-(c * y)) / (y ^ 2 + a ^ 2)

lemma phi_integrable {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun y => y ^ 5 * exp (-(c * y)) / (y ^ 2 + a ^ 2)) (Ioi 0) := by
  refine ((gam_integrable 3 hc).sub ((gam_integrable 1 hc).const_mul (a ^ 2))).add
    ((psi_integrable ha hc).const_mul (a ^ 4)) |>.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  simp only [Pi.add_apply, Pi.sub_apply]
  field_simp
  ring

lemma phi_eq {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Phi a c = 6 / c ^ 4 - a ^ 2 / c ^ 2 + a ^ 4 * Psi a c := by
  have h : Phi a c = ∫ y in Ioi (0 : ℝ), ((y ^ 3 * exp (-(c * y)) - a ^ 2 * (y ^ 1 * exp (-(c * y)))) +
      a ^ 4 * (exp (-(c * y)) * (y / (y ^ 2 + a ^ 2)))) := by
    unfold Phi
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have i1 : IntegrableOn (fun y : ℝ => y ^ 3 * exp (-(c * y)) - a ^ 2 * (y ^ 1 * exp (-(c * y))))
      (Ioi 0) := (gam_integrable 3 hc).sub ((gam_integrable 1 hc).const_mul _)
  have i2 : IntegrableOn (fun y : ℝ => a ^ 4 * (exp (-(c * y)) * (y / (y ^ 2 + a ^ 2)))) (Ioi 0) :=
    (psi_integrable ha hc).const_mul _
  have i3 : IntegrableOn (fun y : ℝ => a ^ 2 * (y ^ 1 * exp (-(c * y)))) (Ioi 0) :=
    (gam_integrable 1 hc).const_mul _
  rw [h, integral_add i1 i2, integral_sub (gam_integrable 3 hc) i3,
    integral_const_mul, integral_const_mul, gam 3 hc, gam 1 hc, Psi]
  simp [Nat.factorial]
  field_simp

lemma phi_symm {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : c ^ 4 * Phi a c = a ^ 4 * Phi c a := by
  rw [phi_eq ha hc, phi_eq hc ha, psi_symm ha hc]
  field_simp

/-- Converse interchange: if the (pointwise) sum is integrable, the integrals sum to its integral. -/
lemma hasSum_integral_nn {f : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hint : ∀ n, IntegrableOn (f n) s) (hnn : ∀ n, ∀ x ∈ s, 0 ≤ f n x)
    (hps : ∀ x ∈ s, Summable fun n => f n x) (hI : IntegrableOn (fun x => ∑' n, f n x) s) :
    HasSum (fun n => ∫ x in s, f n x) (∫ x in s, ∑' n, f n x) := by
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict s) := fun n => (hint n).1
  have hfin : ∑' n, ∫⁻ x in s, ‖f n x‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun n => (hmeas n).enorm]
    have : ∫⁻ x in s, ∑' n, ‖f n x‖ₑ = ∫⁻ x in s, ‖∑' n, f n x‖ₑ := by
      refine setLIntegral_congr_fun hs fun x hx => ?_
      rw [Real.enorm_eq_ofReal (tsum_nonneg fun n => hnn n x hx),
        ENNReal.ofReal_tsum_of_nonneg (fun n => hnn n x hx) (hps x hx)]
      exact tsum_congr fun n => Real.enorm_eq_ofReal (hnn n x hx)
    rw [this]
    exact hI.2.ne
  have hval : ∀ n, ∫ x in s, f n x = (∫⁻ x in s, ‖f n x‖ₑ).toReal := by
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae _ (hmeas n)]
    · congr 1
      refine setLIntegral_congr_fun hs fun x hx => ?_
      rw [Real.enorm_eq_ofReal (hnn n x hx)]
    · filter_upwards [ae_restrict_mem hs] with x hx using hnn n x hx
  have hsum : Summable fun n => ∫ x in s, f n x := by
    simp_rw [hval]; exact ENNReal.summable_toReal hfin
  rw [integral_tsum (fun n => hmeas n) hfin]
  exact hsum.hasSum

/-! ## The pole integral -/

lemma geom_pt {a u : ℝ} (_ha : 0 < a) (hu : 0 < u) :
    HasSum (fun n : ℕ => u ^ 4 * exp (-((a + (n + 1)) * u)))
      (u ^ 4 * exp (-(a * u)) / (exp u - 1)) := by
  have h0 : 0 ≤ exp (-u) := (exp_pos _).le
  have h1 : exp (-u) < 1 := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith); simpa using this
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left (u ^ 4 * exp (-(a * u)) * exp (-u))
  convert hg using 1
  · ext n
    rw [← Real.exp_nat_mul, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  · have he : exp u - 1 ≠ 0 := by
      have : 1 < exp u := Real.one_lt_exp_iff.mpr hu
      linarith
    have hne : 1 - exp (-u) ≠ 0 := by linarith
    simp only [Real.exp_neg] at hne ⊢
    have : exp u ≠ 0 := (exp_pos _).ne'
    field_simp

lemma u_integral {a : ℝ} (ha : 0 < a) {Z : ℝ} (hZ : HasSum (fun n : ℕ => 1 / (a + (n + 1)) ^ 5) Z) :
    IntegrableOn (fun u => u ^ 4 * exp (-(a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u)))
        (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u ^ 4 * exp (-(a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u)) =
        6 / a ^ 5 - 3 / a ^ 4 + 12 * Z := by
  have hc : ∀ n : ℕ, 0 < a + (n + 1) := fun n => by positivity
  have hint : ∀ n : ℕ, IntegrableOn (fun u => u ^ 4 * exp (-((a + (n + 1)) * u))) (Ioi 0) :=
    fun n => gam_integrable 4 (hc n)
  have hval : ∀ n : ℕ, ∫ u in Ioi (0 : ℝ), u ^ 4 * exp (-((a + (n + 1)) * u)) =
      24 * (1 / (a + (n + 1)) ^ 5) := by
    intro n; rw [gam 4 (hc n)]; simp [Nat.factorial]; ring
  have hsum : HasSum (fun n : ℕ => ∫ u in Ioi (0 : ℝ), u ^ 4 * exp (-((a + (n + 1)) * u)))
      (24 * Z) := by
    simp_rw [hval]; exact hZ.mul_left 24
  obtain ⟨hmI, hmV⟩ := integral_tsum_nn measurableSet_Ioi hint
    (fun n u hu => by have : (0 : ℝ) < u := hu; positivity)
    (fun u hu => (geom_pt ha hu).summable) hsum
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ∑' n : ℕ, u ^ 4 * exp (-((a + (n + 1)) * u)) =
      u ^ 4 * exp (-(a * u)) / (exp u - 1) := fun u hu => (geom_pt ha hu).tsum_eq
  have hm : IntegrableOn (fun u => u ^ 4 * exp (-(a * u)) / (exp u - 1)) (Ioi 0) :=
    hmI.congr_fun hpt measurableSet_Ioi
  have hmV' : ∫ u in Ioi (0 : ℝ), u ^ 4 * exp (-(a * u)) / (exp u - 1) = 24 * Z := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hpt, hmV]
  have i1 : IntegrableOn (fun u : ℝ => 1 / 4 * (u ^ 4 * exp (-(a * u))) +
      1 / 2 * (u ^ 4 * exp (-(a * u)) / (exp u - 1))) (Ioi 0) :=
    ((gam_integrable 4 ha).const_mul _).add (hm.const_mul _)
  have i2 : IntegrableOn (fun u : ℝ => 1 / 2 * (u ^ 3 * exp (-(a * u)))) (Ioi 0) :=
    (gam_integrable 3 ha).const_mul _
  have heq : EqOn (fun u : ℝ => (1 / 4 * (u ^ 4 * exp (-(a * u))) +
      1 / 2 * (u ^ 4 * exp (-(a * u)) / (exp u - 1))) - 1 / 2 * (u ^ 3 * exp (-(a * u))))
      (fun u => u ^ 4 * exp (-(a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u))) (Ioi 0) := by
    intro u hu
    have hu : (0 : ℝ) < u := hu
    have he : exp u - 1 ≠ 0 := by
      have : 1 < exp u := Real.one_lt_exp_iff.mpr hu
      linarith
    field_simp
  refine ⟨(i1.sub i2).congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_sub i1 i2,
    integral_add ((gam_integrable 4 ha).const_mul _) (hm.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, gam 4 ha, gam 3 ha, hmV']
  simp [Nat.factorial]
  field_simp
  ring

lemma pole {a : ℝ} (ha : 0 < a) {Z : ℝ} (hZ : HasSum (fun n : ℕ => 1 / (a + (n + 1)) ^ 5) Z) :
    IntegrableOn (fun y => weight y / (y ^ 2 + a ^ 2)) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), weight y / (y ^ 2 + a ^ 2) = 1 / (2 * a) - 1 / 4 + a ^ 4 * Z := by
  have hc : ∀ l : ℕ, 0 < 2 * π * ((l : ℝ) + 1) := fun l => by positivity
  -- u-side: `∑_l Φ(c_l, a) = ∫ u⁴ e^{-au} S(u) du`
  obtain ⟨hUI, hUV⟩ := u_integral ha hZ
  have hptU : ∀ u ∈ Ioi (0 : ℝ), HasSum (fun l : ℕ => u ^ 5 * exp (-(a * u)) /
      (u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2))
      (u ^ 4 * exp (-(a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u))) := by
    intro u hu
    have hu : (0 : ℝ) < u := hu
    convert (S_series hu).mul_left (u ^ 4 * exp (-(a * u))) using 1
    ext l
    have : u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2 ≠ 0 := by positivity
    field_simp
  have hPhiSum : HasSum (fun l : ℕ => Phi (2 * π * ((l : ℝ) + 1)) a)
      (6 / a ^ 5 - 3 / a ^ 4 + 12 * Z) := by
    rw [← hUV]
    have := hasSum_integral_nn measurableSet_Ioi (fun l => phi_integrable (hc l) ha)
      (fun l u hu => by have : (0 : ℝ) < u := hu; positivity)
      (fun u hu => (hptU u hu).summable)
      (hUI.congr_fun (fun u hu => (hptU u hu).tsum_eq.symm) measurableSet_Ioi)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => (hptU u hu).tsum_eq)] at this
    exact this
  -- y-side
  set g : ℕ → ℝ → ℝ := fun l y => (2 * π) ^ 4 / 12 * ((l + 1 : ℕ) : ℝ) ^ 4 *
    (y ^ 5 * exp (-((2 * π * (l + 1)) * y)) / (y ^ 2 + a ^ 2)) with hg
  have hint : ∀ l, IntegrableOn (g l) (Ioi 0) := fun l => (phi_integrable ha (hc l)).const_mul _
  have hval : ∀ l : ℕ, ∫ y in Ioi (0 : ℝ), g l y = a ^ 4 / 12 * Phi (2 * π * ((l : ℝ) + 1)) a := by
    intro l
    simp only [hg]
    rw [integral_const_mul]
    have h := phi_symm ha (hc l)
    unfold Phi at h ⊢
    have e : ∀ I : ℝ, (2 * π) ^ 4 / 12 * ((l + 1 : ℕ) : ℝ) ^ 4 * I =
        1 / 12 * ((2 * π * ((l : ℝ) + 1)) ^ 4 * I) := fun I => by push_cast; ring
    rw [e, h]; ring
  have hsum : HasSum (fun l => ∫ y in Ioi (0 : ℝ), g l y)
      (a ^ 4 / 12 * (6 / a ^ 5 - 3 / a ^ 4 + 12 * Z)) := by
    simp_rw [hval]; exact hPhiSum.mul_left _
  have hps : ∀ y ∈ Ioi (0 : ℝ), Summable fun l => g l y := by
    intro y hy
    have hy : (0 : ℝ) < y := hy
    have := (wsum_summable hy).mul_left ((2 * π) ^ 4 / 12 * y ^ 5 / (y ^ 2 + a ^ 2))
    refine this.congr fun l => ?_
    simp only [hg]
    rw [show -(2 * π * (↑l + 1) * y) = -2 * π * (↑l + 1) * y by ring]
    ring
  have hpt : ∀ y ∈ Ioi (0 : ℝ), weight y / (y ^ 2 + a ^ 2) = ∑' l, g l y := by
    intro y _
    rw [weight_eq, div_eq_mul_inv, mul_comm, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun (l : ℕ) => ?_
    simp only [hg]
    rw [show -(2 * π * (↑l + 1) * y) = -2 * π * (↑l + 1) * y by ring]
    ring
  obtain ⟨hI, hV⟩ := integral_tsum_nn measurableSet_Ioi hint
    (fun l y hy => by simp only [hg]; have : (0 : ℝ) < y := hy; positivity) hps hsum
  refine ⟨hI.congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hV]
  field_simp
  ring

end P22

open P22 in
/-- The weight is positive on `(0, ∞)`. -/
theorem weight_pos' {y : ℝ} (hy : 0 < y) : 0 < weight y := by
  rw [weight_eq]
  refine mul_pos (by positivity) ?_
  exact (wsum_summable hy).tsum_pos (fun l => by positivity) 0 (by positivity)

namespace P22

/-- Moments: `∫₀^∞ y^{2e} w(y) dy = µ(tᵉ)`. -/
lemma moment (e : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * weight y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * weight y = (muMono e : ℝ) := by
  set g : ℕ → ℝ → ℝ := fun l y => (2 * π) ^ 4 / 12 * ((l + 1 : ℕ) : ℝ) ^ 4 *
    (y ^ (2 * e + 5) * exp (-((2 * π * (l + 1)) * y))) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), y ^ (2 * e) * weight y = ∑' l, g l y := by
    intro y _
    rw [weight_eq, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun (l : ℕ) => ?_
    simp only [hg]
    rw [show -(2 * π * (↑l + 1) * y) = -2 * π * (↑l + 1) * y by ring]
    ring
  have hc : ∀ l : ℕ, 0 < 2 * π * ((l : ℝ) + 1) := fun l => by positivity
  have hint : ∀ l, IntegrableOn (g l) (Ioi 0) := fun l =>
    (gam_integrable (2 * e + 5) (hc l)).const_mul _
  have hval : ∀ l : ℕ, ∫ y in Ioi (0 : ℝ), g l y =
      ((2 * π) ^ 4 / 12 * (2 * e + 5)! / (2 * π) ^ (2 * e + 6)) *
        (1 / ((l + 1 : ℕ) : ℝ) ^ (2 * (e + 1))) := by
    intro l
    rw [hg]; simp only
    rw [integral_const_mul, gam _ (hc l)]
    simp only [mul_pow]
    have : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring
  have hz := hasSum_zeta_nat (k := e + 1) (by omega)
  have hz' : HasSum (fun l : ℕ => 1 / ((l + 1 : ℕ) : ℝ) ^ (2 * (e + 1)))
      ((-1 : ℝ) ^ (e + 1 + 1) * (2 : ℝ) ^ (2 * (e + 1) - 1) * π ^ (2 * (e + 1)) *
        _root_.bernoulli (2 * (e + 1)) / (2 * (e + 1))!) := by
    rw [← hasSum_nat_add_iff' 1] at hz
    simpa using hz
  have hsum := (hz'.mul_left ((2 * π) ^ 4 / 12 * (2 * e + 5)! / (2 * π) ^ (2 * e + 6)))
  rw [← funext hval] at hsum
  have hps : ∀ y ∈ Ioi (0 : ℝ), Summable fun l => g l y := by
    intro y hy
    have := (wsum_summable hy).mul_left ((2 * π) ^ 4 / 12 * y ^ (2 * e + 5))
    refine this.congr fun l => ?_
    rw [hg]; simp only
    rw [show -(2 * π * (↑l + 1) * y) = -2 * π * (↑l + 1) * y by ring]
    ring
  obtain ⟨hI, hV⟩ := integral_tsum_nn measurableSet_Ioi hint
    (fun l y hy => by rw [hg]; have : (0:ℝ) < y := hy; positivity) hps hsum
  refine ⟨hI.congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hV, muMono]
  have e1 : (2 * (e + 1) - 1) = 2 * e + 1 := by omega
  have e2 : 2 * (e + 1) = 2 * e + 2 := by ring
  rw [e1, e2]
  have f1 : ((2 * e + 5)! : ℝ) = (2 * e + 2)! * ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)) := by
    rw [show 2 * e + 5 = (2 * e + 2) + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast; ring
  rw [f1]
  have : ((2 * e + 2)! : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ## `ζ(5)` tails and the pole values -/

lemma zeta5_hasSum : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 5) ζ5 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) := summable_one_div_nat_pow.mpr (by norm_num)
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  have h2 : riemannZeta 5 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 5 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast at h ⊢; exact h
  have : ζ5 = ∑' n : ℕ, 1 / (n : ℝ) ^ 5 := by
    unfold ζ5; rw [h2, Complex.ofReal_re]
  rw [this]; exact hs.hasSum

lemma H5_eq_sum (j : ℕ) : ((H5 j : ℚ) : ℝ) = ∑ i ∈ range (j + 1), 1 / (i : ℝ) ^ 5 := by
  induction j with
  | zero => simp [H5]
  | succ m ih =>
    rw [H5_succ, Finset.sum_range_succ, ← ih]
    push_cast; ring

lemma zeta_tail (j : ℕ) :
    HasSum (fun n : ℕ => 1 / ((j : ℝ) + (n + 1)) ^ 5) (ζ5 - (H5 j : ℝ)) := by
  have h := (hasSum_nat_add_iff' (j + 1)).mpr zeta5_hasSum
  rw [← H5_eq_sum] at h
  convert h using 2 with n
  push_cast; ring_nf

lemma pole_val {j : ℕ} (hj : j ≠ 0) :
    IntegrableOn (fun y => weight y / (y ^ 2 + (j : ℝ) ^ 2)) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), weight y / (y ^ 2 + (j : ℝ) ^ 2) = aeval ζ5 (muPole j) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
  obtain ⟨hI, hV⟩ := pole hj' (zeta_tail j)
  refine ⟨hI, ?_⟩
  rw [hV, muPole]
  simp only [map_add, map_sub, map_mul, aeval_C, aeval_X, eq_ratCast]
  push_cast
  ring

/-- Polynomial part: `∫₀^∞ A(y²) w(y) dy = µ(A)`. -/
lemma poly_moment (A : ℚ[X]) :
    IntegrableOn (fun y => aeval (y ^ 2) A * weight y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), aeval (y ^ 2) A * weight y = (muPoly A : ℝ) := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · simp only [map_add, add_mul]; exact hp.1.add hq.1
    · simp only [map_add, add_mul]
      rw [integral_add hp.1 hq.1, hp.2, hq.2, muPoly_add]; push_cast; ring
  | monomial n c =>
    have hpt : ∀ y : ℝ, aeval (y ^ 2) (monomial n c) * weight y =
        (c : ℝ) * (y ^ (2 * n) * weight y) := by
      intro y; simp [aeval_monomial, eq_ratCast, pow_mul]; ring
    simp_rw [hpt]
    obtain ⟨hI, hV⟩ := moment n
    refine ⟨hI.const_mul _, ?_⟩
    rw [integral_const_mul, hV, muPoly_monomial]; push_cast; ring

end P22

end Zeta5

namespace Zeta5

open P22

lemma aeval_sqPoleProd_pos {S : Finset ℕ} (hS : 0 ∉ S) (t : ℝ) (ht : 0 ≤ t) :
    0 < aeval t (sqPoleProd S) := by
  rw [sqPoleProd, map_prod]
  refine Finset.prod_pos fun j hj => ?_
  have : j ≠ 0 := fun h => hS (h ▸ hj)
  have : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero this
  simp only [map_add, aeval_X, aeval_C, eq_ratCast]; push_cast; positivity

/-- Partial fractions for `P(t)/∏_{j∈S}(t + j²)` at real `t ≥ 0`. -/
lemma partial_fractions {S : Finset ℕ} (hS : 0 ∉ S) (P : ℚ[X]) (t : ℝ) (ht : 0 ≤ t) :
    aeval t P / aeval t (sqPoleProd S) =
      aeval t (P /ₘ sqPoleProd S) + ∑ j ∈ S, (sqResidue S P j : ℝ) / (t + (j : ℝ) ^ 2) := by
  have hQ := aeval_sqPoleProd_pos hS t ht
  have hP : aeval t P = aeval t (sqPoleProd S) * aeval t (P /ₘ sqPoleProd S) +
      ∑ j ∈ S, (sqResidue S P j : ℝ) * aeval t (sqPoleProd (S.erase j)) := by
    conv_lhs => rw [← modByMonic_add_div P (sqPoleProd S), modByMonic_sqPoleProd]
    simp only [map_add, map_mul, map_sum, aeval_C, eq_ratCast]
    ring
  rw [hP, add_div, mul_div_cancel_left₀ _ hQ.ne', Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hE : aeval t (sqPoleProd S) = (t + (j : ℝ) ^ 2) * aeval t (sqPoleProd (S.erase j)) := by
    rw [sqPoleProd, ← Finset.mul_prod_erase S _ hj, map_mul, ← sqPoleProd]
    simp only [map_add, aeval_X, aeval_C, eq_ratCast]; push_cast; ring
  have hE0 : aeval t (sqPoleProd (S.erase j)) ≠ 0 :=
    (aeval_sqPoleProd_pos (fun h => hS (Finset.mem_of_mem_erase h)) t ht).ne'
  have hj0 : t + (j : ℝ) ^ 2 ≠ 0 := by
    intro h; rw [h, zero_mul] at hE; exact hQ.ne' hE
  rw [hE]
  field_simp

lemma rat_decomp {S : Finset ℕ} (hS : 0 ∉ S) (P : ℚ[X]) (y : ℝ) :
    aeval (y ^ 2) P / aeval (y ^ 2) (sqPoleProd S) * weight y =
      aeval (y ^ 2) (P /ₘ sqPoleProd S) * weight y +
        ∑ j ∈ S, (sqResidue S P j : ℝ) * (weight y / (y ^ 2 + (j : ℝ) ^ 2)) := by
  rw [partial_fractions hS P _ (sq_nonneg y), add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma rat_integrable {S : Finset ℕ} (hS : 0 ∉ S) (P : ℚ[X]) :
    IntegrableOn (fun y => aeval (y ^ 2) P / aeval (y ^ 2) (sqPoleProd S) * weight y)
      (Set.Ioi 0) := by
  have hj : ∀ j ∈ S, j ≠ 0 := fun j hj h => hS (h ▸ hj)
  refine ((poly_moment _).1.add (integrable_finsetSum S fun j hjS =>
    (pole_val (hj j hjS)).1.const_mul (sqResidue S P j : ℝ))).congr_fun
    (fun y _ => (rat_decomp hS P y).symm) measurableSet_Ioi

/-- Proposition 2.2, (2.10): `µ_{ζ(5)}(R) = ∫₀^∞ R(y²) w(y) dy`. -/
theorem prop_2_2' (S : Finset ℕ) (hS : 0 ∉ S) (P : ℚ[X]) :
    aeval ζ5 (muX S P) =
      ∫ y in Set.Ioi (0 : ℝ), aeval (y ^ 2) P / aeval (y ^ 2) (sqPoleProd S) * weight y := by
  simp_rw [rat_decomp hS P]
  have hj : ∀ j ∈ S, j ≠ 0 := fun j hj h => hS (h ▸ hj)
  have hint : ∀ j ∈ S, Integrable (fun y => (sqResidue S P j : ℝ) *
      (weight y / (y ^ 2 + (j : ℝ) ^ 2))) (volume.restrict (Set.Ioi 0)) :=
    fun j hjS => (pole_val (hj j hjS)).1.const_mul _
  rw [integral_add (poly_moment _).1 (integrable_finsetSum _ hint), (poly_moment _).2,
    integral_finsetSum _ hint]
  unfold muX
  simp only [map_add, map_sum, map_mul, aeval_C, eq_ratCast]
  congr 1
  refine Finset.sum_congr rfl fun j hjS => ?_
  rw [integral_const_mul, (pole_val (hj j hjS)).2]


open Matrix in
/-- Proposition 2.2: `G_K(ζ(5))` is positive definite. -/
theorem G_zeta5_posDef' (K : ℕ) : ((G K).map fun q => aeval ζ5 q).PosDef := by
  set M := (G K).map fun q => aeval ζ5 q with hMdef
  have hS : 0 ∉ Finset.Icc 1 K := by simp
  set f : ℕ → ℝ → ℝ := fun n y => aeval (y ^ 2) (D (Nof K) ^ 6 * X ^ n) /
    aeval (y ^ 2) (sqPoleProd (Finset.Icc 1 K)) * weight y with hf
  have hM : ∀ i j : Fin (hof K), M i j = ∫ y in Set.Ioi (0 : ℝ), f ((i : ℕ) + j) y := by
    intro i j
    simp only [hMdef, Matrix.map_apply, G, Matrix.of_apply, hf]
    exact prop_2_2' _ hS _
  have hfn : ∀ n y, f n y = (y ^ 2) ^ n * f 0 y := by
    intro n y; simp only [hf, map_mul, map_pow, aeval_X, pow_zero, mul_one]; ring
  have hf0 : ∀ y : ℝ, 0 < y → 0 < f 0 y := by
    intro y hy
    simp only [hf, pow_zero, mul_one]
    have h1 : 0 < aeval (y ^ 2) (D (Nof K)) := aeval_sqPoleProd_pos (S := Finset.Icc 1 (Nof K)) (by simp)
      _ (sq_nonneg y)
    have h2 := aeval_sqPoleProd_pos hS _ (sq_nonneg y)
    have h3 := weight_pos' hy
    rw [map_pow]
    positivity
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, hM, add_comm]
  · intro x hx
    have hint : ∀ n, IntegrableOn (f n) (Set.Ioi 0) := fun n => rat_integrable hS _
    set q : ℝ → ℝ := fun y => ∑ i : Fin (hof K), x i * y ^ (2 * (i : ℕ)) with hq
    have hpt : ∀ y, ∑ i : Fin (hof K), ∑ j : Fin (hof K), x i * x j * f ((i : ℕ) + j) y =
        q y ^ 2 * f 0 y := by
      intro y
      simp only [hq]
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfn]; ring
    have hquad : star x ⬝ᵥ (M *ᵥ x) = ∫ y in Set.Ioi (0 : ℝ), q y ^ 2 * f 0 y := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, hM]
      simp_rw [← hpt]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint _).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hint _).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]; ring
    rw [hquad]
    have hFi : IntegrableOn (fun y => q y ^ 2 * f 0 y) (Set.Ioi 0) :=
      IntegrableOn.congr_fun (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hint _).const_mul (x i * x j)) (fun y _ => hpt y) measurableSet_Ioi
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hFi]
    · -- the zero set of `q` is finite
      set p : ℝ[X] := ∑ i : Fin (hof K), Polynomial.C (x i) * X ^ (2 * (i : ℕ)) with hp
      have hpeval : ∀ y, p.eval y = q y := by
        intro y; simp [hp, hq, eval_finsetSum]
      obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
        by_contra h; push Not at h; exact hx (funext h)
      have hp0 : p ≠ 0 := by
        intro h0
        have hc := congrArg (fun r => Polynomial.coeff r (2 * (i₀ : ℕ))) h0
        simp only [hp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
        rw [Finset.sum_eq_single i₀] at hc
        · simp at hc; exact hi₀ hc
        · intro b _ hb
          have : 2 * (i₀ : ℕ) ≠ 2 * (b : ℕ) := by
            intro h; apply hb; ext; omega
          simp [this]
        · simp
      have hZ : ({y | q y = 0} : Set ℝ).Finite := by
        refine (p.roots.toFinset.finite_toSet).subset fun y hy => ?_
        simp only [Set.mem_ofPred_eq] at hy
        simp [Multiset.mem_toFinset, mem_roots hp0, IsRoot, hpeval, hy]
      have hsub : Set.Ioi (0 : ℝ) \ {y | q y = 0} ⊆ Function.support (fun y => q y ^ 2 * f 0 y) ∩
          Set.Ioi 0 := by
        rintro y ⟨hy, hqy⟩
        refine ⟨?_, hy⟩
        simp only [Function.mem_support]
        have : q y ≠ 0 := hqy
        exact (mul_pos (by positivity) (hf0 y hy)).ne'
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [measure_sdiff_null (hZ.measure_zero _), Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (sq_nonneg _) (hf0 y hy).le

/-- Consequence of Proposition 2.2: `Δ_K(ζ(5)) > 0`. -/
theorem Delta_zeta5_pos' (K : ℕ) : 0 < aeval ζ5 (Delta K) := by
  have h := (G_zeta5_posDef' K).det_pos
  unfold Delta
  rw [show ((G K).map fun q => aeval ζ5 q) = (aeval ζ5).toRingHom.mapMatrix (G K) from rfl,
    ← RingHom.map_det] at h
  exact h


/-- The weight is positive on `(0, ∞)`. -/
theorem weight_pos {y : ℝ} (hy : 0 < y) : 0 < weight y := by
  exact weight_pos' hy

/-- Proposition 2.2, (2.10): `µ_{ζ(5)}(R) = ∫₀^∞ R(y²) w(y) dy` for every `R` in the domain of `µ_X`. -/
theorem prop_2_2 (S : Finset ℕ) (hS : 0 ∉ S) (P : ℚ[X]) :
    aeval ζ5 (muX S P) =
      ∫ y in Set.Ioi (0 : ℝ), aeval (y ^ 2) P / aeval (y ^ 2) (sqPoleProd S) * weight y := by
  exact prop_2_2' S hS P

/-- Proposition 2.2: `G_K(ζ(5))` is positive definite. -/
theorem G_zeta5_posDef (K : ℕ) : ((G K).map fun q => aeval ζ5 q).PosDef := by
  exact G_zeta5_posDef' K

/-- Consequence of Proposition 2.2: `Δ_K(ζ(5)) > 0`. -/
theorem Delta_zeta5_pos (K : ℕ) : 0 < aeval ζ5 (Delta K) := by
  exact Delta_zeta5_pos' K

end Zeta5
