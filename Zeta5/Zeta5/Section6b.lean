import Zeta5.Section6
import Zeta5.Energy6
import Zeta5.Prop22

/-!
# §6 (continued): proofs of (6.15) and (6.10)

`log_S_6_15'` proves (6.15) from elementary factorial bounds. `andreief_6_10'` proves (6.10)
assuming Proposition 2.2 (still `sorry` in `Section2.lean`), which is taken as a hypothesis.
-/

open Polynomial Finset MeasureTheory Filter Topology Equiv

noncomputable section

namespace Zeta5

/-- `log m! ≤ m log m - m + log m + 2` for `m ≥ 1`. -/
theorem log_factorial_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ) ≤ m * Real.log m - m + Real.log m + 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : Real.log ((m : ℝ) / (m + 1)) ≤ (m : ℝ) / (m + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hm0.ne' (by positivity)] at h1
    have h2 : (m : ℝ) / (m + 1) - 1 = -1 / (m + 1) := by field_simp; ring
    rw [h2] at h1
    have h3 : ((m : ℝ) + 1) * (Real.log m - Real.log (m + 1)) ≤ -1 := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ m + 1)
      rwa [mul_div_cancel₀ _ (by positivity : (m : ℝ) + 1 ≠ 0)] at this
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

/-- `log m! ≥ m log m - m + 1` for `m ≥ 1`. -/
theorem le_log_factorial (m : ℕ) (hm : 1 ≤ m) :
    m * Real.log m - m + 1 ≤ Real.log (m.factorial : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : Real.log (((m : ℝ) + 1) / m) ≤ ((m : ℝ) + 1) / m - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hm0.ne'] at h1
    have h2 : ((m : ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
    rw [h2] at h1
    have h3 : (m : ℝ) * (Real.log (m + 1) - Real.log m) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hm0.le
      rwa [mul_div_cancel₀ _ hm0.ne'] at this
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

/-- `∑_{1 ≤ i ≤ h-1} log (2i)! ≥ h² log(2h) - 3h²/2 - 2h log(2h)` for `h ≥ 1`. -/
theorem sum_log_factorial_ge (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ) ^ 2 * Real.log (2 * h) - 3 / 2 * (h : ℝ) ^ 2 - 2 * h * Real.log (2 * h) ≤
      ∑ i ∈ Icc 1 (h - 1), Real.log ((2 * i).factorial : ℝ) := by
  induction h, hh using Nat.le_induction with
  | base =>
    have : Real.log 2 ≥ 0 := Real.log_nonneg (by norm_num)
    norm_num; linarith
  | succ h hh ih =>
    have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
    rw [show h + 1 - 1 = (h - 1) + 1 by omega, Finset.sum_Icc_succ_top (by omega),
      show h - 1 + 1 = h by omega]
    have hf := le_log_factorial (2 * h) (by omega)
    push_cast at hf ⊢
    have h1 : Real.log ((2 * (h : ℝ) + 2) / (2 * h)) ≤ (2 * (h : ℝ) + 2) / (2 * h) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have h2 : (2 * (h : ℝ) + 2) / (2 * h) - 1 = 1 / h := by field_simp; ring
    rw [h2] at h1
    have h3 : (h : ℝ) * (Real.log (2 * h + 2) - Real.log (2 * h)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hh0.le
      rwa [mul_div_cancel₀ _ hh0.ne'] at this
    have h4 : 0 ≤ Real.log (2 * h + 2) - Real.log (2 * h) := by
      rw [sub_nonneg]; exact Real.log_le_log (by positivity) (by linarith)
    have h1' : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have h5 : 0 ≤ Real.log (2 * (h : ℝ)) := Real.log_nonneg (by linarith)
    have e : (2 * ((h : ℝ) + 1)) = 2 * h + 2 := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h3 hh0.le, mul_nonneg hh0.le h4]

/-- (6.15): `log S_K ≤ (2λ - 12αλ - 2λ²)K² log K + C*K² + 6h log K + 6h`. -/
theorem log_S_6_15' (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) :
    Real.log (S K) ≤
      (2 * Lim.lam - 12 * Lim.α * Lim.lam - 2 * Lim.lam ^ 2) * (K : ℝ) ^ 2 * Real.log K +
        Cstar * (K : ℝ) ^ 2 + 6 * hof K * Real.log K + 6 * hof K := by
  obtain ⟨n, rfl⟩ := hK
  have hn : 1 ≤ n := by omega
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  have hS : ((S (40 * n) : ℚ) : ℝ) =
      (((40 * n).factorial : ℝ) ^ (2 * (37 * n)) * 4 ^ (37 * n - 1)) /
        (((3 * n).factorial : ℝ) ^ (12 * (37 * n)) *
          ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℝ) ^ 2) := by
    unfold S; rw [hh, hN]; push_cast; rfl
  rw [hS, hh]
  have hp : ∀ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℝ) ^ 2 ≠ 0 := fun i _ => by positivity
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr hp), Real.log_prod hp]
  simp only [Real.log_pow]
  rw [← Finset.mul_sum]
  have hA := log_factorial_le (40 * n) (by omega)
  have hB := le_log_factorial (3 * n) (by omega)
  have hC := sum_log_factorial_ge (37 * n) (by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((37 * n - 1 : ℕ) : ℝ) = 37 * n - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hsub]
  push_cast at hA hB hC ⊢
  -- logarithms of `N = αK` and `2h = 2λK`
  have hK' : (0 : ℝ) < 40 * n := by positivity
  have eN : Real.log (3 * n) = Real.log Lim.α + Real.log (40 * n) := by
    rw [← Real.log_mul (by norm_num [Lim.α]) hK'.ne']; unfold Lim.α; ring_nf
  have eh : Real.log (2 * (37 * n)) = Real.log (2 * Lim.lam) + Real.log (40 * n) := by
    rw [← Real.log_mul (by norm_num [Lim.lam]) hK'.ne']; unfold Lim.lam; ring_nf
  rw [eN] at hB
  rw [eh] at hC
  have l4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have l4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have lb : Real.log (2 * Lim.lam) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num [Lim.lam] : (0 : ℝ) < 2 * Lim.lam)
    unfold Lim.lam at this ⊢; linarith
  unfold Cstar
  have hn0 : (0 : ℝ) ≤ n := by linarith
  set L := Real.log (40 * (n : ℝ))
  set a := Real.log Lim.α
  set b := Real.log (2 * Lim.lam)
  unfold Lim.α Lim.lam at *
  linarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * (37 * n)),
    mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 12 * (37 * n)),
    mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ 14 - Real.log 4 - 4 * b)]

/-! ## (6.10): Andréief's identity -/

theorem comp_perm_mp {n : ℕ} (μ : Measure ℝ) [SigmaFinite μ] (ρ : Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => x (ρ i)) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => μ) := by
  have := measurePreserving_arrowCongr' (fun _ : Fin n => μ) (fun _ => μ) ρ.symm
    (MeasurableEquiv.refl ℝ) (fun _ => MeasurePreserving.id μ)
  convert this using 1
  ext x i
  simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']

theorem andreief {n : ℕ} (μ : Measure ℝ) [SigmaFinite μ] (φ ψ : Fin n → ℝ → ℝ)
    (hint : ∀ i j, Integrable (fun x => φ i x * ψ j x) μ) :
    (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det =
      1 / n.factorial * ∫ x : Fin n → ℝ,
        (Matrix.of fun a b => φ a (x b)).det * (Matrix.of fun a b => ψ a (x b)).det
          ∂(Measure.pi fun _ => μ) := by
  set P : (Fin n → ℝ) → ℝ := fun x => (Matrix.of fun a b => φ a (x b)).det with hPdef
  set I1 : (Fin n → ℝ) → ℝ := fun x => P x * ∏ i, ψ i (x i) with hI1
  have hI1' : I1 = fun x => ∑ σ : Perm (Fin n),
      (Perm.sign σ : ℝ) * ∏ i, (φ (σ i) (x i) * ψ i (x i)) := by
    funext x
    simp only [hI1, hPdef, Matrix.det_apply', Matrix.of_apply, Finset.sum_mul,
      Finset.prod_mul_distrib, mul_assoc]
  have hint1 : Integrable I1 (Measure.pi fun _ => μ) := by
    rw [hI1']
    exact integrable_finsetSum _ fun σ _ =>
      (Integrable.fintype_prod (f := fun i t => φ (σ i) t * ψ i t) fun i => hint _ _).const_mul _
  have step1 : (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det =
      ∫ x, I1 x ∂(Measure.pi fun _ => μ) := by
    rw [hI1', integral_finsetSum _ fun σ _ =>
      (Integrable.fintype_prod (f := fun i t => φ (σ i) t * ψ i t) fun i => hint _ _).const_mul _,
      Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [integral_fintype_prod_eq_prod (f := fun i t => φ (σ i) t * ψ i t)]
    rfl
  have hcomp : ∀ ρ : Perm (Fin n), ∀ x : Fin n → ℝ,
      I1 (fun i => x (ρ i)) = (Perm.sign ρ : ℝ) * (P x * ∏ i, ψ i (x (ρ i))) := by
    intro ρ x
    simp only [hI1, hPdef]
    have : (Matrix.of fun a b => φ a (x (ρ b))) =
        (Matrix.of fun a b => φ a (x b)).submatrix id ρ := by
      ext a b; rfl
    rw [this, Matrix.det_permute']
    ring
  have hmp := comp_perm_mp (n := n) μ
  calc (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det
      = 1 / n.factorial * ∑ _ρ : Perm (Fin n), ∫ x, I1 x ∂(Measure.pi fun _ => μ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, step1]
        field_simp
    _ = 1 / n.factorial * ∑ ρ : Perm (Fin n),
          ∫ x, I1 (fun i => x (ρ i)) ∂(Measure.pi fun _ => μ) := by
        congr 1
        refine Finset.sum_congr rfl fun ρ _ => ?_
        have h := (measurePreserving_arrowCongr' (fun _ : Fin n => μ) (fun _ => μ) ρ.symm
          (MeasurableEquiv.refl ℝ) (fun _ => MeasurePreserving.id μ)).integral_comp' I1
        rw [← h]
        rfl
    _ = _ := by
        congr 1
        have hi : ∀ ρ : Perm (Fin n), Integrable (fun x : Fin n → ℝ => I1 (fun i => x (ρ i)))
            (Measure.pi fun _ => μ) := fun ρ => (hmp ρ).integrable_comp_of_integrable hint1
        rw [← integral_finsetSum _ fun ρ _ => hi ρ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hcomp]
        show _ = P x * _
        rw [← Matrix.det_transpose (Matrix.of fun a b => ψ a (x b)),
          Matrix.det_apply' (Matrix.of fun a b => ψ a (x b)).transpose, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [Matrix.transpose_apply, Matrix.of_apply]
        ring


theorem weight_summable {y : ℝ} (hy : 0 < y) :
    Summable fun l : ℕ => ((l + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-2 * Real.pi * (l + 1) * y) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul 4 (by positivity : 0 < 2 * Real.pi * y))
  refine h.congr fun l => ?_
  push_cast; ring_nf

theorem weight_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ weight y := by
  unfold weight
  exact mul_nonneg (by positivity) (tsum_nonneg fun l => by positivity)

theorem weight_aesm : AEStronglyMeasurable weight (volume.restrict (Set.Ioi 0)) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun M y => (2 * Real.pi) ^ 4 * y ^ 5 / 12 *
      ∑ l ∈ range M, ((l + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-2 * Real.pi * (l + 1) * y))
    (fun M => (by fun_prop : Continuous _).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun y (hy : 0 < y) => ?_
  exact ((weight_summable hy).hasSum.tendsto_sum_nat).const_mul _

theorem aeval_D (m : ℕ) (t : ℝ) : aeval t (D m) = ∏ j ∈ Icc 1 m, (t + (j : ℝ) ^ 2) := by
  simp [D, map_prod]

theorem integrable_weightf (N K m : ℕ) :
    Integrable (fun y : ℝ => (y ^ 2) ^ m *
      (aeval (y ^ 2) (D N) ^ 6 / aeval (y ^ 2) (D K) * weight y)) (volume.restrict (Set.Ioi 0)) := by
  set c : ℝ := ∏ j ∈ Icc 1 N, ((j : ℝ) ^ 2)
  set d : ℕ := 2 * m + 12 * N + 5
  have hg : IntegrableOn (fun y : ℝ => 8192 * c ^ 6 * 2 ^ d *
      (Real.exp (-(2 * Real.pi) * y) + y ^ (d : ℝ) * Real.exp (-(2 * Real.pi) * y ^ (1 : ℝ))))
      (Set.Ioi 0) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact exp_neg_integrableOn_Ioi 0 (by positivity)
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow
        (by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith) one_pos (by positivity)
  refine Integrable.mono' hg ?_ ?_
  · refine AEStronglyMeasurable.mul (by fun_prop) (AEStronglyMeasurable.mul ?_ weight_aesm)
    exact ((((D N).continuous_aeval.comp (continuous_pow 2 : Continuous fun y : ℝ => y ^ 2)).pow
      6).measurable.div ((D K).continuous_aeval.comp
        (continuous_pow 2 : Continuous fun y : ℝ => y ^ 2)).measurable).aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun y (hy : 0 < y) => ?_
  rw [aeval_D, aeval_D]
  have hDK : 1 ≤ ∏ j ∈ Icc 1 K, (y ^ 2 + (j : ℝ) ^ 2) := by
    rw [← prod_const_one (s := Icc 1 K)]
    refine prod_le_prod₀ (fun _ _ => zero_le_one) fun j hj => ?_
    have : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    nlinarith
  have hDN0 : 0 ≤ ∏ j ∈ Icc 1 N, (y ^ 2 + (j : ℝ) ^ 2) := prod_nonneg fun _ _ => by positivity
  have hDN : ∏ j ∈ Icc 1 N, (y ^ 2 + (j : ℝ) ^ 2) ≤ (1 + y) ^ (2 * N) * c := by
    have e : ((1 + y) ^ 2) ^ N = ∏ _j ∈ Icc 1 N, (1 + y) ^ 2 := by
      rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
    rw [pow_mul, e, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun j hj => ?_
    have : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    nlinarith [mul_nonneg hy.le (sq_nonneg (j : ℝ)), mul_le_mul_of_nonneg_left this (sq_nonneg y)]
  have hw := weight_le' y hy
  have hw0 := weight_nonneg hy
  have hq : 0 ≤ (∏ j ∈ Icc 1 N, (y ^ 2 + (j : ℝ) ^ 2)) ^ 6 /
      ∏ j ∈ Icc 1 K, (y ^ 2 + (j : ℝ) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- polynomial factor
  have hpoly : (1 + y) ^ d ≤ 2 ^ d * (1 + y ^ (d : ℝ)) := by
    rw [Real.rpow_natCast]
    rcases le_total y 1 with h1 | h1
    · calc (1 + y) ^ d ≤ 2 ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
        _ ≤ 2 ^ d * (1 + y ^ d) := le_mul_of_one_le_right (by positivity)
            (by linarith [pow_nonneg hy.le d])
    · calc (1 + y) ^ d ≤ (2 * y) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
        _ = 2 ^ d * y ^ d := mul_pow _ _ _
        _ ≤ 2 ^ d * (1 + y ^ d) := by gcongr; linarith
  have hy2 : (y ^ 2) ^ m ≤ (1 + y) ^ (2 * m) := by
    rw [← pow_mul]; exact pow_le_pow_left₀ hy.le (by linarith) _
  have hA : (∏ j ∈ Icc 1 N, (y ^ 2 + (j : ℝ) ^ 2)) ^ 6 / ∏ j ∈ Icc 1 K, (y ^ 2 + (j : ℝ) ^ 2) ≤
      ((1 + y) ^ (2 * N) * c) ^ 6 :=
    (div_le_self (by positivity) hDK).trans (pow_le_pow_left₀ hDN0 hDN 6)
  have he : 0 ≤ Real.exp (-2 * Real.pi * y) := (Real.exp_pos _).le
  calc (y ^ 2) ^ m * (((∏ j ∈ Icc 1 N, (y ^ 2 + (j : ℝ) ^ 2)) ^ 6 /
        ∏ j ∈ Icc 1 K, (y ^ 2 + (j : ℝ) ^ 2)) * weight y)
      ≤ (1 + y) ^ (2 * m) * (((1 + y) ^ (2 * N) * c) ^ 6 *
          (8192 * (1 + y) ^ 5 * Real.exp (-2 * Real.pi * y))) :=
        mul_le_mul hy2 (mul_le_mul hA hw hw0 (by positivity)) (by positivity) (by positivity)
    _ = 8192 * c ^ 6 * ((1 + y) ^ d * Real.exp (-2 * Real.pi * y)) := by
        simp only [d]; ring
    _ ≤ 8192 * c ^ 6 * (2 ^ d * (1 + y ^ (d : ℝ)) * Real.exp (-2 * Real.pi * y)) := by
        gcongr
    _ = 8192 * c ^ 6 * 2 ^ d * (Real.exp (-(2 * Real.pi) * y) +
          y ^ (d : ℝ) * Real.exp (-(2 * Real.pi) * y ^ (1 : ℝ))) := by
        rw [Real.rpow_one]; ring_nf


/-- (6.10), Andréief's identity, assuming Proposition 2.2 (`prop_2_2`, still `sorry` in
`Section2.lean`) as the hypothesis `hprop`. -/
theorem andreief_6_10'
    (hprop : ∀ (S : Finset ℕ), 0 ∉ S → ∀ P : ℚ[X], aeval ζ5 (muX S P) =
      ∫ y in Set.Ioi (0 : ℝ), aeval (y ^ 2) P / aeval (y ^ 2) (sqPoleProd S) * weight y)
    (K : ℕ) (hK : 40 ∣ K) :
    aeval ζ5 (Delta K) =
      1 / (hof K).factorial *
        ∫ y in {y : Fin (hof K) → ℝ | ∀ i, 0 < y i},
          (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) *
            ∏ i, (aeval ((y i) ^ 2) (D (Nof K)) ^ 6 / aeval ((y i) ^ 2) (D K) * weight (y i)) := by
  have hint : ∀ i j : Fin (hof K), Integrable (fun y : ℝ => (y ^ 2) ^ (i : ℕ) *
      ((y ^ 2) ^ (j : ℕ) * (aeval (y ^ 2) (D (Nof K)) ^ 6 / aeval (y ^ 2) (D K) * weight y)))
      (volume.restrict (Set.Ioi 0)) := by
    intro i j
    refine (integrable_weightf (Nof K) K ((i : ℕ) + j)).congr (Eventually.of_forall fun y => ?_)
    simp only [pow_add]; ring
  have hA := andreief (volume.restrict (Set.Ioi 0)) _ _ hint
  have hL : aeval ζ5 (Delta K) = (Matrix.of fun i j : Fin (hof K) => ∫ y, (y ^ 2) ^ (i : ℕ) *
      ((y ^ 2) ^ (j : ℕ) * (aeval (y ^ 2) (D (Nof K)) ^ 6 / aeval (y ^ 2) (D K) * weight y))
        ∂(volume.restrict (Set.Ioi 0))).det := by
    rw [Delta, AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, G, Matrix.of_apply]
    rw [hprop _ (by simp)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e : sqPoleProd (Icc 1 K) = D K := rfl
    simp only [e, map_mul, map_pow, aeval_X]
    ring
  rw [hL, hA]
  congr 1
  have hset : {y : Fin (hof K) → ℝ | ∀ i, 0 < y i} = Set.univ.pi fun _ => Set.Ioi 0 := by
    ext y; simp
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hV : (Matrix.of fun a b : Fin (hof K) => (y b ^ 2) ^ (a : ℕ)) =
      (Matrix.vandermonde fun b => y b ^ 2).transpose := by
    ext a b; rfl
  have hW : (Matrix.of fun a b : Fin (hof K) => (y b ^ 2) ^ (a : ℕ) *
      (aeval (y b ^ 2) (D (Nof K)) ^ 6 / aeval (y b ^ 2) (D K) * weight (y b))) =
      Matrix.of fun a b => (aeval (y b ^ 2) (D (Nof K)) ^ 6 / aeval (y b ^ 2) (D K) *
        weight (y b)) * (Matrix.vandermonde fun b => y b ^ 2).transpose a b := by
    ext a b; simp [Matrix.vandermonde_apply]; ring
  have key : ∏ i : Fin (hof K), ∏ j ∈ univ.filter (fun j => i < j), (y i ^ 2 - y j ^ 2) ^ 2 =
      (∏ i : Fin (hof K), ∏ j ∈ Ioi i, (y j ^ 2 - y i ^ 2)) ^ 2 := by
    rw [← prod_pow]
    refine prod_congr rfl fun i _ => ?_
    rw [← prod_pow, filter_lt_eq_Ioi]
    exact prod_congr rfl fun j _ => by ring
  simp only
  rw [hV, hW, Matrix.det_mul_row, Matrix.det_transpose, Matrix.det_vandermonde, key]
  ring


/-! ## The §6 statements under their original names -/

/-- (6.10), Andréief's identity:
`Δ_K(ζ(5)) = (1/h!) ∫_{(0,∞)^h} ∏_{i<j} (y_i² - y_j²)² ∏_i D_N(y_i²)⁶/D_K(y_i²) w(y_i) dy`. -/
theorem andreief_6_10 (K : ℕ) (hK : 40 ∣ K) :
    aeval ζ5 (Delta K) =
      1 / (hof K).factorial *
        ∫ y in {y : Fin (hof K) → ℝ | ∀ i, 0 < y i},
          (∏ i, ∏ j ∈ univ.filter (fun j => i < j), ((y i) ^ 2 - (y j) ^ 2) ^ 2) *
            ∏ i, (aeval ((y i) ^ 2) (D (Nof K)) ^ 6 / aeval ((y i) ^ 2) (D K) * weight (y i)) := by
  exact andreief_6_10' (fun S hS P => prop_2_2 S hS P) K hK


/-- (6.15): `log S_K ≤ (2λ - 12αλ - 2λ²)K² log K + C*K² + 6h log K + 6h`. -/
theorem log_S_6_15 (K : ℕ) (hK : 40 ∣ K) (hK0 : 0 < K) :
    Real.log (S K) ≤
      (2 * Lim.lam - 12 * Lim.α * Lim.lam - 2 * Lim.lam ^ 2) * (K : ℝ) ^ 2 * Real.log K +
        Cstar * (K : ℝ) ^ 2 + 6 * hof K * Real.log K + 6 * hof K := by
  exact log_S_6_15' K hK hK0


-- (6.14) and Proposition 6.3 are in `Section6c.lean`.

end Zeta5
