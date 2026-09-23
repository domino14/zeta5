import Zeta5.Prop51
import Zeta5.Prop52
import Zeta5.Degree29
import Zeta5.Section6c
import Zeta5.AppendixB

/-!
# §7 Completion: Theorem 2.1

Theorem 2.1 is assembled here from the section lemmas. Everything in this file is proved from
the stated (possibly `sorry`'d) results of §2–§6 and Appendix B, so this file checks the
logic of §7 itself.
-/

open Polynomial Finset Filter Topology

noncomputable section

namespace Zeta5

theorem aeval_Q (K M : ℕ) : aeval ζ5 (Q K M) = (mKM K M : ℝ) * aeval ζ5 (F K) := by
  simp [Q, F]

/-- Theorem 2.1, first part: `Q_{K,M} ∈ ℤ[X]`, `deg Q_{K,M} = h`, `Q_{K,M}(ζ(5)) > 0`. -/
theorem theorem_2_1 {K M : ℕ} (h : StdHyp K M) :
    (∃ P : ℤ[X], P.map (algebraMap ℤ ℚ) = Q K M) ∧ (Q K M).natDegree = hof K ∧
      0 < aeval ζ5 (Q K M) := by
  refine ⟨prop_5_1 h, ?_, ?_⟩
  · rw [Q, F, ← mul_assoc, ← C_mul, natDegree_C_mul (mul_ne_zero (mKM_pos K M).ne' (S_pos K).ne')]
    exact (Delta_natDegree_leadingCoeff K h.2.1).1
  · rw [aeval_Q, F]
    simp only [map_mul, aeval_C, eq_ratCast]
    have := Delta_zeta5_pos K
    have := mKM_pos K M
    have := S_pos K
    positivity

/-- `(24 K log K + 200 K) / K² → 0` along `K = 40n`. -/
theorem error_term_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (24 * ((40 * n : ℕ) : ℝ) * Real.log ((40 * n : ℕ) : ℝ) + 200 * ((40 * n : ℕ) : ℝ)) /
        ((40 * n : ℕ) : ℝ) ^ 2 ≤ ε := by
  have hK : Tendsto (fun n : ℕ => ((40 * n : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_id.const_mul_atTop' (by norm_num)
  have h1 : Tendsto (fun x : ℝ => (24 * Real.log x + 200) / x) atTop (𝓝 0) := by
    have hl := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at hl
    have hi : Tendsto (fun x : ℝ => 200 / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := (hl.const_mul 24).add hi
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
  filter_upwards [(h1.comp hK).eventually (ge_mem_nhds hε), hK.eventually (eventually_gt_atTop 0)]
    with n hn hpos
  simp only [Function.comp] at hn
  calc _ = (24 * Real.log ((40 * n : ℕ) : ℝ) + 200) / ((40 * n : ℕ) : ℝ) := by
          field_simp
    _ ≤ ε := hn

/-- (7.1): `limsup K⁻² log Q_{K,M}(ζ(5)) ≤ A_M + U` for `M ∈ 40ℤ`, `M ≥ 40`. -/
theorem limsup_7_1 (M : ℕ) (hM : 40 ≤ M) (hM40 : 40 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (aeval ζ5 (Q (40 * n) M)) / ((40 * n : ℕ) : ℝ) ^ 2 ≤ AM M + U + ε := by
  filter_upwards [limsup_5_21 M hM hM40 (ε / 2) (half_pos hε),
    error_term_small (ε / 2) (half_pos hε), eventually_gt_atTop 0] with n h1 h2 hn
  set K := 40 * n with hKdef
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  obtain ⟨hFpos, hFlog⟩ := prop_6_3 K (Dvd.intro n rfl) hK0
  have hm := mKM_pos K M
  have hmr : (0 : ℝ) < (mKM K M : ℝ) := by exact_mod_cast hm
  rw [aeval_Q, Real.log_mul hmr.ne' hFpos.ne', add_div]
  have hF' : Real.log (aeval ζ5 (F K)) / (K : ℝ) ^ 2 ≤
      U + (24 * (K : ℝ) * Real.log K + 200 * K) / (K : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  linarith

/-- (2.7): `0 < Q_{40n,200}(ζ(5)) < exp(-139n²/5)` for all large `n`. -/
theorem theorem_2_1_decay_200 :
    ∀ᶠ n : ℕ in atTop,
      0 < aeval ζ5 (Q (40 * n) 200) ∧
        aeval ζ5 (Q (40 * n) 200) < Real.exp (-(139 / 5 * (n : ℝ) ^ 2)) := by
  obtain ⟨hmarg, -⟩ := margin_200
  set δ : ℚ := 3089837638249482469 / 58872425992515135000 with hδ
  have hδpos : (0 : ℝ) < (δ : ℝ) / 3200 := by rw [hδ]; norm_num
  filter_upwards [limsup_7_1 200 (by norm_num) (by norm_num) _ hδpos,
    eventually_ge_atTop 200000] with n h1 hn
  have hstd : StdHyp (40 * n) 200 := ⟨by norm_num, Dvd.intro n rfl, by omega, by omega⟩
  have hpos := (theorem_2_1 hstd).2.2
  refine ⟨hpos, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hK2 : (((40 * n : ℕ) : ℝ)) ^ 2 = 1600 * (n : ℝ) ^ 2 := by push_cast; ring
  rw [hK2, div_le_iff₀ (by positivity)] at h1
  rw [← Real.log_lt_iff_lt_exp hpos]
  have hm : ((AM 200 + U : ℚ) : ℝ) = -(139 / 5 + (δ : ℝ)) / 1600 := by
    have : AM 200 + U = -(139 / 5 + δ) / 1600 := by linarith [hmarg]
    rw [this]; push_cast; ring
  have hm' : ((AM 200 : ℚ) : ℝ) + (U : ℝ) = -(139 / 5 + (δ : ℝ)) / 1600 := by
    rw [← hm]; push_cast; ring
  rw [hm'] at h1
  have hδr : (0 : ℝ) < δ := by rw [hδ]; norm_num
  nlinarith [sq_nonneg (n : ℝ), mul_pos hδr (pow_pos hn0 2)]

end Zeta5
