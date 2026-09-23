import Zeta5.Valuation

/-!
# Lemma 4.2
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-- The weight arithmetic behind Lemma 4.2: for nonpositive half-integer weights and any set `U`,
`∑_{i ∈ U} (w_i + 1/2) ≤ min(|U|, z)/2`, where `z` is the number of zero weights. -/
theorem weight_loss {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, w i ≤ 0)
    (hw2 : ∀ i, ∃ k : ℤ, 2 * w i = k) (U : Finset ι) :
    ∑ i ∈ U, (w i + 1 / 2) ≤
      (min U.card (Finset.univ.filter fun i => w i = 0).card : ℚ) / 2 := by
  classical
  have hterm : ∀ i, w i + 1 / 2 ≤ if w i = 0 then 1 / 2 else 0 := by
    intro i
    split_ifs with h0
    · simp [h0]
    · obtain ⟨k, hk⟩ := hw2 i
      have hneg : w i < 0 := lt_of_le_of_ne (hw i) h0
      have hk' : k < 0 := by
        have : (k : ℚ) < 0 := by rw [← hk]; linarith
        exact_mod_cast this
      have : (k : ℚ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk'
      linarith
  calc ∑ i ∈ U, (w i + 1 / 2) ≤ ∑ i ∈ U, (if w i = 0 then (1 / 2 : ℚ) else 0) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ((U.filter fun i => w i = 0).card : ℚ) / 2 := by
        rw [← Finset.sum_filter]; simp [div_eq_mul_inv]
    _ ≤ _ := by
        gcongr
        rw [le_min_iff]
        constructor
        · exact_mod_cast Finset.card_filter_le _ _
        · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ U))

/-- More than `rank L` rows of `L` are linearly dependent. -/
theorem rows_dependent {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℚ)
    (T : Finset ι) (hT : L.rank < T.card) :
    ∃ c : ι → ℚ, (∀ i ∉ T, c i = 0) ∧ (∃ i ∈ T, c i ≠ 0) ∧ ∑ i, c i • L.row i = 0 := by
  have hdep : ¬ LinearIndependent ℚ (fun i : T => L.row i) := by
    intro hli
    have h1 := finrank_span_eq_card hli
    have h2 : Submodule.span ℚ (Set.range fun i : T => L.row i) ≤
        Submodule.span ℚ (Set.range L.row) :=
      Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    have h3 := Submodule.finrank_mono h2
    rw [h1, ← Matrix.rank_eq_finrank_span_row] at h3
    simp at h3
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set c : ι → ℚ := fun j => if h : j ∈ T then g ⟨j, h⟩ else 0 with hc
  refine ⟨c, fun j hj => by simp [hc, hj], ⟨i, i.2, by simpa [hc] using hi⟩, ?_⟩
  calc ∑ j, c j • L.row j = ∑ j ∈ T, c j • L.row j :=
        (Finset.sum_subset (Finset.subset_univ T) fun j _ hj => by simp [hc, hj]).symm
    _ = ∑ j : T, c j • L.row j := (Finset.sum_coe_sort T _).symm
    _ = ∑ j : T, g j • L.row j := Finset.sum_congr rfl fun j _ => by simp [hc, j.2]
    _ = 0 := hg

/-- Lemma 4.2: if `v(A_ij) ≥ w_i + w_j` with nonpositive half-integer weights, `L` is integral
of rank at most `r`, and exactly `z` weights are zero, then
`v(det(A + p⁻¹L)) ≥ 2∑ w_i - min(r, z)`. Stated for the Gauss valuation, with `L` constant
(as it is in (4.10)). `Matrix.rank` is over `ℚ`, which equals the rank over `ℚ_p`.

The proof expands `det` multilinearly in the rows instead of by complementary minors: a term
taking the rows in `T` from `p⁻¹L` vanishes if `|T| > r`, and otherwise loses at most
`|T| + ∑_{T} w + ∑_{σ⁻¹T} w ≤ min(r, z)` by `weight_loss`. -/
theorem lemma_4_2 (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (L : Matrix ι ι ℚ) (w : ι → ℚ)
    (hw : ∀ i, w i ≤ 0) (hw2 : ∀ i, ∃ k : ℤ, 2 * w i = k)
    (hA : ∀ i j, vpGge p (A i j) (w i + w j))
    (hL : ∀ i j, L i j ≠ 0 → 0 ≤ padicValRat p (L i j)) (r : ℕ) (hr : L.rank ≤ r) :
    vpGge p (A + (L.map fun c => C ((p : ℚ)⁻¹ * c))).det
      (2 * ∑ i, w i - min r (Finset.univ.filter fun i => w i = 0).card) := by
  classical
  set L' : Matrix ι ι ℚ[X] := L.map fun c => C ((p : ℚ)⁻¹ * c) with hL'
  set z := (Finset.univ.filter fun i => w i = 0).card
  have hdet : (A + L').det = ∑ s : Finset ι, Matrix.det (s.piecewise A L') :=
    (Matrix.detRowAlternating (n := ι) (R := ℚ[X])).map_add_univ A L'
  rw [hdet]
  refine vpGge_sum _ _ fun s _ => ?_
  set T := Finset.univ.filter fun j => j ∉ s with hT
  by_cases hs : r < T.card
  · -- the `p⁻¹L` rows in `T` are dependent, so this determinant vanishes
    obtain ⟨c, hc0, ⟨i, hiT, hi⟩, hsum⟩ := rows_dependent L T (lt_of_le_of_lt hr hs)
    have hz : Matrix.det (s.piecewise A L') = 0 := by
      apply Matrix.det_eq_zero_of_not_linearIndependent_rows
      rw [Fintype.not_linearIndependent_iff]
      refine ⟨fun j => C (c j), ?_, i, by simpa using hi⟩
      funext k
      have hk := congrFun hsum k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row] at hk ⊢
      calc ∑ j, C (c j) * (s.piecewise A L' : Matrix ι ι ℚ[X]) j k
            = ∑ j, C ((p : ℚ)⁻¹ * (c j * L j k)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : j ∈ s
            · have : c j = 0 := hc0 j (by simp [hT, hj])
              simp [this]
            · simp only [Finset.piecewise, hj, ite_false, hL', Matrix.map_apply, ← C_mul]
              ring_nf
        _ = C ((p : ℚ)⁻¹ * ∑ j, c j * L j k) := by
            rw [Finset.mul_sum, map_sum]
        _ = 0 := by rw [hk]; simp
    rw [hz]; exact vpGge_zero _
  · push Not at hs
    apply vpGge_det_of_terms
    intro σ
    have hfac : ∀ i, vpGge p ((s.piecewise A L' : Matrix ι ι ℚ[X]) (σ i) i)
        (if σ i ∈ s then w (σ i) + w i else -1) := by
      intro i
      split_ifs with hi
      · simp only [Finset.piecewise, hi, ite_true]; exact hA _ _
      · simp only [Finset.piecewise, hi, ite_false, hL', Matrix.map_apply]
        refine vpGge_C ?_
        have hLv : vge p (L (σ i) i) 0 := fun h => by exact_mod_cast hL _ _ h
        have := vge_mul (p := p) (vge_inv_p (p := p)) hLv
        simpa using this
    refine vpGge_mono (vpGge_prod _ _ _ fun i _ => hfac i) ?_
    -- the numeric inequality
    set J := Finset.univ.filter fun i => σ i ∉ s with hJ
    have hJT : J.map σ.toEmbedding = T := by
      ext j; simp [hJ, hT]
    have hcard : J.card = T.card := by rw [← hJT, Finset.card_map]
    have hsplit : ∑ i, (if σ i ∈ s then w (σ i) + w i else -1) =
        2 * ∑ i, w i - (∑ i ∈ J, (w (σ i) + 1 / 2) + ∑ i ∈ J, (w i + 1 / 2)) := by
      have e1 : ∑ i, (w (σ i) + w i) = 2 * ∑ i, w i := by
        rw [Finset.sum_add_distrib, Equiv.sum_comp σ w]; ring
      have e2 : ∑ i, (if σ i ∈ s then w (σ i) + w i else -1) =
          ∑ i, (w (σ i) + w i) - ∑ i, (if σ i ∈ s then 0 else (w (σ i) + 1 / 2) + (w i + 1 / 2)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      rw [e2, e1, ← Finset.sum_add_distrib]
      congr 1
      rw [hJ, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have hσ : ∑ i ∈ J, (w (σ i) + 1 / 2) = ∑ j ∈ T, (w j + 1 / 2) := by
      rw [← hJT, Finset.sum_map]; rfl
    have l1 : ∑ i ∈ T, (w i + 1 / 2) ≤ min (T.card : ℚ) (z : ℚ) / 2 := by
      exact weight_loss w hw hw2 T
    have l2 : ∑ i ∈ J, (w i + 1 / 2) ≤ min (T.card : ℚ) (z : ℚ) / 2 := by
      have := weight_loss w hw hw2 J; rw [hcard] at this; exact this
    have hmin : min (T.card : ℚ) (z : ℚ) ≤ min (r : ℚ) (z : ℚ) :=
      min_le_min_right _ (by exact_mod_cast hs)
    rw [hsplit, hσ]
    push_cast
    linarith

end Zeta5
