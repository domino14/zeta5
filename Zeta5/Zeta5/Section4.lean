import Zeta5.Prop43
import Zeta5.Prop43Large

/-!
# §4 Local estimates for the determinant

Inner range (Proposition 4.1, via the basis (4.5) and the entry bounds (4.2), (4.3)), the
rank lemma (Lemma 4.2), and the outer range (Proposition 4.3, via (4.10) and (4.12)).
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

-- The inner-range results (`Lin_nonneg`, `sum_Lin`, `innerBasis_unimodular`,
-- `innerGram_entry_bound`, Proposition 4.1) are in `InnerBasis.lean` and `InnerFinal.lean`.

/-- (4.1): the inner range. -/
def InnerHyp (K M p : ℕ) : Prop :=
  40 ≤ M ∧ 40 ∣ K ∧ 0 < K ∧ 200 * M ^ 2 ≤ K ∧ K < p * M ∧ 3 * p ≤ K

/-- Under (4.1): `p > 200M` and `p² > 5K`. -/
theorem innerHyp_bounds {K M p : ℕ} (h : InnerHyp K M p) : 200 * M < p ∧ 5 * K < p ^ 2 := by
  obtain ⟨hM, -, -, hKM, hpM, -⟩ := h
  have h1 : 200 * M < p := by
    by_contra hc
    push Not at hc
    nlinarith [Nat.mul_le_mul_right M hc]
  exact ⟨h1, by nlinarith⟩

/-- (4.4): `0 ≤ E < m` and `mT + E = h - L₀ + 3(N - m_N)`. -/
theorem TE_spec {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    0 ≤ Ein K M p ∧ Ein K M p < mHalf p ∧
      (mHalf p : ℤ) * Tin K M p + Ein K M p = rhs44 K M p := by
  have hp := (innerHyp_bounds h).1
  have hm : (0 : ℤ) < mHalf p := by
    have : 0 < mHalf p := by unfold mHalf; have := h.1; omega
    exact_mod_cast this
  exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm, Int.mul_ediv_add_emod _ _⟩



/-- `x` is a half-integer: `2x ∈ ℤ`. -/
def IsHalfInt (x : ℚ) : Prop := ∃ k : ℤ, 2 * x = k

theorem isHalfInt_fold_min {α : Type*} (s : Finset α) (init : ℚ) (f : α → ℚ)
    (h0 : IsHalfInt init) (hf : ∀ a ∈ s, IsHalfInt (f a)) : IsHalfInt (s.fold min init f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    rcases min_choice (f a) (s.fold min init f) with hm | hm <;> rw [hm]
    · exact hf a (Finset.mem_insert_self a s)
    · exact ih fun b hb => hf b (Finset.mem_insert_of_mem hb)

theorem wIn_isHalfInt (K M p a i : ℕ) (pos : ℕ → ℕ) : IsHalfInt (wIn K M p a i pos) := by
  unfold wIn
  generalize Nof K / p = u
  generalize K / p = v
  split_ifs
  · refine isHalfInt_fold_min _ _ _ ⟨2 * (2 * i + 6 * (u : ℤ) - (v : ℤ)) + 1, ?_⟩
      fun c _ => ⟨2 * Zin K M p c pos - (ell p K c + 4), ?_⟩
    · push_cast; ring
    · push_cast; ring
  · exact ⟨2 * i + 2 * bIn K p a - (ell p K a + 4), by push_cast; ring⟩

/-- (4.8): `γ_p^in` is an integer, since it is twice a sum of half-integers. -/
theorem gammaIn_isInt' (K M p : ℕ) (pos : ℕ → ℕ) : ∃ n : ℤ, gammaIn K M p pos = n := by
  classical
  unfold gammaIn
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  choose k hk using fun a i => wIn_isHalfInt K M p a i pos
  refine ⟨∑ a ∈ Finset.range (mHalf p + 1), ∑ i ∈ Finset.range (Lin K M p a pos).toNat, k a i, ?_⟩
  push_cast
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => hk a i

theorem gammaIn_isInt {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p) :
    gammaIn K M p = ⌊gammaIn K M p⌋ := by
  obtain ⟨n, hn⟩ := gammaIn_isInt' K M p (defaultPos K p)
  rw [hn, Int.floor_intCast]

/-- Ties in the ordering by `ℓ_K` do not affect `γ_p^in`: any injective ordering `pos` of the
classes `1..m` compatible with decreasing `ℓ_K` gives the same value. -/
theorem gammaIn_tie_independent {K M p : ℕ} [Fact p.Prime] (h : InnerHyp K M p)
    (pos : ℕ → ℕ) (hinj : Set.InjOn pos (Set.Icc 1 (mHalf p)))
    (hord : ∀ a ∈ Set.Icc 1 (mHalf p), ∀ c ∈ Set.Icc 1 (mHalf p),
      ell p K a < ell p K c → pos c < pos a) :
    gammaIn K M p pos = gammaIn K M p := by
  sorry


/-- The row weights of the inner basis. -/
def wInIdx (K M p : ℕ) (x : InnerIdx K M p) : ℚ := wIn K M p x.1 x.2



-- Lemma 4.2 (`lemma_4_2`) is in `Lemma42.lean`.

/-- (4.9) holds when `K ≥ 200M²` and `K/3 < p ≤ K`. -/
theorem outer_hyp_of_range {K M p : ℕ} (hM : 40 ≤ M) (hK : 40 ∣ K) (hKM : 200 * M ^ 2 ≤ K)
    (hp : p.Prime) (h1 : K < 3 * p) (h2 : p ≤ K) : OuterHyp K p := by
  have hK : 320000 ≤ K := by nlinarith
  unfold OuterHyp Nof
  refine ⟨by omega, h2, h1, ?_, by omega, by omega⟩
  nlinarith

/-- The polynomial moments `µ(tᵉ)` have `v_p ≥ -1`, and are `p`-integral for `e < 2p - 3`. -/
theorem muMono_padicVal (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (e : ℕ) (he : muMono e ≠ 0) :
    -1 ≤ padicValRat p (muMono e) ∧ (e < 2 * p - 3 → 0 ≤ padicValRat p (muMono e)) := by
  exact muMono_padicVal' p hp e he

/-- (4.10): `G_K = A + p⁻¹L` with `L` integral, constant, and `rank L ≤ r_p`. -/
theorem decomp_4_10 {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    ∃ L : Matrix (Fin (hof K)) (Fin (hof K)) ℚ,
      G K = Aout K p + L.map (fun c => C ((p : ℚ)⁻¹ * c)) ∧
      (∀ i j, L i j ≠ 0 → 0 ≤ padicValRat p (L i j)) ∧ L.rank ≤ rOut K p := by
  exact decomp_4_10' hK h

/-- (4.11): the outer basis is `ℤ_p`-unimodular. -/
theorem outerBasis_unimodular {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    ∃ e : OuterIdx K p ≃ Fin (hof K),
      padicValRat p (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (outerBasis K p (e.symm x)).coeff d).det = 0 ∧
      (Matrix.of fun (x : Fin (hof K)) (d : Fin (hof K)) =>
        (outerBasis K p (e.symm x)).coeff d).det ≠ 0 := by
  exact outerBasis_unimodular' hK h

/-- (4.12) and the zero-class weights: entries of `A` in the outer basis satisfy the weights. -/
theorem outerGram_entry_bound {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p)
    (x y : OuterIdx K p) :
    vpGge p (outerGram K p x y) (wOut K p x + wOut K p y) := by
  exact outerGram_entry_bound' hK h x y

/-- The table after (4.14): summing (4.12) and applying Lemma 4.2 gives `γ_p^out`. -/
theorem gammaOut_eq_sum {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    (gammaOut K p : ℚ) = 2 * ∑ x, wOut K p x -
      min (rOut K p) (Finset.univ.filter fun x => wOut K p x = 0).card := by
  exact gammaOut_eq_sum' hK h

/-- Proposition 4.3: under (4.9), `v_p^G(Δ_K) ≥ γ_p^out`. -/
theorem prop_4_3 {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    vpGge p (Delta K) (gammaOut K p) := by
  exact prop_4_3' hK h

/-- Proposition 4.3, second part: `v_p^G(Δ_K) ≥ 0` for `p > K`. -/
theorem prop_4_3_large {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (hp : K < p) :
    vpGge p (Delta K) 0 := by
  exact prop_4_3_large' hK hp

end Zeta5
