import Zeta5.Lemma33

/-!
# §3.3 The small-prime bound

`f_i(-x²)` is integer-valued (via binomial identities), the determinant identity (3.11), and the
bound (3.12) from Lemma 3.3.
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-! ## Integer-valued polynomials -/

/-- `A` takes integer values at integers. -/
def IntEval (A : ℚ[X]) : Prop := ∀ x : ℤ, ∃ z : ℤ, A.eval (x : ℚ) = z

theorem IntEval.intValuedAt {A : ℚ[X]} (h : IntEval A) (p : ℕ) [Fact p.Prime] :
    IntValuedAt p A := fun x hx => by
  obtain ⟨z, hz⟩ := h x
  rw [hz] at hx ⊢
  exact_mod_cast vge_int p z hx

theorem IntEval.mul {A B : ℚ[X]} (hA : IntEval A) (hB : IntEval B) : IntEval (A * B) := fun x => by
  obtain ⟨a, ha⟩ := hA x; obtain ⟨b, hb⟩ := hB x
  exact ⟨a * b, by rw [eval_mul, ha, hb]; push_cast; ring⟩

theorem IntEval.pow {A : ℚ[X]} (hA : IntEval A) (n : ℕ) : IntEval (A ^ n) := by
  induction n with
  | zero => exact fun _ => ⟨1, by simp⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem IntEval.add {A B : ℚ[X]} (hA : IntEval A) (hB : IntEval B) : IntEval (A + B) := fun x => by
  obtain ⟨a, ha⟩ := hA x; obtain ⟨b, hb⟩ := hB x
  exact ⟨a + b, by rw [eval_add, ha, hb]; push_cast; ring⟩

theorem intEval_C_int (z : ℤ) : IntEval (C (z : ℚ)) := fun _ => ⟨z, by simp⟩

theorem intEval_X : IntEval X := fun x => ⟨x, by simp⟩

/-- `binom(±x + m, k)` is integer-valued. -/
theorem intEval_bp_comp (k : ℕ) (s m : ℤ) : IntEval ((bp k).comp (C (s : ℚ) * X + C (m : ℚ))) :=
  fun x => by
    obtain ⟨z, hz⟩ := bp_eval_int k (s * x + m)
    exact ⟨z, by rw [eval_comp]; simpa using hz⟩

theorem bp_eval (k : ℕ) (y : ℚ) :
    (bp k).eval y = ((k.factorial : ℚ))⁻¹ * ∏ i ∈ range k, (y - i) := by
  simp [bp, eval_prod]

/-- `∏_{j=1}^N (j² - x²) = ∏_{k<N} (N-k-x)(N-k+x)`. -/
theorem prod_Icc_sq_sub (N : ℕ) (x : ℚ) :
    ∏ j ∈ Icc 1 N, (-x ^ 2 + (j : ℚ) ^ 2) = ∏ k ∈ range N, (((N : ℚ) - x - k) * (x + N - k)) := by
  have hI : Icc 1 N = Ico 1 (N + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← prod_range_reflect]
  refine prod_congr rfl fun k hk => ?_
  have hk' : k < N := mem_range.mp hk
  rw [show 1 + (N - 1 - k) = N - k by omega, Nat.cast_sub hk'.le]
  ring

/-- `D_N(-x²)/(N!)² = binom(N - x, N) binom(N + x, N)`. -/
theorem D_comp_eq (N : ℕ) :
    C (((N.factorial : ℚ) ^ 2)⁻¹) * (D N).comp (-X ^ 2) =
      (bp N).comp (C ((-1 : ℤ) : ℚ) * X + C ((N : ℤ) : ℚ)) *
        (bp N).comp (C ((1 : ℤ) : ℚ) * X + C ((N : ℤ) : ℚ)) := by
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, bp_eval, D, eval_prod, eval_neg,
    eval_pow]
  push_cast
  rw [prod_Icc_sq_sub, prod_mul_distrib]
  have : ∀ k ∈ range N, (-1 * x + N - k) = ((N : ℚ) - x - k) := fun k _ => by ring
  rw [prod_congr rfl this]
  simp only [one_mul]
  ring

theorem intEval_D_comp (N : ℕ) : IntEval (C (((N.factorial : ℚ) ^ 2)⁻¹) * (D N).comp (-X ^ 2)) := by
  rw [D_comp_eq]; exact (intEval_bp_comp N _ _).mul (intEval_bp_comp N _ _)

theorem prod_Icc_succ (m : ℕ) (g : ℕ → ℚ) :
    ∏ j ∈ Icc 1 (m + 1), g j = (∏ j ∈ Icc 1 m, g j) * g (m + 1) := by
  exact Finset.prod_Icc_succ_top (by omega) g

theorem E1_eq (m : ℕ) (x : ℚ) :
    ∏ k ∈ range (2 * m + 2), (x + ((m : ℚ) + 1) - k) =
      (x + m + 1) * x * ∏ j ∈ Icc 1 m, (x ^ 2 - (j : ℚ) ^ 2) := by
  induction m with
  | zero => simp [prod_range_succ]
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 by ring, prod_range_succ', prod_range_succ]
    have : ∏ k ∈ range (2 * m + 2), (x + (((m + 1 : ℕ) : ℚ) + 1) - ((k + 1 : ℕ) : ℚ)) =
        ∏ k ∈ range (2 * m + 2), (x + ((m : ℚ) + 1) - k) :=
      prod_congr rfl fun k _ => by push_cast; ring
    rw [this, ih, prod_Icc_succ]
    push_cast
    ring

theorem E2_eq (m : ℕ) (x : ℚ) :
    ∏ k ∈ range (2 * m + 2), (x + (m : ℚ) - k) =
      x * (x - m - 1) * ∏ j ∈ Icc 1 m, (x ^ 2 - (j : ℚ) ^ 2) := by
  induction m with
  | zero => simp [prod_range_succ]
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 by ring, prod_range_succ', prod_range_succ]
    have : ∏ k ∈ range (2 * m + 2), (x + ((m + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ)) =
        ∏ k ∈ range (2 * m + 2), (x + (m : ℚ) - k) :=
      prod_congr rfl fun k _ => by push_cast; ring
    rw [this, ih, prod_Icc_succ]
    push_cast
    ring

/-- `q_{m+1}(-x²) = binom(x + m + 1, 2m + 2) + binom(x + m, 2m + 2)`. -/
theorem qBasis_comp_eq (m : ℕ) :
    (qBasis (m + 1)).comp (-X ^ 2) =
      (bp (2 * m + 2)).comp (C ((1 : ℤ) : ℚ) * X + C ((m + 1 : ℤ) : ℚ)) +
        (bp (2 * m + 2)).comp (C ((1 : ℤ) : ℚ) * X + C ((m : ℤ) : ℚ)) := by
  apply Polynomial.funext
  intro x
  simp only [qBasis, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, mul_comp, C_comp, X_comp,
    eval_mul, eval_C, eval_neg, eval_pow, eval_X, eval_comp, eval_add, D, eval_prod, bp_eval]
  push_cast
  simp only [one_mul]
  rw [show 2 * (m + 1) = 2 * m + 2 by ring, E1_eq, E2_eq]
  have hneg : ∏ j ∈ Icc 1 m, (-x ^ 2 + (j : ℚ) ^ 2) = (-1) ^ m * ∏ j ∈ Icc 1 m, (x ^ 2 - (j : ℚ) ^ 2) := by
    rw [prod_congr rfl (fun (j : ℕ) _ => show -x ^ 2 + (j : ℚ) ^ 2 = (-1) * (x ^ 2 - (j : ℚ) ^ 2) by ring),
      prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hneg]
  have hf : ((2 * m + 2).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [show m * 2 = 2 * m by ring, pow_mul, neg_one_sq, one_pow, mul_one]

theorem intEval_qBasis (i : ℕ) : IntEval ((qBasis i).comp (-X ^ 2)) := by
  rcases i with _ | m
  · simp only [qBasis, ite_true, one_comp]; exact fun _ => ⟨1, by simp⟩
  · rw [qBasis_comp_eq]; exact (intEval_bp_comp _ _ _).add (intEval_bp_comp _ _ _)

theorem intEval_fBasis (K i : ℕ) : IntEval ((fBasis K i).comp (-X ^ 2)) := by
  unfold fBasis
  rw [mul_comp, pow_comp, mul_comp, C_comp, one_div]
  exact ((intEval_D_comp (Nof K)).pow 3).mul (intEval_qBasis i)

/-- §3.3: `f_i(-x²)` is integer-valued. -/
theorem fBasis_intValued' (p : ℕ) [Fact p.Prime] (K i : ℕ) :
    IntValuedAt p ((fBasis K i).comp (-X ^ 2)) :=
  (intEval_fBasis K i).intValuedAt p

/-! ## The determinant identity (3.11) -/

theorem D_monic (m : ℕ) : (D m).Monic := sqPoleProd_monic _

theorem D_natDegree (m : ℕ) : (D m).natDegree = m := by
  rw [show D m = sqPoleProd (Icc 1 m) from rfl, sqPoleProd_natDegree]; simp

/-- The leading coefficient `(-1)ⁱ 2/(2i)!` of `q_i` (and `1` for `i = 0`). -/
def qLead (i : ℕ) : ℚ := if i = 0 then 1 else (-1) ^ i * 2 / ((2 * i).factorial : ℚ)

theorem qBasis_natDegree_le (i : ℕ) : (qBasis i).natDegree ≤ i := by
  rcases i with _ | m
  · simp [qBasis]
  · simp only [qBasis, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    refine (natDegree_mul_le).trans ?_
    refine le_trans (add_le_add ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      (D_natDegree m).le) ?_
    omega

theorem qBasis_coeff_self (i : ℕ) : (qBasis i).coeff i = qLead i := by
  rcases i with _ | m
  · simp [qBasis, qLead]
  · simp only [qBasis, qLead, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hlc := (D_monic m).coeff_natDegree
    rw [D_natDegree] at hlc
    rw [mul_assoc, coeff_C_mul, coeff_X_mul, hlc, mul_one]

theorem qBasis_eq_sum (h i : ℕ) (hi : i < h) :
    qBasis i = ∑ k : Fin h, C ((qBasis i).coeff k) * X ^ (k : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => C ((qBasis i).coeff k) * X ^ k)]
  conv_lhs => rw [as_sum_range' _ _ (lt_of_le_of_lt (qBasis_natDegree_le i) hi)]
  simp only [C_mul_X_pow_eq_monomial]

/-- The coefficient matrix of the `q_i`, lower triangular. -/
def Qc (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := Matrix.of fun i k => (qBasis i).coeff k

theorem Qc_lower (h : ℕ) : (Qc h).IsLowerTriangular := by
  intro i k hik
  simp only [Qc, Matrix.of_apply]
  exact coeff_eq_zero_of_natDegree_lt ((qBasis_natDegree_le i).trans_lt hik)

theorem Qc_det (h : ℕ) : (Qc h).det = ∏ i : Fin h, qLead i := by
  rw [Matrix.det_of_isLowerTriangular _ (Qc_lower h)]
  exact prod_congr rfl fun i _ => by simp [Qc, qBasis_coeff_self]

theorem qLead_sq_prod (h : ℕ) :
    (∏ i ∈ range h, qLead i) ^ 2 =
      4 ^ (h - 1) / ∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2 := by
  rcases h with _ | n
  · simp
  · rw [prod_range_succ', Nat.add_sub_cancel, mul_pow]
    simp only [qLead, Nat.add_one_ne_zero, ite_false, ite_true, one_pow, mul_one]
    have hI : Icc 1 n = Ico 1 (n + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← prod_pow,
      show (4 : ℚ) ^ n = ∏ _k ∈ range n, (4 : ℚ) by simp, ← prod_div_distrib]
    refine prod_congr rfl fun x _ => ?_
    have hs : ((-1 : ℚ) ^ (x + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [show 1 + x = x + 1 by ring, div_pow, mul_pow, hs]
    norm_num

theorem fBasis_mul (K i j : ℕ) :
    fBasis K i * fBasis K j =
      C ((((Nof K).factorial : ℚ) ^ 2)⁻¹ ^ 6) * (D (Nof K) ^ 6 * (qBasis i * qBasis j)) := by
  unfold fBasis
  rw [one_div]
  simp only [mul_pow, C_pow]
  ring

theorem muX_fBasis (K : ℕ) (i j : Fin (hof K)) :
    muX (Icc 1 K) (fBasis K i * fBasis K j) =
      C ((((Nof K).factorial : ℚ) ^ 2)⁻¹ ^ 6) *
        ∑ k : Fin (hof K), ∑ l : Fin (hof K), C (Qc _ i k * Qc _ j l) * G K k l := by
  rw [fBasis_mul, muX_C_mul]
  congr 1
  rw [qBasis_eq_sum (hof K) i i.2, qBasis_eq_sum (hof K) j j.2, sum_mul_sum, mul_sum, muX_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, muX_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [show D (Nof K) ^ 6 * (C ((qBasis i).coeff k) * X ^ (k : ℕ) * (C ((qBasis j).coeff l) * X ^ (l : ℕ)))
      = C ((qBasis i).coeff k * (qBasis j).coeff l) * (D (Nof K) ^ 6 * X ^ ((k : ℕ) + l)) by
    rw [C_mul, pow_add]; ring, muX_C_mul]
  rfl

theorem S_eq_lead (K : ℕ) :
    S K = ((K.factorial : ℚ) ^ 2 * (((Nof K).factorial : ℚ) ^ 2)⁻¹ ^ 6) ^ hof K *
      (∏ i : Fin (hof K), qLead i) ^ 2 := by
  rw [Fin.prod_univ_eq_prod_range (fun i => qLead i), qLead_sq_prod, S, inv_pow, ← pow_mul]
  have h1 : ((Nof K).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ∏ i ∈ Icc 1 (hof K - 1), ((2 * i).factorial : ℚ) ^ 2 ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => by positivity
  field_simp
  ring_nf
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ h1, one_pow, mul_one]

theorem det_fBasis_matrix (K : ℕ) :
    (Matrix.of fun i j : Fin (hof K) =>
      C ((K.factorial : ℚ) ^ 2) * muX (Icc 1 K) (fBasis K i * fBasis K j)) =
      C ((K.factorial : ℚ) ^ 2 * (((Nof K).factorial : ℚ) ^ 2)⁻¹ ^ 6) •
        ((Qc (hof K)).map C * G K * ((Qc (hof K)).map C).transpose) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.of_apply, muX_fBasis, Matrix.smul_apply, smul_eq_mul, C_mul, mul_assoc]
  congr 1
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [C_mul, mul_right_comm]

theorem map_C_det {h : ℕ} (M : Matrix (Fin h) (Fin h) ℚ) : (M.map C).det = C M.det := by
  rw [RingHom.map_det]; rfl

/-- **(3.11)**: `F_K = det[(K!)² µ_X(f_i f_j / D_K)]`. -/
theorem F_eq_det_fBasis' (K : ℕ) :
    F K = (Matrix.of fun i j : Fin (hof K) =>
      C ((K.factorial : ℚ) ^ 2) * muX (Icc 1 K) (fBasis K i * fBasis K j)).det := by
  rw [det_fBasis_matrix, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Fintype.card_fin, map_C_det, Qc_det, F, Delta, S_eq_lead]
  simp only [map_mul, map_pow]
  ring

/-! ## The small-prime bound (3.12) -/

theorem fBasis_natDegree_le (K i : ℕ) : (fBasis K i).natDegree ≤ 3 * Nof K + i := by
  unfold fBasis
  refine natDegree_mul_le.trans (add_le_add ?_ (qBasis_natDegree_le i))
  refine natDegree_pow_le.trans ?_
  exact Nat.mul_le_mul_left 3 ((natDegree_C_mul_le _ _).trans (D_natDegree _).le)

theorem signedPoles_Icc (K : ℕ) : signedPoles (Icc 1 K) = (Icc (-(K : ℤ)) K).erase 0 := by
  ext x
  simp only [signedPoles, mem_union, mem_image, mem_Icc, mem_erase]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · intro hx
    rcases le_or_gt 0 x with h | h
    · exact Or.inl ⟨x.toNat, by omega, by omega⟩
    · exact Or.inr ⟨(-x).toNat, by omega, by omega⟩

/-- Each entry of the matrix in (3.11) satisfies the Lemma 3.3 bound. -/
theorem fBasis_entry_vge (p : ℕ) [Fact p.Prime] (K : ℕ) (hK : 40 ∣ K) (i j : Fin (hof K)) :
    vpGge p (C ((K.factorial : ℚ) ^ 2) * muX (Icc 1 K) (fBasis K i * fBasis K j))
      (-6 * Nat.log p (5 * K) - padicValNat p 24) := by
  obtain ⟨n, rfl⟩ := hK
  have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
  have hh : hof (40 * n) = 37 * n := by unfold hof; omega
  have hi : (i : ℕ) < 37 * n := by have := i.2; omega
  have hj : (j : ℕ) < 37 * n := by have := j.2; omega
  set A := C ((-1 : ℚ) ^ (Icc 1 (40 * n)).card) * X ^ 5 *
    (fBasis (40 * n) i * fBasis (40 * n) j).comp (-X ^ 2) with hA
  have h0 : 0 ∉ Icc 1 (40 * n) := by simp
  rw [pullback _ h0, ← tauX_C_mul, signedPoles_Icc]
  have hAint : IntValuedAt p A := by
    refine IntEval.intValuedAt ?_ p
    rw [hA, mul_comp]
    have hc : IntEval (C ((-1 : ℚ) ^ (Icc 1 (40 * n)).card)) :=
      fun _ => ⟨(-1) ^ (Icc 1 (40 * n)).card, by simp⟩
    exact (hc.mul (intEval_X.pow 5)).mul ((intEval_fBasis _ _).mul (intEval_fBasis _ _))
  have hdeg : A.natDegree ≤ 5 + 184 * n := by
    have h1 : (fBasis (40 * n) i * fBasis (40 * n) j).natDegree ≤ 92 * n := by
      refine natDegree_mul_le.trans ?_
      have := fBasis_natDegree_le (40 * n) i
      have := fBasis_natDegree_le (40 * n) j
      omega
    have h2 : ((fBasis (40 * n) i * fBasis (40 * n) j).comp (-X ^ 2)).natDegree ≤ 184 * n := by
      refine natDegree_comp_le.trans ?_
      rw [natDegree_neg, natDegree_X_pow]
      omega
    rw [hA]
    refine natDegree_mul_le.trans (add_le_add ?_ h2)
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C, natDegree_X_pow]
  refine vpGge_mono (lemma_3_3' p (40 * n) (5 + 184 * n) A hAint hdeg) ?_
  have hlog : Nat.log p (max (2 * (40 * n)) (5 + 184 * n + 1)) ≤ Nat.log p (5 * (40 * n)) :=
    Nat.log_mono_right (max_le (by omega) (by omega))
  have : (Nat.log p (max (2 * (40 * n)) (5 + 184 * n + 1)) : ℚ) ≤ Nat.log p (5 * (40 * n)) := by
    exact_mod_cast hlog
  linarith

/-- **(3.12)**: `v_p^G(F_K) ≥ -6h ⌊log_p(5K)⌋ - h v_p(24)` for every prime `p`. -/
theorem vpG_F_ge' (p : ℕ) [Fact p.Prime] (K : ℕ) (hK : 40 ∣ K) :
    vpGge p (F K) (-6 * hof K * Nat.log p (5 * K) - hof K * padicValNat p 24) := by
  rw [F_eq_det_fBasis']
  apply vpGge_det_of_terms
  intro σ
  refine vpGge_mono (vpGge_prod _ _ (fun _ => (-6 * Nat.log p (5 * K) - padicValNat p 24 : ℚ))
    fun i _ => by simpa using fBasis_entry_vge p K hK (σ i) i) ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

end Zeta5