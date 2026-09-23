import Zeta5.Valuation

/-!
# The closed form (4.14) of `γ_p^out`

`gammaOut_eq_sum'`: summing the weights (4.12) of the outer basis and applying the rank loss of
Lemma 4.2 gives exactly `γ_p^out`.
-/

open Polynomial Finset

noncomputable section

namespace Zeta5

/-- For `x < 2p`: `x % p = 0 ↔ x = 0 ∨ x = p`. -/
theorem mod_eq_zero_lt_two {p x : ℕ} (_hp : 0 < p) (hx : x < 2 * p) :
    x % p = 0 ↔ x = 0 ∨ x = p := by
  rcases lt_or_ge x p with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

/-- Membership in a class `±a (mod p)` for `j < 3p`. -/
theorem class_char {p a j : ℕ} (ha1 : 1 ≤ a) (ha : a < p) (hj : j < 3 * p) :
    (j % p = a % p ∨ (j + a) % p = 0) ↔
      (j = a ∨ j = p + a ∨ j = 2 * p + a ∨ j + a = p ∨ j + a = 2 * p ∨ j + a = 3 * p) := by
  have hp : 0 < p := by omega
  have hdm := Nat.div_add_mod j p
  have hr := Nat.mod_lt j hp
  have hq : j / p < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by linarith)
  set q := j / p
  set r := j % p
  have hja : (j + a) % p = (r + a) % p := by
    rw [← hdm, show p * q + r + a = (r + a) + p * q by ring, Nat.add_mul_mod_self_left]
  rw [hja, Nat.mod_eq_of_lt ha, mod_eq_zero_lt_two hp (by omega)]
  interval_cases q <;> omega

/-- Membership in the zero class for `j < 3p`. -/
theorem zero_class_char {p j : ℕ} (hp : 0 < p) (hj : j < 3 * p) :
    (j % p = 0 % p ∨ (j + 0) % p = 0) ↔ (j = 0 ∨ j = p ∨ j = 2 * p) := by
  have hdm := Nat.div_add_mod j p
  have hr := Nat.mod_lt j hp
  have hq : j / p < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by linarith)
  set q := j / p
  set r := j % p
  simp only [Nat.zero_mod, add_zero]
  interval_cases q <;> omega

def ind (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

theorem ite_eq_ind {c d : Prop} [Decidable c] [Decidable d] (h : c ↔ d) :
    (if c then 1 else 0 : ℕ) = ind d := by
  unfold ind; by_cases hc : c
  · simp [hc, h.mp hc]
  · have hd : ¬ d := fun hd => hc (h.mpr hd)
    simp [hc, hd]

/-- The class `±a` in `[L, K]`, as six indicators. -/
theorem card_class {p a K L : ℕ} (ha1 : 1 ≤ a) (ha : 2 * a < p) (hK : K < 3 * p) :
    ((Icc L K).filter fun j => j % p = a % p ∨ (j + a) % p = 0).card =
      ind (L ≤ a ∧ a ≤ K) + ind (L ≤ p - a ∧ p - a ≤ K) + ind (L ≤ p + a ∧ p + a ≤ K) +
        ind (L ≤ 2 * p - a ∧ 2 * p - a ≤ K) + ind (L ≤ 2 * p + a ∧ 2 * p + a ≤ K) +
          ind (L ≤ 3 * p - a ∧ 3 * p - a ≤ K) := by
  have hset : ((Icc L K).filter fun j => j % p = a % p ∨ (j + a) % p = 0) =
      ({a, p - a, p + a, 2 * p - a, 2 * p + a, 3 * p - a} : Finset ℕ).filter
        (fun j => L ≤ j ∧ j ≤ K) := by
    ext j
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [class_char ha1 (by omega) (by omega)] at h3
      exact ⟨by omega, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨h1, h2⟩, (class_char ha1 (by omega) (by omega)).mpr (by omega)⟩
  rw [hset, card_filter]
  rw [sum_insert (by simp only [mem_insert, mem_singleton]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton]; omega),
    sum_insert (by simp only [mem_singleton]; omega), sum_singleton]
  simp only [ite_eq_ind Iff.rfl]
  ring

theorem ind_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : ind P = ind Q := by
  unfold ind; by_cases hP : P
  · simp [hP, h.mp hP]
  · have hQ : ¬ Q := fun hq => hP (h.mpr hq)
    simp [hP, hQ]

theorem ind_pos {P : Prop} [Decidable P] (h : P) : ind P = 1 := by simp [ind, h]
theorem ind_neg {P : Prop} [Decidable P] (h : ¬ P) : ind P = 0 := by simp [ind, h]
theorem ind_le_one (P : Prop) [Decidable P] : ind P ≤ 1 := by unfold ind; split_ifs <;> omega
theorem ind_mul (P Q : Prop) [Decidable P] [Decidable Q] : ind P * ind Q = ind (P ∧ Q) := by
  unfold ind; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- Facts implied by (4.9) and `40 ∣ K`. -/
structure OuterFacts (K p : ℕ) : Prop where
  p7 : 7 ≤ p
  pK : p ≤ K
  K3 : K < 3 * p
  N2 : 2 * Nof K < p
  m2 : 2 * mHalf p + 1 = p
  v1 : K < 2 * p → K % p = K - p
  v2 : 2 * p ≤ K → K % p = K - 2 * p

theorem outerFacts {K p : ℕ} [hp : Fact p.Prime] (h : OuterHyp K p) : OuterFacts K p := by
  obtain ⟨h7, hpK, hK3, -, hN, -⟩ := h
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  refine ⟨h7, hpK, hK3, hN, by unfold mHalf; omega, fun h1 => ?_, fun h2 => ?_⟩
  · rw [Nat.mod_eq_sub_mod hpK, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_sub_mod hpK, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem ell_eq {K p a : ℕ} (F : OuterFacts K p) (ha1 : 1 ≤ a) (ham : a ≤ mHalf p) :
    ell p K a = (if K < 2 * p then 2 else 4) + ind (a ≤ K % p) + ind (p ≤ K % p + a) := by
  have := F.m2
  have := F.pK
  have := F.K3
  unfold ell
  rw [card_class ha1 (by omega) F.K3]
  rw [ind_pos (by omega : 1 ≤ a ∧ a ≤ K), ind_pos (by omega : 1 ≤ p - a ∧ p - a ≤ K)]
  by_cases hK : K < 2 * p
  · rw [if_pos hK, F.v1 hK, ind_neg (by omega : ¬ (1 ≤ 2 * p + a ∧ 2 * p + a ≤ K)),
      ind_neg (by omega : ¬ (1 ≤ 3 * p - a ∧ 3 * p - a ≤ K)),
      ind_congr (by omega : (1 ≤ p + a ∧ p + a ≤ K) ↔ a ≤ K - p),
      ind_congr (by omega : (1 ≤ 2 * p - a ∧ 2 * p - a ≤ K) ↔ p ≤ K - p + a)]
    ring
  · rw [if_neg hK, F.v2 (by omega), ind_pos (by omega : 1 ≤ p + a ∧ p + a ≤ K),
      ind_pos (by omega : 1 ≤ 2 * p - a ∧ 2 * p - a ≤ K),
      ind_congr (by omega : (1 ≤ 2 * p + a ∧ 2 * p + a ≤ K) ↔ a ≤ K - 2 * p),
      ind_congr (by omega : (1 ≤ 3 * p - a ∧ 3 * p - a ≤ K) ↔ p ≤ K - 2 * p + a)]

theorem outerCount_add {K p a : ℕ} (F : OuterFacts K p) (ha1 : 1 ≤ a) (ham : a ≤ mHalf p) :
    outerCount K p a + ind (a ≤ Nof K) = ell p K a := by
  have := F.m2
  have := F.N2
  have := F.pK
  have := F.K3
  unfold outerCount outerClassPoles ell
  rw [card_class ha1 (by omega) F.K3, card_class ha1 (by omega) F.K3,
    ind_congr (by omega : (Nof K + 1 ≤ a ∧ a ≤ K) ↔ ¬ a ≤ Nof K),
    ind_congr (by omega : (Nof K + 1 ≤ p - a ∧ p - a ≤ K) ↔ (1 ≤ p - a ∧ p - a ≤ K)),
    ind_congr (by omega : (Nof K + 1 ≤ p + a ∧ p + a ≤ K) ↔ (1 ≤ p + a ∧ p + a ≤ K)),
    ind_congr (by omega : (Nof K + 1 ≤ 2 * p - a ∧ 2 * p - a ≤ K) ↔ (1 ≤ 2 * p - a ∧ 2 * p - a ≤ K)),
    ind_congr (by omega : (Nof K + 1 ≤ 2 * p + a ∧ 2 * p + a ≤ K) ↔ (1 ≤ 2 * p + a ∧ 2 * p + a ≤ K)),
    ind_congr (by omega : (Nof K + 1 ≤ 3 * p - a ∧ 3 * p - a ≤ K) ↔ (1 ≤ 3 * p - a ∧ 3 * p - a ≤ K)),
    ind_pos (by omega : 1 ≤ a ∧ a ≤ K)]
  have : ind (¬ a ≤ Nof K) + ind (a ≤ Nof K) = 1 := by
    unfold ind; split_ifs <;> omega
  omega

theorem outerCount_zero {K p : ℕ} (F : OuterFacts K p) :
    outerCount K p 0 = if K < 2 * p then 1 else 2 := by
  have := F.N2
  have hp : 0 < p := by have := F.p7; omega
  unfold outerCount outerClassPoles
  have hset : ((Icc (Nof K + 1) K).filter fun j => j % p = 0 % p ∨ (j + 0) % p = 0) =
      ({p, 2 * p} : Finset ℕ).filter (fun j => j ≤ K) := by
    ext j
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [zero_class_char hp (by have := F.K3; omega)] at h3
      exact ⟨by omega, h2⟩
    · rintro ⟨h3, h2⟩
      exact ⟨⟨by omega, h2⟩, (zero_class_char hp (by have := F.K3; omega)).mpr (by omega)⟩
  rw [hset, card_filter, sum_insert (by simp; omega), sum_singleton]
  have := F.pK
  split_ifs with h1 h2 h3 <;> omega

/-- The weight (4.12) of row `i` of a class with `ℓ` poles and `δ = d`. -/
def Wc (l d i : ℕ) : ℚ := if i < l - 2 then min 0 ((i : ℚ) + 3 * (d : ℚ) - ((l : ℚ) + 4) / 2) else 0

theorem cls2 (A B d : ℕ) (hA : A ≤ 1) (hB : B ≤ 1) (hd : d ≤ 1) :
    2 * ∑ i ∈ range (2 + A + B - d), Wc (2 + A + B) d i =
      -7 * ((A : ℚ) + B) + 6 * (d : ℚ) * ((A : ℚ) + B) ∧
    ((range (2 + A + B - d)).filter fun i => Wc (2 + A + B) d i = 0).card = 2 - d + d * A * B := by
  rw [card_filter]
  interval_cases A <;> interval_cases B <;> interval_cases d <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, sum_range_succ, sum_range_zero, Wc] <;>
    norm_num

theorem cls4 (A B d : ℕ) (hA : A ≤ 1) (hB : B ≤ 1) (hd : d ≤ 1) :
    2 * ∑ i ∈ range (4 + A + B - d), Wc (4 + A + B) d i =
      -14 - 7 * ((A : ℚ) + B) + (d : ℚ) * (12 + 5 * ((A : ℚ) + B)) ∧
    ((range (4 + A + B - d)).filter fun i => Wc (4 + A + B) d i = 0).card = 2 + d * A * B := by
  rw [card_filter]
  interval_cases A <;> interval_cases B <;> interval_cases d <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, sum_range_succ, sum_range_zero, Wc] <;>
    norm_num

/-- The weight as a function of natural numbers. -/
def Wn (K p a i : ℕ) : ℚ :=
  if a = 0 then (if outerCount K p 0 = 1 then -1 / 2 else if i = 0 then -2 else 0)
  else Wc (ell p K a) (ind (a ≤ Nof K)) i

theorem wOut_eq (K p : ℕ) (x : OuterIdx K p) : wOut K p x = Wn K p x.1 x.2 := by
  unfold wOut Wn Wc ind
  by_cases h0 : (x.1 : ℕ) = 0
  · simp only [h0, if_true]
  · simp only [h0, if_false]
    split_ifs <;> simp

theorem sum_wOut (K p : ℕ) :
    ∑ x, wOut K p x = ∑ a ∈ range (mHalf p + 1), ∑ i ∈ range (outerCount K p a), Wn K p a i := by
  rw [Fintype.sum_sigma]
  simp only [wOut_eq]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ i ∈ range (outerCount K p a), Wn K p a i)]
  exact sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun i => Wn K p a i) _

theorem card_zero_wOut (K p : ℕ) :
    (Finset.univ.filter fun x => wOut K p x = 0).card =
      ∑ a ∈ range (mHalf p + 1), ((range (outerCount K p a)).filter fun i => Wn K p a i = 0).card := by
  rw [card_filter, Fintype.sum_sigma]
  simp only [wOut_eq, card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ i ∈ range (outerCount K p a),
    if Wn K p a i = 0 then 1 else 0)]
  exact sum_congr rfl fun a _ =>
    Fin.sum_univ_eq_sum_range (fun i => if Wn K p a i = 0 then 1 else 0) _

theorem range_succ_eq (m : ℕ) : range (m + 1) = insert 0 (Icc 1 m) := by
  ext a; simp only [mem_range, mem_insert, mem_Icc]; omega

theorem class_low {K p a : ℕ} (F : OuterFacts K p) (hK : K < 2 * p) (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) :
    2 * ∑ i ∈ range (outerCount K p a), Wn K p a i =
      -7 * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a)) +
        6 * (ind (a ≤ Nof K) : ℚ) * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a)) ∧
    ((range (outerCount K p a)).filter fun i => Wn K p a i = 0).card =
      2 - ind (a ≤ Nof K) + ind (a ≤ Nof K) * ind (a ≤ K % p) * ind (p ≤ K % p + a) := by
  have hell := ell_eq F ha1 ham
  rw [if_pos hK] at hell
  have hoc := outerCount_add F ha1 ham
  have hoc' : outerCount K p a =
      2 + ind (a ≤ K % p) + ind (p ≤ K % p + a) - ind (a ≤ Nof K) := by omega
  have hW : ∀ i, Wn K p a i =
      Wc (2 + ind (a ≤ K % p) + ind (p ≤ K % p + a)) (ind (a ≤ Nof K)) i := by
    intro i; unfold Wn; rw [if_neg (by omega), hell]
  simp only [hoc', hW]
  exact cls2 _ _ _ (ind_le_one _) (ind_le_one _) (ind_le_one _)

theorem class_high {K p a : ℕ} (F : OuterFacts K p) (hK : ¬ K < 2 * p) (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) :
    2 * ∑ i ∈ range (outerCount K p a), Wn K p a i =
      -14 - 7 * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a)) +
        (ind (a ≤ Nof K) : ℚ) * (12 + 5 * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a))) ∧
    ((range (outerCount K p a)).filter fun i => Wn K p a i = 0).card =
      2 + ind (a ≤ Nof K) * ind (a ≤ K % p) * ind (p ≤ K % p + a) := by
  have hell := ell_eq F ha1 ham
  rw [if_neg hK] at hell
  have hoc := outerCount_add F ha1 ham
  have hoc' : outerCount K p a =
      4 + ind (a ≤ K % p) + ind (p ≤ K % p + a) - ind (a ≤ Nof K) := by omega
  have hW : ∀ i, Wn K p a i =
      Wc (4 + ind (a ≤ K % p) + ind (p ≤ K % p + a)) (ind (a ≤ Nof K)) i := by
    intro i; unfold Wn; rw [if_neg (by omega), hell]
  simp only [hoc', hW]
  exact cls4 _ _ _ (ind_le_one _) (ind_le_one _) (ind_le_one _)

theorem sum_ind_cast (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ a ∈ s, (ind (P a) : ℚ) = ((s.filter P).card : ℚ) := by
  rw [card_filter]; push_cast; simp [ind]

theorem ind_mul_cast (P Q : Prop) [Decidable P] [Decidable Q] :
    (ind P : ℚ) * (ind Q : ℚ) = (ind (P ∧ Q) : ℚ) := by
  rw [← Nat.cast_mul, ind_mul]

/-- The interval counts used in (4.14). -/
theorem counts {K p : ℕ} (F : OuterFacts K p) :
    ((Icc 1 (mHalf p)).filter fun a => a ≤ K % p).card +
        ((Icc 1 (mHalf p)).filter fun a => p ≤ K % p + a).card = K % p ∧
    ((Icc 1 (mHalf p)).filter fun a => a ≤ Nof K ∧ a ≤ K % p).card = min (Nof K) (K % p) ∧
    ((Icc 1 (mHalf p)).filter fun a => a ≤ Nof K ∧ p ≤ K % p + a).card =
      Nof K + K % p + 1 - p ∧
    ((Icc 1 (mHalf p)).filter fun a => a ≤ Nof K).card = Nof K ∧
    ((Icc 1 (mHalf p)).filter fun a => (a ≤ Nof K ∧ a ≤ K % p) ∧ p ≤ K % p + a).card =
      Nof K + K % p + 1 - p := by
  have hm := F.m2
  have hN := F.N2
  have hvp : K % p < p := Nat.mod_lt _ (by have := F.p7; omega)
  have e1 : ((Icc 1 (mHalf p)).filter fun a => a ≤ K % p) = Icc 1 (min (mHalf p) (K % p)) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e2 : ((Icc 1 (mHalf p)).filter fun a => p ≤ K % p + a) = Icc (p - K % p) (mHalf p) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e3 : ((Icc 1 (mHalf p)).filter fun a => a ≤ Nof K ∧ a ≤ K % p) =
      Icc 1 (min (Nof K) (K % p)) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e4 : ((Icc 1 (mHalf p)).filter fun a => a ≤ Nof K ∧ p ≤ K % p + a) =
      Icc (p - K % p) (Nof K) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e5 : ((Icc 1 (mHalf p)).filter fun a => a ≤ Nof K) = Icc 1 (Nof K) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e6 : ((Icc 1 (mHalf p)).filter fun a => (a ≤ Nof K ∧ a ≤ K % p) ∧ p ≤ K % p + a) =
      Icc (p - K % p) (Nof K) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [e1, e2, e3, e4, e5, e6]
  simp only [Nat.card_Icc]
  omega

/-- Summing the weights (4.12) and applying Lemma 4.2's rank loss gives `γ_p^out` (4.14). -/
theorem gammaOut_eq_sum' {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    (gammaOut K p : ℚ) = 2 * ∑ x, wOut K p x -
      min (rOut K p) (Finset.univ.filter fun x => wOut K p x = 0).card := by
  have F := outerFacts h
  obtain ⟨c12, c3, c4, c5, c6⟩ := counts F
  have hm := F.m2
  have hN := F.N2
  have hpK := F.pK
  have hvp : K % p < p := Nat.mod_lt _ (by have := F.p7; omega)
  set I := Icc 1 (mHalf p) with hI
  have hA := sum_ind_cast I (fun a => a ≤ K % p)
  have hB := sum_ind_cast I (fun a => p ≤ K % p + a)
  have hdA := sum_ind_cast I (fun a => a ≤ Nof K ∧ a ≤ K % p)
  have hdB := sum_ind_cast I (fun a => a ≤ Nof K ∧ p ≤ K % p + a)
  have hd := sum_ind_cast I (fun a => a ≤ Nof K)
  have hdAB := sum_ind_cast I (fun a => (a ≤ Nof K ∧ a ≤ K % p) ∧ p ≤ K % p + a)
  have hIc : I.card = mHalf p := by rw [hI, Nat.card_Icc]; omega
  have hpt1 : ∀ a : ℕ, (ind (a ≤ Nof K) : ℚ) * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a)) =
      (ind (a ≤ Nof K ∧ a ≤ K % p) : ℚ) + ind (a ≤ Nof K ∧ p ≤ K % p + a) := by
    intro a; rw [mul_add, ind_mul_cast, ind_mul_cast]
  have hpt2 : ∀ a : ℕ, ind (a ≤ Nof K) * ind (a ≤ K % p) * ind (p ≤ K % p + a) =
      ind ((a ≤ Nof K ∧ a ≤ K % p) ∧ p ≤ K % p + a) := by
    intro a; rw [ind_mul, ind_mul]
  have hW0 : ∑ x, wOut K p x = ∑ i ∈ range (outerCount K p 0), Wn K p 0 i +
      ∑ a ∈ I, ∑ i ∈ range (outerCount K p a), Wn K p a i := by
    rw [sum_wOut, range_succ_eq, sum_insert (by simp)]
  have hZ0 : (Finset.univ.filter fun x => wOut K p x = 0).card =
      ((range (outerCount K p 0)).filter fun i => Wn K p 0 i = 0).card +
        ∑ a ∈ I, ((range (outerCount K p a)).filter fun i => Wn K p a i = 0).card := by
    rw [card_zero_wOut, range_succ_eq, sum_insert (by simp)]
  set u := Nof K + K % p + 1 - p with hu
  by_cases hK2 : K < 2 * p
  · have hv := F.v1 hK2
    have hoc0 : outerCount K p 0 = 1 := by rw [outerCount_zero F, if_pos hK2]
    have hz0 : ∑ i ∈ range (outerCount K p 0), Wn K p 0 i = -1 / 2 := by
      rw [hoc0]; simp [Wn, hoc0]
    have hzc : ((range (outerCount K p 0)).filter fun i => Wn K p 0 i = 0).card = 0 := by
      rw [hoc0]; simp [Wn, hoc0]
    have hS : 2 * ∑ a ∈ I, ∑ i ∈ range (outerCount K p a), Wn K p a i =
        -7 * (((I.filter fun a => a ≤ K % p).card : ℚ) + (I.filter fun a => p ≤ K % p + a).card) +
          6 * (((I.filter fun a => a ≤ Nof K ∧ a ≤ K % p).card : ℚ) +
            (I.filter fun a => a ≤ Nof K ∧ p ≤ K % p + a).card) := by
      rw [mul_sum, sum_congr rfl fun a ha => (class_low F hK2 (mem_Icc.mp ha).1 (mem_Icc.mp ha).2).1]
      simp only [mul_assoc, hpt1]
      rw [← hA, ← hB, ← hdA, ← hdB]
      simp only [mul_add, sum_add_distrib, ← mul_sum]
      rfl
    have hZ : (Finset.univ.filter fun x => wOut K p x = 0).card = 2 * mHalf p - Nof K + u := by
      have hq : (((Finset.univ.filter fun x => wOut K p x = 0).card : ℕ) : ℚ) =
          2 * (mHalf p : ℚ) - Nof K + u := by
        rw [hZ0, hzc, zero_add, Nat.cast_sum]
        rw [sum_congr rfl fun a ha => by
          rw [(class_low F hK2 (mem_Icc.mp ha).1 (mem_Icc.mp ha).2).2, hpt2]]
        have hc : ∀ a : ℕ, ((2 - ind (a ≤ Nof K) + ind ((a ≤ Nof K ∧ a ≤ K % p) ∧ p ≤ K % p + a)
            : ℕ) : ℚ) = 2 - (ind (a ≤ Nof K) : ℚ) +
              (ind ((a ≤ Nof K ∧ a ≤ K % p) ∧ p ≤ K % p + a) : ℚ) := by
          intro a
          have := ind_le_one (a ≤ Nof K)
          push_cast [Nat.cast_sub (by omega : ind (a ≤ Nof K) ≤ 2)]
          ring
        simp only [hc, sum_add_distrib, sum_sub_distrib, sum_const, hIc, nsmul_eq_mul]
        rw [hd, hdAB, c5, c6]
        push_cast
        ring
      have : (((2 * mHalf p - Nof K + u : ℕ)) : ℚ) = 2 * (mHalf p : ℚ) - Nof K + u := by
        push_cast [Nat.cast_sub (by omega : Nof K ≤ 2 * mHalf p)]; ring
      exact_mod_cast hq.trans this.symm
    rw [hZ, hW0, mul_add, hS, hz0]
    unfold gammaOut
    simp only [hK2, if_true]
    rw [← hu]
    have hzz : ((p : ℤ) - 1 - (Nof K : ℤ) + (u : ℤ)) = ((2 * mHalf p - Nof K + u : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : Nof K ≤ 2 * mHalf p)]; omega
    rw [hzz, ← Nat.cast_min]
    have e12 : ((#(I.filter fun a => a ≤ K % p) : ℕ) : ℚ) +
        ((#(I.filter fun a => p ≤ K % p + a) : ℕ) : ℚ) = (K : ℚ) - p := by
      rw [← Nat.cast_add, c12, hv, Nat.cast_sub hpK]
    have e34 : ((#(I.filter fun a => a ≤ Nof K ∧ a ≤ K % p) : ℕ) : ℚ) +
        ((#(I.filter fun a => a ≤ Nof K ∧ p ≤ K % p + a) : ℕ) : ℚ) =
          ((min (Nof K) (K % p) : ℕ) : ℚ) + (u : ℚ) := by
      rw [c3, c4]
    generalize min (Nof K) (K % p) = mn at e34 ⊢
    push_cast
    linear_combination 7 * e12 - 6 * e34
  · have hv := F.v2 (by omega)
    have hoc0 : outerCount K p 0 = 2 := by rw [outerCount_zero F, if_neg hK2]
    have hz0 : ∑ i ∈ range (outerCount K p 0), Wn K p 0 i = -2 := by
      rw [hoc0]; simp [Wn, hoc0]
    have hzc : ((range (outerCount K p 0)).filter fun i => Wn K p 0 i = 0).card = 1 := by
      rw [hoc0, card_filter]; simp [Wn, hoc0, sum_range_succ]
    have hpt3 : ∀ a : ℕ, -14 - 7 * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a)) +
        (ind (a ≤ Nof K) : ℚ) * (12 + 5 * ((ind (a ≤ K % p) : ℚ) + ind (p ≤ K % p + a))) =
        -14 - 7 * (ind (a ≤ K % p) : ℚ) - 7 * (ind (p ≤ K % p + a) : ℚ) +
          12 * (ind (a ≤ Nof K) : ℚ) + 5 * (ind (a ≤ Nof K ∧ a ≤ K % p) : ℚ) +
            5 * (ind (a ≤ Nof K ∧ p ≤ K % p + a) : ℚ) := by
      intro a
      linear_combination 5 * hpt1 a
    have hS : 2 * ∑ a ∈ I, ∑ i ∈ range (outerCount K p a), Wn K p a i =
        -14 * (mHalf p : ℚ) -
          7 * (((I.filter fun a => a ≤ K % p).card : ℚ) + (I.filter fun a => p ≤ K % p + a).card) +
          12 * ((I.filter fun a => a ≤ Nof K).card : ℚ) +
          5 * (((I.filter fun a => a ≤ Nof K ∧ a ≤ K % p).card : ℚ) +
            (I.filter fun a => a ≤ Nof K ∧ p ≤ K % p + a).card) := by
      rw [mul_sum, sum_congr rfl fun a ha =>
        (class_high F hK2 (mem_Icc.mp ha).1 (mem_Icc.mp ha).2).1]
      rw [sum_congr rfl fun a _ => hpt3 a]
      simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [hA, hB, hd, hdA, hdB]
      simp only [Nat.card_Icc, Nat.add_sub_cancel]
      ring
    have hZ : (Finset.univ.filter fun x => wOut K p x = 0).card = 2 * mHalf p + 1 + u := by
      have hq : (((Finset.univ.filter fun x => wOut K p x = 0).card : ℕ) : ℚ) =
          2 * (mHalf p : ℚ) + 1 + u := by
        rw [hZ0, hzc, Nat.cast_add, Nat.cast_sum]
        rw [sum_congr rfl fun a ha => by
          rw [(class_high F hK2 (mem_Icc.mp ha).1 (mem_Icc.mp ha).2).2, hpt2]]
        push_cast
        simp only [sum_add_distrib, sum_const, hIc, nsmul_eq_mul]
        rw [hdAB, c6]
        ring
      exact_mod_cast hq
    rw [hZ, hW0, mul_add, hS, hz0]
    unfold gammaOut
    simp only [hK2, if_false]
    rw [← hu]
    have hzz : ((p : ℤ) + (u : ℤ)) = ((2 * mHalf p + 1 + u : ℕ) : ℤ) := by
      push_cast; omega
    rw [hzz, ← Nat.cast_min]
    have e12 : ((#(I.filter fun a => a ≤ K % p) : ℕ) : ℚ) +
        ((#(I.filter fun a => p ≤ K % p + a) : ℕ) : ℚ) = (K : ℚ) - 2 * p := by
      rw [← Nat.cast_add, c12, hv, Nat.cast_sub (by omega)]; push_cast; ring
    have e34 : ((#(I.filter fun a => a ≤ Nof K ∧ a ≤ K % p) : ℕ) : ℚ) +
        ((#(I.filter fun a => a ≤ Nof K ∧ p ≤ K % p + a) : ℕ) : ℚ) =
          ((min (Nof K) (K % p) : ℕ) : ℚ) + (u : ℚ) := by
      rw [c3, c4]
    have hmq : 2 * (mHalf p : ℚ) + 1 = p := by exact_mod_cast hm
    rw [c5]
    generalize min (Nof K) (K % p) = mn at e34 ⊢
    push_cast
    linear_combination 7 * e12 - 5 * e34 + 7 * hmq

end Zeta5