import Zeta5.MuMod
import Zeta5.Lemma33

/-!
# §4.2 Entry bounds in the outer basis, (4.12)
-/

open Polynomial Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## `p`-integral rationals and integral polynomials -/

/-- The subring of `p`-integral rationals. -/
def Zp (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | vge p x 0}
  mul_mem' ha hb := by simpa using vge_mul ha hb
  one_mem' := vge_one
  add_mem' ha hb := vge_add ha hb
  zero_mem' := vge_zero 0
  neg_mem' ha := vge_neg ha

theorem lifts_Zp {P : ℚ[X]} (hP : vpGge p P 0) : P ∈ lifts (Zp p).subtype :=
  (lifts_iff_coeff_lifts P).mpr fun n => ⟨⟨P.coeff n, hP n⟩, rfl⟩

theorem vpGge_map_Zp (P : (Zp p)[X]) : vpGge p (P.map (Zp p).subtype) 0 := fun n => by
  rw [coeff_map]; exact (P.coeff n).2

/-- Division of an integral polynomial by an integral monic polynomial is integral. -/
theorem divByMonic_vge {P Q : ℚ[X]} (hP : vpGge p P 0) (hQ : Q.Monic) (hQi : vpGge p Q 0) :
    vpGge p (P /ₘ Q) 0 := by
  obtain ⟨Q', hQ'map, -, hQ'monic⟩ := lifts_and_degree_eq_and_monic (lifts_Zp hQi) hQ
  obtain ⟨P', hP'⟩ := lifts_Zp hP
  have hP'' : P'.map (Zp p).subtype = P := hP'
  rw [← hQ'map, ← hP'', ← map_divByMonic _ hQ'monic]
  exact vpGge_map_Zp _

/-- For an integral polynomial and integral `x, y`: `v(R(x) - R(y)) ≥ v(x - y)`. -/
theorem eval_sub_vge {R : ℚ[X]} (hR : vpGge p R 0) {x y b : ℚ} (hx : vge p x 0) (hy : vge p y 0)
    (hxy : vge p (x - y) b) : vge p (R.eval x - R.eval y) b := by
  obtain ⟨R', hR'⟩ := lifts_Zp hR
  have hR'' : R'.map (Zp p).subtype = R := hR'
  have e : ∀ a : Zp p, (Zp p).subtype (R'.eval a) = R.eval (a : ℚ) := fun a => by
    rw [← hR'', eval_map]
    exact (eval₂_at_apply (Zp p).subtype a).symm
  obtain ⟨z, hz⟩ := sub_dvd_eval_sub (⟨x, hx⟩ : Zp p) ⟨y, hy⟩ R'
  have h := congrArg (Zp p).subtype hz
  simp only [map_sub, map_mul, e] at h
  rw [h]
  simpa using vge_mul hxy z.2

theorem vpGge_X_add_C_int (j : ℤ) : vpGge p (X + C (j : ℚ)) 0 :=
  vpGge_add vpGge_X (vpGge_C (vge_int p j))

theorem vpGge_sqPoleProd (S : Finset ℕ) : vpGge p (sqPoleProd S) 0 := by
  have := vpGge_prod S (fun j : ℕ => X + C ((j : ℚ) ^ 2)) (fun _ => (0 : ℚ)) fun j _ => by
    have h := vpGge_X_add_C_int (p := p) ((j : ℤ) ^ 2)
    push_cast at h
    exact h
  rw [sum_const_zero] at this
  exact this

theorem vpGge_mul0 {A B : ℚ[X]} (hA : vpGge p A 0) (hB : vpGge p B 0) : vpGge p (A * B) 0 := by
  simpa using vpGge_mul hA hB

theorem vpGge_pow0 {A : ℚ[X]} (hA : vpGge p A 0) (n : ℕ) : vpGge p (A ^ n) 0 := by
  induction n with
  | zero => simpa using vpGge_one (p := p)
  | succ n ih => rw [pow_succ]; exact vpGge_mul0 ih hA

/-! ## The modified functional `µ⁰_X` -/

/-- `µ⁰` on polynomials. -/
def muModPoly (p : ℕ) (Q : ℚ[X]) : ℚ := Q.sum fun e c => c * (muMono e - cCorr p e / p)

theorem muXmod_def (S : Finset ℕ) (P : ℚ[X]) :
    muXmod p S P = C (muModPoly p (P /ₘ sqPoleProd S)) + ∑ j ∈ S, C (sqResidue S P j) * muPole j :=
  rfl

theorem muModPoly_vge (hp7 : 7 ≤ p) {Q : ℚ[X]} (hQ : vpGge p Q 0) : vge p (muModPoly p Q) 0 := by
  unfold muModPoly Polynomial.sum
  exact vge_sum _ _ fun e _ => by simpa using vge_mul (hQ e) (muMod_vge p hp7 e)

theorem muModPoly_sub_muPoly (Q : ℚ[X]) :
    muModPoly p Q = muPoly Q - Q.sum fun e c => c * (cCorr p e / p) := by
  unfold muModPoly muPoly Polynomial.sum
  rw [← Finset.sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- `µ⁰_X` also depends only on the rational function. -/
theorem muXmod_mul_cancel_set (T S : Finset ℕ) (hd : Disjoint T S) (P : ℚ[X]) :
    muXmod p (T ∪ S) (P * sqPoleProd T) = muXmod p S P := by
  have hcancel := muX_mul_cancel_set T S hd P
  have hq : (P * sqPoleProd T) /ₘ sqPoleProd (T ∪ S) = P /ₘ sqPoleProd S := by
    have hu : sqPoleProd (T ∪ S) = sqPoleProd T * sqPoleProd S := prod_union hd
    rw [hu, mul_divByMonic_mul (sqPoleProd_monic T) (sqPoleProd_monic S)]
  have e1 : ∀ S' P', muXmod p S' P' =
      muX S' P' - C ((P' /ₘ sqPoleProd S').sum fun e c => c * (cCorr p e / p)) := by
    intro S' P'
    rw [muXmod_def, muX, muModPoly_sub_muPoly, C_sub]
    ring
  rw [e1, e1, hcancel, hq]

theorem muXmod_empty (P : ℚ[X]) : muXmod p ∅ P = C (muModPoly p P) := by
  simp [muXmod_def, sqPoleProd]

/-! ## Arithmetic of the pole classes -/

theorem mod_add_small {r a q : ℕ} (hr : r < q) (ha : a < q) :
    (r + a) % q = 0 ↔ r + a = 0 ∨ r + a = q := by
  constructor
  · intro h
    have h1 := Nat.mod_add_div (r + a) q
    have h2 : (r + a) / q < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    interval_cases hq : (r + a) / q <;> [left; right] <;> nlinarith
  · rintro (h | h) <;> rw [h] <;> simp

theorem class_cond_unique {q j a c : ℕ} (hq : 2 ≤ q) (ha : 2 * a < q) (hc : 2 * c < q)
    (h1 : j % q = a % q ∨ (j + a) % q = 0) (h2 : j % q = c % q ∨ (j + c) % q = 0) : a = c := by
  have hja : (j + a) % q = (j % q + a) % q := by rw [Nat.add_mod, Nat.mod_eq_of_lt (a := a) (by omega)]
  have hjc : (j + c) % q = (j % q + c) % q := by rw [Nat.add_mod, Nat.mod_eq_of_lt (a := c) (by omega)]
  have hr : j % q < q := Nat.mod_lt _ (by omega)
  rw [Nat.mod_eq_of_lt (by omega : a < q)] at h1
  rw [Nat.mod_eq_of_lt (by omega : c < q)] at h2
  rw [hja, mod_add_small hr (by omega)] at h1
  rw [hjc, mod_add_small hr (by omega)] at h2
  omega

section Classes

variable {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p)
include hK h

theorem OuterHyp.odd : 2 * mHalf p + 1 = p := by
  have h7 := h.1
  have hodd := (hp.out.eq_two_or_odd').resolve_left (by omega)
  obtain ⟨k, hk⟩ := hodd
  unfold mHalf; omega

theorem mem_class {a j : ℕ} : j ∈ outerClassPoles K p a ↔
    Nof K + 1 ≤ j ∧ j ≤ K ∧ (j % p = a % p ∨ (j + a) % p = 0) := by
  simp [outerClassPoles, and_assoc]

theorem class_disjoint {a c : ℕ} (ha : a ≤ mHalf p) (hc : c ≤ mHalf p) (hac : a ≠ c) :
    Disjoint (outerClassPoles K p a) (outerClassPoles K p c) := by
  have hodd := OuterHyp.odd hK h
  rw [Finset.disjoint_left]
  intro j hja hjc
  rw [mem_class hK h] at hja hjc
  exact hac (class_cond_unique (by have := h.1; omega) (by omega) (by omega) hja.2.2 hjc.2.2)

theorem class_small {a j : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) (hj : j ∈ outerClassPoles K p a)
    (hjp : j < p) : j = a ∨ j = p - a := by
  have hodd := OuterHyp.odd hK h
  rw [mem_class hK h] at hj
  rw [Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt (by omega : a < p)] at hj
  rcases hj.2.2 with h1 | h1
  · exact Or.inl h1
  · rw [Nat.add_mod, Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt (by omega : a < p),
      mod_add_small hjp (by omega)] at h1
    omega

theorem class_not_dvd {a j : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hj : j ∈ outerClassPoles K p a) : ¬ p ∣ j := by
  have hodd := OuterHyp.odd hK h
  intro hdvd
  have h0 : j % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [mem_class hK h] at hj
  rcases hj.2.2 with h1 | h1
  · rw [h0, Nat.mod_eq_of_lt (by omega : a < p)] at h1; omega
  · rw [Nat.add_mod, h0, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : a < p)] at h1
    omega

theorem pa_mem {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) : p - a ∈ outerClassPoles K p a := by
  have hodd := OuterHyp.odd hK h
  have h2 := h.2.1
  have h5 := h.2.2.2.2.1
  rw [mem_class hK h]
  refine ⟨by omega, by omega, Or.inr ?_⟩
  rw [Nat.sub_add_cancel (by omega), Nat.mod_self]

theorem a_mem_iff {a : ℕ} (_ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    a ∈ outerClassPoles K p a ↔ Nof K < a := by
  have hodd := OuterHyp.odd hK h
  rw [mem_class hK h]
  have := h.2.1
  constructor
  · intro h1; omega
  · intro h1; exact ⟨h1, by omega, Or.inl rfl⟩

theorem card_outerClass {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    (outerClassPoles K p a).card + (if a ≤ Nof K then 1 else 0) = ell p K a := by
  have hodd := OuterHyp.odd hK h
  have h2 := h.2.1
  have h5 := h.2.2.2.2.1
  have hsplit : (Icc 1 K).filter (fun j => j % p = a % p ∨ (j + a) % p = 0) =
      (outerClassPoles K p a) ∪ (if a ≤ Nof K then {a} else ∅) := by
    ext j
    simp only [mem_filter, mem_Icc, mem_union, outerClassPoles]
    constructor
    · rintro ⟨⟨hj1, hjK⟩, hc⟩
      by_cases hjN : Nof K + 1 ≤ j
      · exact Or.inl ⟨⟨hjN, hjK⟩, hc⟩
      · right
        have hjp : j < p := by omega
        rw [Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt (by omega : a < p)] at hc
        rcases hc with hc | hc
        · subst hc; simp [show j ≤ Nof K by omega]
        · rw [Nat.add_mod, Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt (by omega : a < p),
            mod_add_small hjp (by omega)] at hc
          omega
    · rintro (⟨⟨hj1, hjK⟩, hc⟩ | hj)
      · exact ⟨⟨by omega, hjK⟩, hc⟩
      · split_ifs at hj with haN
        · rw [mem_singleton] at hj; subst hj
          exact ⟨⟨ha1, by omega⟩, Or.inl rfl⟩
        · simp at hj
  unfold ell
  rw [hsplit, card_union_of_disjoint]
  · split_ifs <;> simp
  · split_ifs with haN
    · rw [disjoint_singleton_right, mem_class hK h]; omega
    · exact disjoint_empty_right _

theorem zero_class : outerClassPoles K p 0 = if 2 * p ≤ K then {p, 2 * p} else {p} := by
  have hodd := OuterHyp.odd hK h
  obtain ⟨h7, h2, h3, -, h5, -⟩ := h
  ext j
  simp only [outerClassPoles, mem_filter, mem_Icc, Nat.zero_mod, add_zero, or_self]
  constructor
  · rintro ⟨⟨hj1, hjK⟩, hj0⟩
    obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hj0
    have hq1 : 1 ≤ q := by rcases q with _ | q <;> simp_all
    have hq3 : q < 3 := by by_contra hc; push Not at hc; nlinarith
    interval_cases q <;> split_ifs <;> simp_all <;> omega
  · intro hj
    split_ifs at hj with h2p
    · simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl <;> refine ⟨⟨by omega, by omega⟩, by simp⟩
    · rw [mem_singleton] at hj; subst hj
      exact ⟨⟨by omega, h2⟩, Nat.mod_self _⟩

end Classes

/-! ## Valuations of integers and pole values -/

theorem vge_int_of_dvd (z : ℤ) (k : ℕ) (hk : (p : ℤ) ^ k ∣ z) : vge p (z : ℚ) k := by
  intro hz
  have hz' : z ≠ 0 := by exact_mod_cast hz
  rw [padicValRat.of_int]
  have := padicValInt_dvd_iff (p := p) k z |>.mp hk
  rcases this with h0 | h0
  · exact absurd h0 hz'
  · exact_mod_cast h0

theorem padicValRat_int_le_one (z : ℤ) (hz : z ≠ 0) (hlt : z.natAbs < p ^ 2) :
    (padicValRat p (z : ℚ) : ℚ) ≤ 1 := by
  have h := padicValRat_int_le_log (p := p) z hz (p ^ 2 - 1) (Nat.le_sub_one_of_lt hlt)
  have hlog : Nat.log p (p ^ 2 - 1) = 1 := by
    rw [Nat.log_eq_iff (by norm_num)]
    have h2 := hp.out.two_le
    have hpp : p < p ^ 2 := by nlinarith
    constructor
    · rw [pow_one]; omega
    · rw [show p ^ (1 + 1) = p ^ 2 by ring]; omega
  rw [hlog] at h; exact_mod_cast h

theorem padicValRat_int_of_not_dvd (z : ℤ) (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]; rfl

theorem vge_div_of_le {x y b U : ℚ} (hx : vge p x b) (hy : y ≠ 0)
    (hU : (padicValRat p y : ℚ) ≤ U) : vge p (x / y) (b - U) := by
  intro hxy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxy
  rw [padicValRat.div hx0 hy]
  push_cast
  linarith [hx hx0]

/-- `µ_X(1/(t+j²))` has coefficients of valuation `≥ β` when `j⁴ H_j` and `1/(2j)` do. -/
theorem muPole_vge (j : ℕ) {β : ℚ} (hβ : β ≤ 0) (hp2 : p ≠ 2)
    (h1 : vge p ((j : ℚ) ^ 4 * H5 j) β) (h2 : vge p (1 / (2 * (j : ℚ))) β) :
    vpGge p (muPole j) β := by
  have h4 : vge p (1 / 4 : ℚ) 0 := by
    have := vge_inv_int (p := p) 4 (by norm_num) 0 (by
      intro hd; simp only [zero_add, pow_one] at hd
      have : (p : ℤ) ∣ 2 ^ 2 := by norm_num; exact hd
      have := Int.Prime.dvd_pow' hp.out this
      have := (Int.natCast_dvd_natCast.mp this)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this))
    simpa using this
  have e : muPole j =
      C ((j : ℚ) ^ 4) * X + C (-((j : ℚ) ^ 4 * H5 j) + -(1 / 4) + 1 / (2 * (j : ℚ))) := by
    unfold muPole; simp only [map_sub, map_add, map_neg, map_mul, map_pow]; ring
  rw [e]
  refine vpGge_add (vpGge_mono (vpGge_mul (vpGge_C (vge_int p ((j : ℤ) ^ 4) |> fun h => by
    simpa using h)) vpGge_X) (by linarith)) (vpGge_C ?_)
  exact vge_add (vge_add (vge_neg h1) (vge_neg (vge_mono h4 hβ))) h2

/-! ## Structure of the outer basis -/

/-- The poles of `D_tail`. -/
def tailPoles (K : ℕ) : Finset ℕ := Icc (Nof K + 1) K

/-- The `q`-part of an outer basis row: `outerBasis = P_a · oq`. -/
def oq (K p : ℕ) (x : OuterIdx K p) : ℚ[X] :=
  if (x.1 : ℕ) = 0 then (X + C ((p : ℚ) ^ 2)) ^ (x.2 : ℕ)
  else if (x.2 : ℕ) < ell p K x.1 - 2 then (X + C (((x.1 : ℕ) : ℚ) ^ 2)) ^ (x.2 : ℕ)
  else sqPoleProd ((outerClassPoles K p x.1).filter fun j => p < j) *
    (X + C (((x.1 : ℕ) : ℚ) ^ 2)) ^ ((x.2 : ℕ) - (ell p K x.1 - 2))

theorem outerBasis_eq (K p : ℕ) (x : OuterIdx K p) :
    outerBasis K p x = sqPoleProd (tailPoles K \ outerClassPoles K p x.1) * oq K p x := by
  unfold outerBasis oq tailPoles
  by_cases h0 : (x.1 : ℕ) = 0 <;> by_cases h1 : (x.2 : ℕ) < ell p K x.1 - 2 <;>
    simp only [h0, h1, if_true, if_false] <;> ring

theorem vpGge_X_add_C_natSq (n : ℕ) : vpGge p (X + C ((n : ℚ) ^ 2)) 0 := by
  have h := vpGge_X_add_C_int (p := p) ((n : ℤ) ^ 2)
  rwa [Int.cast_pow, Int.cast_natCast] at h

theorem oq_vge (K p : ℕ) [Fact p.Prime] (x : OuterIdx K p) : vpGge p (oq K p x) 0 := by
  unfold oq
  split_ifs
  · exact vpGge_pow0 (vpGge_X_add_C_natSq p) _
  · exact vpGge_pow0 (vpGge_X_add_C_natSq _) _
  · exact vpGge_mul0 (vpGge_sqPoleProd _) (vpGge_pow0 (vpGge_X_add_C_natSq _) _)

theorem D_eq_sqPoleProd (m : ℕ) : D m = sqPoleProd (Icc 1 m) := rfl

theorem Icc_eq_union (K : ℕ) : Icc 1 K = Icc 1 (Nof K) ∪ tailPoles K := by
  ext x; simp only [tailPoles, mem_Icc, mem_union]; unfold Nof; omega

theorem Icc_tail_disjoint (K : ℕ) : Disjoint (Icc 1 (Nof K)) (tailPoles K) := by
  rw [Finset.disjoint_left]; intro x hx hx'; simp only [tailPoles, mem_Icc] at hx hx'; omega

theorem class_subset_tail (K p a : ℕ) : outerClassPoles K p a ⊆ tailPoles K :=
  filter_subset _ _

theorem sqPoleProd_union {s t : Finset ℕ} (hd : Disjoint s t) :
    sqPoleProd (s ∪ t) = sqPoleProd s * sqPoleProd t := prod_union hd

theorem sqPoleProd_union_inter (s t : Finset ℕ) :
    sqPoleProd (s ∪ t) * sqPoleProd (s ∩ t) = sqPoleProd s * sqPoleProd t := prod_union_inter

theorem sqPoleProd_Icc_split (K : ℕ) :
    sqPoleProd (Icc 1 K) = D (Nof K) * sqPoleProd (tailPoles K) := by
  rw [Icc_eq_union K, sqPoleProd_union (Icc_tail_disjoint K), D_eq_sqPoleProd]

/-- The cancellation behind a same-class entry. -/
theorem same_class_cancel (K : ℕ) (Ca : Finset ℕ) (hCa : Ca ⊆ tailPoles K) (A B : ℚ[X]) :
    muXmod p (Icc 1 K) (D (Nof K) ^ 6 * (sqPoleProd (tailPoles K \ Ca) * A) *
        (sqPoleProd (tailPoles K \ Ca) * B)) =
      muXmod p Ca (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ Ca) * A * B) := by
  have hT : Disjoint (Icc 1 (Nof K) ∪ (tailPoles K \ Ca)) Ca := by
    rw [Finset.disjoint_left]
    intro j hj hjC
    rcases mem_union.mp hj with h1 | h1
    · exact Finset.disjoint_left.mp (Icc_tail_disjoint K) h1 (hCa hjC)
    · exact (mem_sdiff.mp h1).2 hjC
  have hU : (Icc 1 (Nof K) ∪ (tailPoles K \ Ca)) ∪ Ca = Icc 1 K := by
    rw [Icc_eq_union K]
    ext j; simp only [mem_union, mem_sdiff]
    have := @hCa j
    tauto
  have hsq : sqPoleProd (Icc 1 (Nof K) ∪ (tailPoles K \ Ca)) =
      D (Nof K) * sqPoleProd (tailPoles K \ Ca) := by
    rw [sqPoleProd_union (Finset.disjoint_of_subset_right sdiff_subset (Icc_tail_disjoint K)),
      D_eq_sqPoleProd]
  rw [← hU, ← muXmod_mul_cancel_set _ Ca hT, hsq]
  exact congrArg (muXmod p _) (by ring)

/-- The cancellation behind a cross-class entry. -/
theorem cross_class_cancel (K : ℕ) (Ca Cc : Finset ℕ) (hd : Disjoint Ca Cc) (A B : ℚ[X]) :
    muXmod p (Icc 1 K) (D (Nof K) ^ 6 * (sqPoleProd (tailPoles K \ Ca) * A) *
        (sqPoleProd (tailPoles K \ Cc) * B)) =
      C (muModPoly p (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ (Ca ∪ Cc)) * A * B)) := by
  have hprod : sqPoleProd (tailPoles K \ Ca) * sqPoleProd (tailPoles K \ Cc) =
      sqPoleProd (tailPoles K) * sqPoleProd (tailPoles K \ (Ca ∪ Cc)) := by
    have e1 : (tailPoles K \ Ca) ∪ (tailPoles K \ Cc) = tailPoles K := by
      ext j; simp only [mem_union, mem_sdiff]
      have : j ∈ Ca → j ∉ Cc := fun h => Finset.disjoint_left.mp hd h
      tauto
    have e2 : (tailPoles K \ Ca) ∩ (tailPoles K \ Cc) = tailPoles K \ (Ca ∪ Cc) := by
      ext j; simp only [mem_inter, mem_sdiff, mem_union]; tauto
    rw [← sqPoleProd_union_inter, e1, e2]
  rw [← muXmod_empty (p := p), ← union_empty (Icc 1 K),
    ← muXmod_mul_cancel_set (Icc 1 K) ∅ (disjoint_empty_right _), sqPoleProd_Icc_split]
  exact congrArg (muXmod p _) (by linear_combination (D (Nof K) ^ 5 * D (Nof K) * A * B) * hprod)

/-! ## Valuations at the poles of a class -/

theorem vge_pow0 {x : ℚ} (hx : vge p x 0) (n : ℕ) : vge p (x ^ n) 0 := by
  induction n with
  | zero => simpa using vge_one (p := p)
  | succ n ih => rw [pow_succ]; simpa using vge_mul ih hx

theorem eval_vge0 {P : ℚ[X]} (hP : vpGge p P 0) {x : ℚ} (hx : vge p x 0) :
    vge p (P.eval x) 0 := by
  rw [eval_eq_sum_range]
  exact vge_sum _ _ fun n _ => by simpa using vge_mul (hP n) (vge_pow0 hx n)

theorem vge_pow' {x b : ℚ} (hx : vge p x b) (n : ℕ) : vge p (x ^ n) (n * b) := by
  induction n with
  | zero => simpa using vge_one (p := p)
  | succ n ih =>
    rw [pow_succ]
    exact vge_mono (vge_mul ih hx) (by push_cast; ring_nf; rfl)

theorem vge_natCast (n : ℕ) : vge p (n : ℚ) 0 := by simpa using vge_int p (n : ℤ)

theorem vge_neg_sq (j : ℕ) : vge p (-(j : ℚ) ^ 2) 0 := by
  simpa using vge_neg (vge_pow0 (vge_natCast (p := p) j) 2)

theorem log_le_one_of_lt_sq {K : ℕ} (hK : K < p ^ 2) : Nat.log p K ≤ 1 := by
  rcases Nat.eq_zero_or_pos K with rfl | hpos
  · simp
  · exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow hp.out.one_lt hpos.ne').mpr hK)

/-- `µ⁰_X(R / ∏_{j∈S}(t+j²))` is bounded by its residue terms, for integral `R`. -/
theorem muXmod_vge_of_residues (hp7 : 7 ≤ p) (S : Finset ℕ) {R : ℚ[X]} (hR : vpGge p R 0)
    {B : ℚ} (hB : B ≤ 0) (hres : ∀ j ∈ S, vpGge p (C (sqResidue S R j) * muPole j) B) :
    vpGge p (muXmod p S R) B := by
  rw [muXmod_def]
  refine vpGge_add (vpGge_mono (vpGge_C (muModPoly_vge hp7
    (divByMonic_vge hR (sqPoleProd_monic S) (vpGge_sqPoleProd S)))) hB) ?_
  exact vpGge_sum _ _ hres

theorem vge_inv_two_mul {j : ℕ} (hj : ¬ p ∣ j) (hp2 : p ≠ 2) : vge p (1 / (2 * (j : ℚ))) 0 := by
  have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero p)
  have := vge_inv_int (p := p) (2 * j) (by omega) 0 (by
    intro hd
    simp only [zero_add, pow_one] at hd
    rcases Int.Prime.dvd_mul' hp.out hd with h2 | h2
    · have := Int.le_of_dvd (by norm_num) h2
      have := hp.out.two_le
      exact hp2 (by omega)
    · exact hj (Int.natCast_dvd_natCast.mp h2))
  simpa using this

section ClassVal

variable {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p)
include hK h

theorem sq_sub_vge {a j : ℕ} (hj : j ∈ outerClassPoles K p a) :
    vge p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 1 := by
  rw [mem_class hK h] at hj
  have hd : (p : ℤ) ∣ (a : ℤ) ^ 2 - (j : ℤ) ^ 2 := by
    rcases hj.2.2 with h1 | h1
    · have h2 : (p : ℤ) ∣ (a : ℤ) - j := Nat.modEq_iff_dvd.mp h1
      exact (show (a : ℤ) ^ 2 - (j : ℤ) ^ 2 = ((a : ℤ) - j) * (a + j) by ring) ▸
        Dvd.dvd.mul_right h2 _
    · have := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero h1)
      push_cast at this
      exact (show (a : ℤ) ^ 2 - (j : ℤ) ^ 2 = ((j : ℤ) + a) * (a - j) by ring) ▸
        Dvd.dvd.mul_right this _
  have := vge_int_of_dvd (p := p) _ 1 (by simpa using hd)
  push_cast at this
  simpa using this

theorem D_eval_vge {a j : ℕ} (ha1 : 1 ≤ a) (hj : j ∈ outerClassPoles K p a) :
    vge p ((D (Nof K)).eval (-(j : ℚ) ^ 2)) (if a ≤ Nof K then 1 else 0) := by
  split_ifs with haN
  · have hmem : a ∈ Icc 1 (Nof K) := mem_Icc.mpr ⟨ha1, haN⟩
    rw [D_eq_sqPoleProd, sqPoleProd, ← mul_prod_erase _ _ hmem, eval_mul, ← sqPoleProd]
    have h1 : vge p (eval (-(j : ℚ) ^ 2) (X + C ((a : ℚ) ^ 2))) 1 := by
      simpa [add_comm, sub_eq_add_neg] using sq_sub_vge hK h hj
    simpa using vge_mul h1 (eval_vge0 (vpGge_sqPoleProd _) (vge_neg_sq j))
  · exact eval_vge0 (vpGge_sqPoleProd _) (vge_neg_sq j)

theorem node_factor_le {a j k : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hj : j ∈ outerClassPoles K p a) (hk : k ∈ outerClassPoles K p a) (hjk : j ≠ k) :
    (padicValRat p ((k : ℚ) ^ 2 - (j : ℚ) ^ 2) : ℚ) ≤ 1 := by
  have hodd := OuterHyp.odd hK h
  obtain ⟨h7, h2, h3, h4, h5, h6⟩ := h
  have hKp : K < p ^ 2 := by omega
  have hjK : j ≤ K := ((mem_class hK ⟨h7, h2, h3, h4, h5, h6⟩).mp hj).2.1
  have hkK : k ≤ K := ((mem_class hK ⟨h7, h2, h3, h4, h5, h6⟩).mp hk).2.1
  have hkp := class_not_dvd hK ⟨h7, h2, h3, h4, h5, h6⟩ ha1 ha hk
  have e : (k : ℚ) ^ 2 - (j : ℚ) ^ 2 = (((k : ℤ) - j : ℤ) : ℚ) * (((k : ℤ) + j : ℤ) : ℚ) := by
    push_cast; ring
  have hm : ((k : ℤ) - j) ≠ 0 := by omega
  have hpl : ((k : ℤ) + j) ≠ 0 := by omega
  rw [e, padicValRat.mul (by exact_mod_cast hm) (by exact_mod_cast hpl)]
  have b1 := padicValRat_int_le_one (p := p) ((k : ℤ) - j) hm (by omega)
  have b2 := padicValRat_int_le_one (p := p) ((k : ℤ) + j) hpl (by omega)
  by_cases hd : (p : ℤ) ∣ (k : ℤ) - j
  · have hnd : ¬ (p : ℤ) ∣ (k : ℤ) + j := by
      intro hd2
      have h2k : (p : ℤ) ∣ 2 * k := by
        have := dvd_add hd hd2; rwa [show (k : ℤ) - j + (k + j) = 2 * k by ring] at this
      have hp2 : Nat.Prime p := hp.out
      rcases (Int.Prime.dvd_mul' hp2 h2k) with h2 | h2
      · have := Int.le_of_dvd (by norm_num) h2
        omega
      · exact hkp (Int.natCast_dvd_natCast.mp h2)
    rw [Int.cast_add, padicValRat_int_of_not_dvd _ hnd, Int.cast_zero]
    linarith
  · rw [Int.cast_add, padicValRat_int_of_not_dvd _ hd, Int.cast_zero]
    linarith

/-- The node derivative `∏_{k ≠ j} (k² - j²)` of a class loses at most `|C_a| - 1`. -/
theorem node_prod_le {a j : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hj : j ∈ outerClassPoles K p a) :
    ∏ k ∈ (outerClassPoles K p a).erase j, ((k : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 ∧
    (padicValRat p (∏ k ∈ (outerClassPoles K p a).erase j, ((k : ℚ) ^ 2 - (j : ℚ) ^ 2)) : ℚ) ≤
      ((outerClassPoles K p a).card : ℚ) - 1 := by
  have hne : ∀ k ∈ (outerClassPoles K p a).erase j, (k : ℚ) ^ 2 - (j : ℚ) ^ 2 ≠ 0 :=
    fun k hk => sq_ne_sq_of_ne (ne_of_mem_erase hk).symm
  refine ⟨prod_ne_zero_iff.mpr hne, ?_⟩
  rw [padicValRat_prod _ _ hne]
  push_cast
  calc ∑ k ∈ (outerClassPoles K p a).erase j, (padicValRat p ((k : ℚ) ^ 2 - (j : ℚ) ^ 2) : ℚ)
      ≤ ∑ k ∈ (outerClassPoles K p a).erase j, (1 : ℚ) :=
        sum_le_sum fun k hk => node_factor_le hK h ha1 ha hj (mem_of_mem_erase hk)
          (ne_of_mem_erase hk).symm
    _ = _ := by rw [sum_const, card_erase_of_mem hj, nsmul_eq_mul, mul_one,
        Nat.cast_sub (card_pos.mpr ⟨j, hj⟩)]; simp

/-- Pole values in a nonzero class have valuation `≥ -5`. -/
theorem muPole_vge_class {a j : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hj : j ∈ outerClassPoles K p a) : vpGge p (muPole j) (-5) := by
  have hp2 : p ≠ 2 := by have := h.1; omega
  have hjK : j ≤ K := ((mem_class hK h).mp hj).2.1
  have hlog := log_le_one_of_lt_sq (p := p) (by have := h.2.2.2.1; omega : K < p ^ 2)
  refine muPole_vge j (by norm_num) hp2 ?_ (vge_mono (vge_inv_two_mul
    (class_not_dvd hK h ha1 ha hj) hp2) (by norm_num))
  have hH := vge_H5 (p := p) K j hjK
  have := vge_mul (vge_pow0 (vge_natCast (p := p) j) 4) hH
  refine vge_mono this ?_
  have : (Nat.log p K : ℚ) ≤ 1 := by exact_mod_cast hlog
  linarith

/-- The class-`a` factor `δ`. -/
def dlt (K a : ℕ) : ℚ := if a ≤ Nof K then 1 else 0

/-- **(4.12), ordinary rows**: a same-class entry between rows `i, i' < ℓ - 2`. -/
theorem entry_ord {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) (i i' : ℕ) :
    vpGge p (muXmod p (outerClassPoles K p a)
      (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) *
        (X + C ((a : ℚ) ^ 2)) ^ i * (X + C ((a : ℚ) ^ 2)) ^ i'))
      (min 0 ((i : ℚ) + i' + 6 * dlt K a - ell p K a - 4)) := by
  have hp7 := h.1
  have hcard := card_outerClass hK h ha1 ha
  have hR : vpGge p (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) *
      (X + C ((a : ℚ) ^ 2)) ^ i * (X + C ((a : ℚ) ^ 2)) ^ i') 0 :=
    vpGge_mul0 (vpGge_mul0 (vpGge_mul0 (vpGge_pow0 (vpGge_sqPoleProd _) _) (vpGge_sqPoleProd _))
      (vpGge_pow0 (vpGge_X_add_C_natSq a) _)) (vpGge_pow0 (vpGge_X_add_C_natSq a) _)
  refine muXmod_vge_of_residues hp7 _ hR (min_le_left _ _) fun j hj => ?_
  obtain ⟨hden, hdenv⟩ := node_prod_le hK h ha1 ha hj
  have hnum : vge p ((D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) *
      (X + C ((a : ℚ) ^ 2)) ^ i * (X + C ((a : ℚ) ^ 2)) ^ i').eval (-(j : ℚ) ^ 2))
      (5 * dlt K a + i + i') := by
    simp only [eval_mul, eval_pow]
    have hD := vge_pow' (D_eval_vge hK h ha1 hj) 5
    have hP := eval_vge0 (vpGge_sqPoleProd (tailPoles K \ outerClassPoles K p a)) (vge_neg_sq (p := p) j)
    have hq : vge p (eval (-(j : ℚ) ^ 2) (X + C ((a : ℚ) ^ 2))) 1 := by
      simpa [add_comm, sub_eq_add_neg] using sq_sub_vge hK h hj
    have := vge_mul (vge_mul (vge_mul hD hP) (vge_pow' hq i)) (vge_pow' hq i')
    refine vge_mono this ?_
    unfold dlt; push_cast; ring_nf; rfl
  have hres := vge_div_of_le hnum hden hdenv
  refine vpGge_mono (vpGge_mul (vpGge_C hres) (muPole_vge_class hK h ha1 ha hj)) ?_
  refine (min_le_right _ _).trans (le_of_eq ?_)
  have hc : ((outerClassPoles K p a).card : ℚ) = ell p K a - dlt K a := by
    unfold dlt; split_ifs at hcard ⊢ <;> [skip; skip] <;> push_cast [← hcard] <;> ring
  rw [hc]
  ring

end ClassVal

/-- Pole values below `p` are integral. -/
theorem muPole_vge_small {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) (hp2 : p ≠ 2) :
    vpGge p (muPole j) 0 := by
  refine muPole_vge j le_rfl hp2 ?_ (vge_inv_two_mul (fun hd => by
    have := Nat.le_of_dvd (by omega) hd; omega) hp2)
  have hH := vge_H5 (p := p) (p - 1) j (by omega)
  rw [Nat.log_of_lt (by omega)] at hH
  simpa using vge_mul (vge_pow0 (vge_natCast (p := p) j) 4) hH

/-! ## The two small poles `a`, `p - a` -/

theorem vge_nat_of_dvd (n : ℕ) (hn : p ∣ n) : vge p (n : ℚ) 1 := by
  have := vge_int_of_dvd (p := p) (n : ℤ) 1 (by simpa using Int.natCast_dvd_natCast.mpr hn)
  simpa using this

theorem vge_inv_nat_unit {n : ℕ} (hn : ¬ p ∣ n) : vge p (1 / (n : ℚ)) 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  have := vge_inv_int (p := p) (n : ℤ) (by exact_mod_cast hn0) 0 (by
    simpa using fun h => hn (Int.natCast_dvd_natCast.mp h))
  simpa using this

/-- `∑_{v=a}^{p-a} v⁻⁵ ≡ 0 (mod p)`, by pairing `v ↔ p - v`. -/
theorem pair_sum_vge (hp2 : p ≠ 2) {a : ℕ} (ha1 : 1 ≤ a) (ha : 2 * a < p) :
    vge p (∑ v ∈ Icc a (p - a), 1 / ((v : ℚ) ^ 5)) 1 := by
  set S := ∑ v ∈ Icc a (p - a), 1 / ((v : ℚ) ^ 5)
  have hrefl : ∑ v ∈ Icc a (p - a), 1 / (((p - v : ℕ) : ℚ) ^ 5) = S := by
    refine Finset.sum_nbij' (fun v => p - v) (fun v => p - v) ?_ ?_ ?_ ?_ ?_
    · intro v hv; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hv ⊢; omega
    · intro v hv; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hv ⊢; omega
    · intro v hv; simp only [mem_coe, mem_Icc] at hv; omega
    · intro v hv; simp only [mem_coe, mem_Icc] at hv; omega
    · intro v _; rfl
  have h2S : 2 * S = ∑ v ∈ Icc a (p - a), (1 / ((v : ℚ) ^ 5) + 1 / (((p - v : ℕ) : ℚ) ^ 5)) := by
    rw [sum_add_distrib, hrefl]; ring
  have hterm : ∀ v ∈ Icc a (p - a),
      vge p (1 / ((v : ℚ) ^ 5) + 1 / (((p - v : ℕ) : ℚ) ^ 5)) 1 := by
    intro v hv
    rw [mem_Icc] at hv
    have hv1 : ¬ p ∣ v := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hv2 : ¬ p ∣ (p - v) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hw : 1 / ((v : ℚ) ^ 5) + 1 / (((p - v : ℕ) : ℚ) ^ 5) =
        (((p - v : ℕ) : ℚ) ^ 5 + (v : ℚ) ^ 5) * ((1 / (v : ℚ)) ^ 5 * (1 / ((p - v : ℕ) : ℚ)) ^ 5) := by
      have h1 : (v : ℚ) ≠ 0 := by exact_mod_cast (show v ≠ 0 by omega)
      have h2 : ((p - v : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show p - v ≠ 0 by omega)
      field_simp
    rw [hw]
    have hnum : vge p (((p - v : ℕ) : ℚ) ^ 5 + (v : ℚ) ^ 5) 1 := by
      have e : ((p - v : ℕ) : ℚ) ^ 5 + (v : ℚ) ^ 5 =
          ((p * (p ^ 4 - 5 * p ^ 3 * v + 10 * p ^ 2 * v ^ 2 - 10 * p * v ^ 3 + 5 * v ^ 4) : ℤ) : ℚ) := by
        push_cast [Nat.cast_sub (show v ≤ p by omega)]; ring
      rw [e]
      exact vge_int_of_dvd (p := p) _ 1 (by rw [pow_one]; exact dvd_mul_right _ _)
    simpa using vge_mul hnum (vge_mul (vge_pow0 (vge_inv_nat_unit hv1) 5)
      (vge_pow0 (vge_inv_nat_unit hv2) 5))
  have h2 : vge p (2 * S) 1 := h2S ▸ vge_sum _ _ hterm
  have hhalf : vge p (1 / 2 : ℚ) 0 := by
    have := vge_inv_nat_unit (p := p) (n := 2) (fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd; have := hp.out.two_le; omega)
    simpa using this
  have := vge_mul hhalf h2
  simpa [← mul_assoc] using this

/-- The constant term of `µ_X(1/(t + j²))`. -/
def c0 (j : ℕ) : ℚ := -((j : ℚ) ^ 4 * H5 j) - 1 / 4 + 1 / (2 * (j : ℚ))

theorem muPole_eq (j : ℕ) : muPole j = C ((j : ℚ) ^ 4) * X + C (c0 j) := by
  unfold muPole c0; simp only [map_sub, map_add, map_neg, map_mul, map_pow]; ring

theorem muPole_coeff (j n : ℕ) :
    (muPole j).coeff n = if n = 1 then (j : ℚ) ^ 4 else if n = 0 then c0 j else 0 := by
  rw [muPole_eq, coeff_add, coeff_C_mul_X, coeff_C]
  rcases n with _ | _ | n <;> simp

theorem H5_split {a b : ℕ} (ha1 : 1 ≤ a) (hab : a ≤ b) :
    H5 b = H5 (a - 1) + ∑ v ∈ Icc a b, 1 / ((v : ℚ) ^ 5) := by
  unfold H5
  have hU : Icc 1 b = Icc 1 (a - 1) ∪ Icc a b := by ext v; simp only [mem_Icc, mem_union]; omega
  have hD : Disjoint (Icc 1 (a - 1)) (Icc a b) := by
    rw [Finset.disjoint_left]; intro v h1 h2; simp only [mem_Icc] at h1 h2; omega
  rw [hU, sum_union hD]

theorem pole_congr (hp2 : p ≠ 2) {a : ℕ} (ha1 : 1 ≤ a) (ha : 2 * a < p) (n : ℕ) :
    vge p ((muPole a).coeff n - (muPole (p - a)).coeff n) 1 := by
  set b := p - a with hb
  have hab : a + b = p := by omega
  have hb' : (b : ℚ) = p - a := by rw [hb, Nat.cast_sub (by omega)]
  have hK1 : vge p ((a : ℚ) ^ 4 - (b : ℚ) ^ 4) 1 := by
    have e : (a : ℚ) ^ 4 - (b : ℚ) ^ 4 =
        ((p * (-(p : ℤ) ^ 3 + 4 * p ^ 2 * a - 6 * p * a ^ 2 + 4 * a ^ 3) : ℤ) : ℚ) := by
      rw [hb']; push_cast; ring
    rw [e]; exact vge_int_of_dvd (p := p) _ 1 (by rw [pow_one]; exact dvd_mul_right _ _)
  rw [muPole_coeff, muPole_coeff]
  split_ifs
  · exact hK1
  · -- the constant terms
    have hH := H5_split (a := a) (b := b) ha1 (by omega)
    have hHa : H5 a = H5 (a - 1) + 1 / ((a : ℚ) ^ 5) := by
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      rw [H5_succ]; simp
    set S := ∑ v ∈ Icc a b, 1 / ((v : ℚ) ^ 5)
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have e : c0 a - c0 b = ((b : ℚ) ^ 4 - (a : ℚ) ^ 4) * H5 (a - 1) + (b : ℚ) ^ 4 * S -
        (p : ℚ) * ((1 / (2 * (a : ℚ))) * (1 / (b : ℚ))) := by
      unfold c0
      rw [hH, hHa]
      have hp' : (p : ℚ) = a + b := by exact_mod_cast hab.symm
      rw [hp']
      field_simp
      ring
    rw [e]
    have hHint : vge p (H5 (a - 1)) 0 := by
      have := vge_H5 (p := p) (p - 1) (a - 1) (by omega)
      rwa [Nat.log_of_lt (by omega), Nat.cast_zero, mul_zero] at this
    have hbnd : ¬ p ∣ b := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hand : ¬ p ∣ a := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hK1' : vge p ((b : ℚ) ^ 4 - (a : ℚ) ^ 4) 1 := by
      have := vge_neg hK1; rwa [neg_sub] at this
    rw [sub_eq_add_neg]
    refine vge_add (p := p) (vge_add (p := p) ?_ ?_) (vge_neg (p := p) ?_)
    · simpa using vge_mul hK1' hHint
    · have h := vge_mul (vge_pow0 (vge_natCast (p := p) b) 4) (pair_sum_vge (p := p) hp2 ha1 ha)
      rw [zero_add] at h; exact h
    · simpa using vge_mul (vge_nat_of_dvd (p := p) p dvd_rfl)
        (vge_mul (vge_inv_two_mul hand hp2) (vge_inv_nat_unit hbnd))
  · simpa using vge_zero (p := p) 1

/-- The divided difference at the two nodes `a`, `p - a` is integral. -/
theorem two_pole_vge (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (ha : 2 * a < p) {R : ℚ[X]}
    (hR : vpGge p R 0) : vpGge p (muXmod p {a, p - a} R) 0 := by
  have hp2 : p ≠ 2 := by omega
  set b := p - a with hb
  have hab : a ≠ b := by omega
  rw [muXmod_def]
  refine vpGge_add (vpGge_C (muModPoly_vge hp7
    (divByMonic_vge hR (sqPoleProd_monic _) (vpGge_sqPoleProd _)))) ?_
  rw [sum_insert (by simpa using hab), sum_singleton]
  have e1 : ({a, b} : Finset ℕ).erase a = {b} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega
  have e2 : ({a, b} : Finset ℕ).erase b = {a} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega
  simp only [sqResidue, e1, e2, prod_singleton]
  set d : ℚ := (b : ℚ) ^ 2 - (a : ℚ) ^ 2
  have hd0 : d ≠ 0 := sq_ne_sq_of_ne hab
  have hdv : (padicValRat p d : ℚ) ≤ 1 := by
    have e : d = (((b : ℤ) ^ 2 - (a : ℤ) ^ 2 : ℤ) : ℚ) := by simp [d]
    rw [e]
    refine padicValRat_int_le_one _ (by rw [e] at hd0; exact_mod_cast hd0) ?_
    have hb1 : (b : ℤ) < p := by omega
    have hb2 : (a : ℤ) ≤ b := by omega
    have ha0 : (0 : ℤ) ≤ a := by omega
    have : (b : ℤ) ^ 2 - (a : ℤ) ^ 2 < (p : ℤ) ^ 2 := by nlinarith
    have : 0 ≤ (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by nlinarith
    zify; rw [abs_of_nonneg this]; omega
  intro n
  rw [coeff_add, coeff_C_mul, coeff_C_mul]
  have hx : vge p (R.eval (-(a : ℚ) ^ 2)) 0 := eval_vge0 hR (vge_neg_sq a)
  have hxy : vge p (R.eval (-(a : ℚ) ^ 2) - R.eval (-(b : ℚ) ^ 2)) 1 := by
    refine eval_sub_vge hR (vge_neg_sq a) (vge_neg_sq b) ?_
    have e : -(a : ℚ) ^ 2 - -(b : ℚ) ^ 2 = (((b - a) * p : ℤ) : ℚ) := by
      rw [hb]; push_cast [Nat.cast_sub (show a ≤ p by omega)]; ring
    rw [e]; exact vge_int_of_dvd (p := p) _ 1 (by rw [pow_one]; exact dvd_mul_left _ _)
  have hya : vge p ((muPole a).coeff n) 0 := muPole_vge_small ha1 (by omega) hp2 n
  have hyb : vge p ((muPole b).coeff n) 0 := muPole_vge_small (by omega) (by omega) hp2 n
  have hyy := pole_congr hp2 ha1 ha n
  have hnum : vge p (R.eval (-(a : ℚ) ^ 2) * (muPole a).coeff n -
      R.eval (-(b : ℚ) ^ 2) * (muPole b).coeff n) 1 := by
    have e : R.eval (-(a : ℚ) ^ 2) * (muPole a).coeff n - R.eval (-(b : ℚ) ^ 2) * (muPole b).coeff n =
        R.eval (-(a : ℚ) ^ 2) * ((muPole a).coeff n - (muPole b).coeff n) +
          (R.eval (-(a : ℚ) ^ 2) - R.eval (-(b : ℚ) ^ 2)) * (muPole b).coeff n := by ring
    rw [e]
    exact vge_add (by simpa using vge_mul hx hyy) (by simpa using vge_mul hxy hyb)
  have e : R.eval (-(a : ℚ) ^ 2) / d * (muPole a).coeff n +
      R.eval (-(b : ℚ) ^ 2) / ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) * (muPole b).coeff n =
      (R.eval (-(a : ℚ) ^ 2) * (muPole a).coeff n - R.eval (-(b : ℚ) ^ 2) * (muPole b).coeff n) / d := by
    have : (a : ℚ) ^ 2 - (b : ℚ) ^ 2 = -d := by simp [d]
    rw [this]; field_simp; ring
  rw [e]
  exact vge_mono (vge_div_of_le hnum hd0 hdv) (by norm_num)

section Large

variable {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p)
include hK h

theorem small_poles {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    (outerClassPoles K p a).filter (fun j => j < p) =
      if a ≤ Nof K then {p - a} else {a, p - a} := by
  have hodd := OuterHyp.odd hK h
  ext j
  simp only [mem_filter]
  constructor
  · rintro ⟨hj, hjp⟩
    rcases class_small hK h ha1 ha hj hjp with rfl | rfl
    · have := (a_mem_iff hK h ha1 ha).mp hj
      split_ifs with haN
      · omega
      · simp
    · split_ifs <;> simp
  · intro hj
    split_ifs at hj with haN
    · rw [mem_singleton] at hj; subst hj
      exact ⟨pa_mem hK h ha1 ha, by omega⟩
    · simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact ⟨(a_mem_iff hK h ha1 ha).mpr (by omega), by omega⟩
      · exact ⟨pa_mem hK h ha1 ha, by omega⟩

/-- **(4.12), rows `i ≥ ℓ - 2`**: once `E_a` is a factor, the entry is integral. -/
theorem entry_large {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) {R : ℚ[X]} (hR : vpGge p R 0) :
    vpGge p (muXmod p (outerClassPoles K p a)
      (R * sqPoleProd ((outerClassPoles K p a).filter fun j => p < j))) 0 := by
  have hodd := OuterHyp.odd hK h
  have hp7 := h.1
  set Ca := outerClassPoles K p a
  have hsplit : Ca.filter (fun j => p < j) ∪ Ca.filter (fun j => j < p) = Ca := by
    ext j; simp only [mem_union, mem_filter]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
    · intro hj
      have : j ≠ p := fun e => class_not_dvd hK h ha1 ha hj (e ▸ dvd_rfl)
      rcases lt_or_gt_of_ne this with h1 | h1
      · exact Or.inr ⟨hj, h1⟩
      · exact Or.inl ⟨hj, h1⟩
  have hdisj : Disjoint (Ca.filter fun j => p < j) (Ca.filter fun j => j < p) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_filter] at h1 h2; omega
  have hc := muXmod_mul_cancel_set (p := p) _ _ hdisj R
  rw [hsplit] at hc
  rw [hc, small_poles hK h ha1 ha]
  split_ifs with haN
  · refine muXmod_vge_of_residues hp7 _ hR le_rfl fun j hj => ?_
    rw [mem_singleton] at hj; subst hj
    have hres : sqResidue {p - a} R (p - a) = R.eval (-((p - a : ℕ) : ℚ) ^ 2) := by
      simp [sqResidue]
    rw [hres]
    simpa using vpGge_mul (vpGge_C (eval_vge0 hR (vge_neg_sq (p - a))))
      (muPole_vge_small (by omega) (by omega) (by omega))
  · exact two_pole_vge hp7 ha1 (by omega) hR

end Large

/-! ## The zero class -/

theorem muPole_vge_mult {t : ℕ} (ht : 1 ≤ t) (ht2 : t ≤ 2) (hp7 : 7 ≤ p) :
    vpGge p (muPole (t * p)) (-1) := by
  have hp2 : p ≠ 2 := by omega
  refine muPole_vge _ (by norm_num) hp2 ?_ ?_
  · have h4 : vge p (((t * p : ℕ) : ℚ) ^ 4) 4 := by
      have := vge_int_of_dvd (p := p) (((t * p : ℕ) : ℤ) ^ 4) 4
        (pow_dvd_pow_of_dvd (by push_cast; exact dvd_mul_left _ _) 4)
      simpa using this
    have hlog : Nat.log p (t * p) ≤ 1 := log_le_one_of_lt_sq (by nlinarith)
    have hH := vge_H5 (p := p) (t * p) (t * p) le_rfl
    have hlog' : (Nat.log p (t * p) : ℚ) ≤ 1 := by exact_mod_cast hlog
    exact vge_mono (vge_mul h4 hH) (by linarith)
  · have := vge_inv_int (p := p) (2 * (t * p : ℕ) : ℤ) (by positivity) 1 (by
      intro hd
      have h1 := Int.le_of_dvd (by positivity) hd
      push_cast at h1
      nlinarith)
    simpa using this

theorem padicValRat_three_sq (hp7 : 7 ≤ p) : (padicValRat p (3 * (p : ℚ) ^ 2) : ℚ) ≤ 2 := by
  have h3 : ¬ p ∣ 3 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpp2 : padicValRat p ((p : ℚ) ^ 2) = 2 := by
    rw [padicValRat.pow, padicValRat.self hp.out.one_lt]; norm_num
  rw [padicValRat.mul (by norm_num) (pow_ne_zero 2 hp0), hpp2]
  have h3' : padicValRat p (3 : ℚ) = 0 := by
    have : padicValRat p ((3 : ℕ) : ℚ) = padicValNat p 3 := padicValRat.of_nat
    rw [show ((3 : ℕ) : ℚ) = 3 by norm_num] at this
    rw [this, padicValNat.eq_zero_of_not_dvd h3]; rfl
  rw [h3']
  norm_num

section Zero

variable {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p)
include hK h

/-- The zero class with a single pole `p`. -/
theorem entry_zero_one (hK2 : K < 2 * p) {R : ℚ[X]} (hR : vpGge p R 0) :
    vpGge p (muXmod p (outerClassPoles K p 0) R) (-1) := by
  have hp7 := h.1
  rw [zero_class hK h, if_neg (by omega)]
  refine muXmod_vge_of_residues hp7 _ hR (by norm_num) fun j hj => ?_
  rw [mem_singleton] at hj
  rw [hj]
  have hres : sqResidue {p} R p = R.eval (-((p : ℕ) : ℚ) ^ 2) := by simp [sqResidue]
  rw [hres]
  simpa using vpGge_mul (vpGge_C (eval_vge0 hR (vge_neg_sq p)))
    (by simpa using muPole_vge_mult (p := p) (t := 1) le_rfl (by norm_num) hp7)

/-- The zero class with two poles `p, 2p`. -/
theorem entry_zero_two (hK2 : 2 * p ≤ K) (A : ℚ[X]) (hA : vpGge p A 0) (i i' : ℕ) :
    vpGge p (muXmod p (outerClassPoles K p 0)
      (A * (X + C ((p : ℚ) ^ 2)) ^ i * (X + C ((p : ℚ) ^ 2)) ^ i'))
      (min 0 (2 * ((i : ℚ) + i') - 3)) := by
  have hp7 := h.1
  rw [zero_class hK h, if_pos hK2]
  set R := A * (X + C ((p : ℚ) ^ 2)) ^ i * (X + C ((p : ℚ) ^ 2)) ^ i'
  have hR : vpGge p R 0 :=
    vpGge_mul0 (vpGge_mul0 hA (vpGge_pow0 (vpGge_X_add_C_natSq p) _))
      (vpGge_pow0 (vpGge_X_add_C_natSq p) _)
  refine muXmod_vge_of_residues hp7 _ hR (min_le_left _ _) fun j hj => ?_
  have hpp : p ≠ 2 * p := by omega
  have hRv : ∀ t : ℕ, 1 ≤ t → t ≤ 2 → vge p (R.eval (-((t * p : ℕ) : ℚ) ^ 2)) (2 * ((i : ℚ) + i')) := by
    intro t ht1 ht2
    have hq : vge p (eval (-((t * p : ℕ) : ℚ) ^ 2) (X + C ((p : ℚ) ^ 2))) 2 := by
      have e : eval (-((t * p : ℕ) : ℚ) ^ 2) (X + C ((p : ℚ) ^ 2)) =
          ((-((t : ℤ) ^ 2 - 1) * (p : ℤ) ^ 2 : ℤ) : ℚ) := by simp; push_cast; ring
      rw [e]; exact vge_int_of_dvd (p := p) _ 2 (dvd_mul_left _ _)
    have := vge_mul (vge_mul (eval_vge0 hA (vge_neg_sq (t * p))) (vge_pow' hq i)) (vge_pow' hq i')
    simp only [R, eval_mul, eval_pow]
    exact vge_mono this (by ring_nf; rfl)
  have hden : ∀ t s : ℕ, (t = 1 ∧ s = 2 ∨ t = 2 ∧ s = 1) →
      ((s * p : ℕ) : ℚ) ^ 2 - ((t * p : ℕ) : ℚ) ^ 2 ≠ 0 ∧
      (padicValRat p (((s * p : ℕ) : ℚ) ^ 2 - ((t * p : ℕ) : ℚ) ^ 2) : ℚ) ≤ 2 := by
    rintro t s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have e : ((2 * p : ℕ) : ℚ) ^ 2 - ((1 * p : ℕ) : ℚ) ^ 2 = 3 * (p : ℚ) ^ 2 := by push_cast; ring
      rw [e]; exact ⟨by positivity, padicValRat_three_sq hp7⟩
    · have e : ((1 * p : ℕ) : ℚ) ^ 2 - ((2 * p : ℕ) : ℚ) ^ 2 = -(3 * (p : ℚ) ^ 2) := by push_cast; ring
      rw [e, padicValRat.neg]
      refine ⟨?_, padicValRat_three_sq hp7⟩
      have : (0 : ℚ) < 3 * p ^ 2 := by positivity
      linarith
  simp only [mem_insert, mem_singleton] at hj
  rcases hj with hj | hj <;> rw [hj]
  · have e1 : ({p, 2 * p} : Finset ℕ).erase p = {2 * p} := by
      ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega
    obtain ⟨hd0, hdv⟩ := hden 1 2 (Or.inl ⟨rfl, rfl⟩)
    simp only [one_mul] at hd0 hdv
    rw [sqResidue, e1, prod_singleton]
    have := vge_div_of_le (by simpa using hRv 1 le_rfl (by norm_num)) hd0 hdv
    have hmu := muPole_vge_mult (p := p) (t := 1) le_rfl (by norm_num) hp7
    rw [one_mul] at hmu
    refine vpGge_mono (vpGge_mul (vpGge_C this) hmu) ?_
    refine (min_le_right _ _).trans (le_of_eq (by ring))
  · have e2 : ({p, 2 * p} : Finset ℕ).erase (2 * p) = {p} := by
      ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega
    obtain ⟨hd0, hdv⟩ := hden 2 1 (Or.inr ⟨rfl, rfl⟩)
    simp only [one_mul] at hd0 hdv
    rw [sqResidue, e2, prod_singleton]
    have := vge_div_of_le (hRv 2 (by norm_num) le_rfl) hd0 hdv
    refine vpGge_mono (vpGge_mul (vpGge_C this) (muPole_vge_mult (p := p) (t := 2)
      (by norm_num) le_rfl hp7)) ?_
    refine (min_le_right _ _).trans (le_of_eq (by ring))

end Zero

/-! ## The entry bound (4.12) -/

theorem wOut_nonpos (K p : ℕ) (x : OuterIdx K p) : wOut K p x ≤ 0 := by
  simp only [wOut]
  split_ifs <;> first | norm_num | exact min_le_left _ _

theorem min_add_le_min (A B : ℚ) : min 0 A + min 0 B ≤ min 0 (A + B) := by
  rw [le_min_iff]; constructor
  · linarith [min_le_left (0 : ℚ) A, min_le_left (0 : ℚ) B]
  · linarith [min_le_right (0 : ℚ) A, min_le_right (0 : ℚ) B]

theorem outerGram_apply (K p : ℕ) (x y : OuterIdx K p) :
    outerGram K p x y = muXmod p (Icc 1 K)
      (D (Nof K) ^ 6 * outerBasis K p x * outerBasis K p y) := rfl

/-- **(4.12)** and the zero-class weights: the entries of `A` in the outer basis satisfy the
row weights. -/
theorem outerGram_entry_bound' {K : ℕ} (hK : 40 ∣ K) (h : OuterHyp K p) (x y : OuterIdx K p) :
    vpGge p (outerGram K p x y) (wOut K p x + wOut K p y) := by
  have hp7 := h.1
  have hwx := wOut_nonpos K p x
  have hwy := wOut_nonpos K p y
  have hw0 : wOut K p x + wOut K p y ≤ 0 := by linarith
  rw [outerGram_apply, outerBasis_eq, outerBasis_eq]
  by_cases hac : x.1 = y.1
  swap
  · -- cross-class
    have hdisj := class_disjoint hK h (Nat.lt_succ_iff.mp x.1.2) (Nat.lt_succ_iff.mp y.1.2)
      (fun e => hac (Fin.ext e))
    rw [cross_class_cancel (p := p) K _ _ hdisj]
    refine vpGge_mono (vpGge_C (muModPoly_vge hp7 ?_)) hw0
    exact vpGge_mul0 (vpGge_mul0 (vpGge_mul0 (vpGge_pow0 (vpGge_sqPoleProd _) _)
      (vpGge_sqPoleProd _)) (oq_vge K p x)) (oq_vge K p y)
  -- same class
  have hyx : (y.1 : ℕ) = x.1 := congrArg Fin.val hac.symm
  rw [hyx, same_class_cancel (p := p) K _ (class_subset_tail K p _)]
  have hint0 : vpGge p (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p x.1)) 0 :=
    vpGge_mul0 (vpGge_pow0 (vpGge_sqPoleProd _) _) (vpGge_sqPoleProd _)
  have hxi : (x.2 : ℕ) < outerCount K p x.1 := x.2.2
  have hyi : (y.2 : ℕ) < outerCount K p x.1 :=
    lt_of_lt_of_eq y.2.2 (by rw [hyx])
  by_cases ha0 : (x.1 : ℕ) = 0
  · -- the zero class
    have hoqx : oq K p x = (X + C ((p : ℚ) ^ 2)) ^ (x.2 : ℕ) := by simp [oq, ha0]
    have hoqy : oq K p y = (X + C ((p : ℚ) ^ 2)) ^ (y.2 : ℕ) := by simp [oq, hyx, ha0]
    have hC0 : outerClassPoles K p x.1 = outerClassPoles K p 0 := by rw [ha0]
    have hN0 : outerCount K p x.1 = outerCount K p 0 := by rw [ha0]
    rw [hoqx, hoqy, hC0]
    rw [hC0] at hint0
    have hcnt : outerCount K p 0 = if 2 * p ≤ K then 2 else 1 := by
      unfold outerCount; rw [zero_class hK h]
      split_ifs
      · rw [card_insert_of_notMem (by simp; have := h.1; omega), card_singleton]
      · exact card_singleton p
    by_cases hK2 : 2 * p ≤ K
    · have hxi2 : (x.2 : ℕ) < 2 := lt_of_lt_of_eq hxi (by rw [hN0, hcnt, if_pos hK2])
      have hyi2 : (y.2 : ℕ) < 2 := lt_of_lt_of_eq hyi (by rw [hN0, hcnt, if_pos hK2])
      have hwx' : wOut K p x = if (x.2 : ℕ) = 0 then -2 else 0 := by
        simp [wOut, ha0, hcnt, hK2]
      have hwy' : wOut K p y = if (y.2 : ℕ) = 0 then -2 else 0 := by
        simp [wOut, hyx, ha0, hcnt, hK2]
      refine vpGge_mono (entry_zero_two hK h hK2 _ hint0 _ _) ?_
      rw [hwx', hwy']
      interval_cases (x.2 : ℕ) <;> interval_cases (y.2 : ℕ) <;> norm_num
    · have hxi2 : (x.2 : ℕ) < 1 := lt_of_lt_of_eq hxi (by rw [hN0, hcnt, if_neg hK2])
      have hyi2 : (y.2 : ℕ) < 1 := lt_of_lt_of_eq hyi (by rw [hN0, hcnt, if_neg hK2])
      have hwx' : wOut K p x = -1 / 2 := by simp [wOut, ha0, hcnt, hK2]
      have hwy' : wOut K p y = -1 / 2 := by simp [wOut, hyx, ha0, hcnt, hK2]
      refine vpGge_mono (entry_zero_one hK h (by omega) (vpGge_mul0 (vpGge_mul0 hint0
        (vpGge_pow0 (vpGge_X_add_C_natSq p) _)) (vpGge_pow0 (vpGge_X_add_C_natSq p) _))) ?_
      rw [hwx', hwy']; norm_num
  · -- an ordinary class
    have ha1 : 1 ≤ (x.1 : ℕ) := Nat.one_le_iff_ne_zero.mpr ha0
    have ha : (x.1 : ℕ) ≤ mHalf p := Nat.lt_succ_iff.mp x.1.2
    set a : ℕ := (x.1 : ℕ) with ha_def
    have ha0y : ¬ (y.1 : ℕ) = 0 := by rw [hyx]; exact ha0
    by_cases hi : (x.2 : ℕ) < ell p K a - 2
    · have hi'y : (y.2 : ℕ) < ell p K (y.1 : ℕ) - 2 ↔ (y.2 : ℕ) < ell p K a - 2 := by
        rw [← hyx]
      by_cases hi' : (y.2 : ℕ) < ell p K a - 2
      · have hoqx : oq K p x = (X + C ((a : ℚ) ^ 2)) ^ (x.2 : ℕ) := by
          unfold oq; rw [if_neg ha0, if_pos hi]
        have hoqy : oq K p y = (X + C ((a : ℚ) ^ 2)) ^ (y.2 : ℕ) := by
          unfold oq; rw [if_neg ha0y, if_pos (hi'y.mpr hi')]; simp only [hyx]
        rw [hoqx, hoqy]
        refine vpGge_mono (entry_ord hK h ha1 ha _ _) ?_
        have hwx' : wOut K p x = min 0 (((x.2 : ℕ) : ℚ) + 3 * dlt K a - ((ell p K a : ℚ) + 4) / 2) := by
          simp only [wOut, dlt]; rw [if_neg ha0, if_pos hi]
        have hwy' : wOut K p y = min 0 (((y.2 : ℕ) : ℚ) + 3 * dlt K a - ((ell p K a : ℚ) + 4) / 2) := by
          simp only [wOut, dlt]; rw [if_neg ha0y, if_pos (hi'y.mpr hi')]; simp only [hyx]
        rw [hwx', hwy']
        refine (min_add_le_min _ _).trans (le_of_eq ?_)
        congr 1; ring
      · -- row `y` has the factor `E_a`
        have hoqy : oq K p y = sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) *
            (X + C ((a : ℚ) ^ 2)) ^ ((y.2 : ℕ) - (ell p K a - 2)) := by
          unfold oq; rw [if_neg ha0y, if_neg (fun hh => hi' (hi'y.mp hh))]; simp only [hyx]
        rw [hoqy, show D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) * oq K p x *
            (sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) *
              (X + C ((a : ℚ) ^ 2)) ^ ((y.2 : ℕ) - (ell p K a - 2))) =
            (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) * oq K p x *
              (X + C ((a : ℚ) ^ 2)) ^ ((y.2 : ℕ) - (ell p K a - 2))) *
            sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) by ring]
        exact vpGge_mono (entry_large hK h ha1 ha (vpGge_mul0 (vpGge_mul0 hint0 (oq_vge K p x))
          (vpGge_pow0 (vpGge_X_add_C_natSq a) _))) hw0
    · -- row `x` has the factor `E_a`
      have hoqx : oq K p x = sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) *
          (X + C ((a : ℚ) ^ 2)) ^ ((x.2 : ℕ) - (ell p K a - 2)) := by
        unfold oq; rw [if_neg ha0, if_neg hi]
      rw [hoqx, show D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) *
          (sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) *
            (X + C ((a : ℚ) ^ 2)) ^ ((x.2 : ℕ) - (ell p K a - 2))) * oq K p y =
          (D (Nof K) ^ 5 * sqPoleProd (tailPoles K \ outerClassPoles K p a) *
            (X + C ((a : ℚ) ^ 2)) ^ ((x.2 : ℕ) - (ell p K a - 2)) * oq K p y) *
          sqPoleProd ((outerClassPoles K p a).filter fun j => p < j) by ring]
      exact vpGge_mono (entry_large hK h ha1 ha (vpGge_mul0 (vpGge_mul0 hint0
        (vpGge_pow0 (vpGge_X_add_C_natSq a) _)) (oq_vge K p y))) hw0

end Zeta5