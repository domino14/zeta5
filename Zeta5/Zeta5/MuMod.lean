import Zeta5.Functionals
import Zeta5.Valuation

/-!
# `p`-adic valuations of the moments, and the decomposition (4.10)

* `muMono_padicVal'`: `v_p(µ(tᵉ)) ≥ -1`, and `µ(tᵉ)` is `p`-integral for `e < 2p - 3` (`p ≥ 7`).
* `kappa_padicVal_ge'`, `kappa_integral'`: the §3.1 facts about `κ_d`. The bound `v_p(κ_d) ≥ -1`
  **fails for `p = 2`**: `κ₃ = 1/4` (`kappa_three`). It holds for every odd prime.
* `muMod_vge`: the modified moments `µ(tᵉ) - c_e/p` are `p`-integral.
* `decomp_4_10'`: `G_K = A + p⁻¹L` with `L` constant, integral, of rank `≤ r_p`.
-/

open Polynomial Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Elementary valuation facts -/

theorem mm_vge_int (z : ℤ) : vge p (z : ℚ) 0 := by
  intro _
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

theorem mm_vge_nat (n : ℕ) : vge p (n : ℚ) 0 := by
  have := mm_vge_int (p := p) n; simpa using this

theorem mm_vge_nat_dvd {n : ℕ} (h : p ∣ n) : vge p (n : ℚ) 1 := by
  intro hn
  have hn0 : n ≠ 0 := by exact_mod_cast hn
  rw [padicValRat.of_nat]
  exact_mod_cast one_le_padicValNat_of_dvd hn0 h

/-- `v_p(1/n) ≥ -v_p(n)` in the form: if `p^(b+1) ∤ n` then `v_p(1/n) ≥ -b`. -/
theorem mm_vge_inv_nat {n : ℕ} (hn : n ≠ 0) (b : ℕ) (h : ¬ p ^ (b + 1) ∣ n) :
    vge p ((n : ℚ)⁻¹) (-(b : ℚ)) := by
  intro _
  rw [padicValRat.inv]
  have h1 : padicValNat p n ≤ b := by
    by_contra hc
    exact h ((padicValNat_dvd_iff_le hn).mpr (by omega))
  have h3 : (padicValRat p (n : ℚ) : ℚ) ≤ b := by
    rw [padicValRat.of_nat]; exact_mod_cast h1
  push_cast
  linarith

theorem mm_vge_inv_prime {q : ℕ} (hq : q.Prime) : vge p ((q : ℚ)⁻¹) (-1) := by
  have h := mm_vge_inv_nat (p := p) hq.ne_zero 1 (by
    intro hd
    have hpq : p ∣ q := (dvd_pow_self p (by norm_num)).trans hd
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp.out hq).mp hpq
    subst this
    have h2 : p ^ 2 ≤ p := Nat.le_of_dvd hq.pos (by simpa using hd)
    nlinarith [hq.two_le])
  simpa using h

theorem mm_vge_inv_prime_ne {q : ℕ} (hq : q.Prime) (hne : q ≠ p) : vge p ((q : ℚ)⁻¹) 0 := by
  have h := mm_vge_inv_nat (p := p) hq.ne_zero 0 (by
    intro hd
    simp only [zero_add, pow_one] at hd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp hd).symm)
  simpa using h

/-- `24` is a `p`-adic unit for `p ≥ 5`. -/
theorem mm_vge_inv24 (h5 : 5 ≤ p) : vge p ((24 : ℚ)⁻¹) 0 := by
  have h := mm_vge_inv_nat (p := p) (n := 24) (by norm_num) 0 (by
    intro hd
    simp only [zero_add, pow_one] at hd
    have : p ∣ 2 ^ 3 * 3 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp.out).mp this with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega)
  simpa using h

/-! ## Bernoulli numbers (von Staudt–Clausen) -/

theorem bern_even (k : ℕ) :
    vge p (_root_.bernoulli (2 * k)) (-1) ∧
      (¬ (p - 1) ∣ 2 * k → vge p (_root_.bernoulli (2 * k)) 0) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  set S := (range (2 * k + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * k
  have hB : _root_.bernoulli (2 * k) = z - ∑ q ∈ S, (1 : ℚ) / q := by rw [hz]; ring
  constructor
  · rw [hB, sub_eq_add_neg]
    refine vge_add (vge_mono (mm_vge_int z) (by norm_num)) (vge_neg (vge_sum _ _ fun q hq => ?_))
    rw [one_div]; exact mm_vge_inv_prime (mem_filter.mp hq).2.1
  · intro hpk
    rw [hB, sub_eq_add_neg]
    refine vge_add (mm_vge_int z) (vge_neg (vge_sum _ _ fun q hq => ?_))
    rw [one_div]
    refine mm_vge_inv_prime_ne (mem_filter.mp hq).2.1 fun hqp => ?_
    exact hpk (hqp ▸ (mem_filter.mp hq).2.2)

theorem bern_vge (n : ℕ) : vge p (_root_.bernoulli n) (-1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · rw [← two_mul]; exact (bern_even k).1
  · rcases Nat.lt_or_ge 1 n with hlt | hle
    · rw [bernoulli_eq_zero_of_odd hodd hlt]; exact vge_zero _
    · obtain rfl : n = 1 := by obtain ⟨m, rfl⟩ := hodd; omega
      rw [_root_.bernoulli_one, show (-1 / 2 : ℚ) = -((2 : ℕ) : ℚ)⁻¹ by norm_num]
      exact vge_neg (mm_vge_inv_prime Nat.prime_two)

/-- `B_n` is `p`-integral unless `p - 1 ∣ n` with `n > 0` (for odd `p`). -/
theorem bern_int (hp3 : 3 ≤ p) (n : ℕ) (h : n = 0 ∨ ¬ (p - 1) ∣ n) :
    vge p (_root_.bernoulli n) 0 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · rw [← two_mul] at h ⊢
    rcases h with h | h
    · obtain rfl : k = 0 := by omega
      simpa using vge_one (p := p)
    · exact (bern_even k).2 h
  · rcases Nat.lt_or_ge 1 n with hlt | hle
    · rw [bernoulli_eq_zero_of_odd hodd hlt]; exact vge_zero _
    · obtain rfl : n = 1 := by obtain ⟨m, rfl⟩ := hodd; omega
      rw [_root_.bernoulli_one, show (-1 / 2 : ℚ) = -((2 : ℕ) : ℚ)⁻¹ by norm_num]
      exact vge_neg (mm_vge_inv_prime_ne Nat.prime_two (by omega))

/-! ## The moments `µ(tᵉ)` -/

theorem muMono_eq (e : ℕ) : muMono e = (-1 : ℚ) ^ e * _root_.bernoulli (2 * e + 2) *
    (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) * (24 : ℚ)⁻¹ := by
  unfold muMono; push_cast; ring

theorem mm_vge_negone_pow (e : ℕ) : vge p ((-1 : ℚ) ^ e) 0 := by
  have := mm_vge_int (p := p) ((-1) ^ e); simpa using this

theorem muMono_vge (hp7 : 7 ≤ p) (e : ℕ) :
    vge p (muMono e) (-1) ∧ (e < 2 * p - 3 → vge p (muMono e) 0) := by
  rw [muMono_eq]
  have h24 := mm_vge_inv24 (p := p) (by omega)
  constructor
  · have := vge_mul (vge_mul (vge_mul (mm_vge_negone_pow (p := p) e) (bern_vge (2 * e + 2)))
      (mm_vge_nat ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)))) h24
    exact vge_mono this (by norm_num)
  · intro he
    by_cases hdiv : (p - 1) ∣ 2 * e + 2
    · have hP : p ∣ (2 * e + 3) * (2 * e + 4) * (2 * e + 5) := by
        obtain ⟨m, hm⟩ := hdiv
        have hm4 : m < 4 := by
          by_contra hc
          push Not at hc
          have h1 : (p - 1) * 4 ≤ (p - 1) * m := Nat.mul_le_mul_left _ hc
          rw [← hm] at h1
          omega
        interval_cases m
        · omega
        · have h2 : 2 * e + 3 = p := by omega
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (h2 ▸ dvd_refl _) _) _
        · have h2 : 2 * e + 4 = 2 * p := by omega
          rw [h2]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_left p 2) _) _
        · have h2 : 2 * e + 5 = 3 * p := by omega
          rw [h2]
          exact Dvd.dvd.mul_left (dvd_mul_left p 3) _
      have := vge_mul (vge_mul (vge_mul (mm_vge_negone_pow (p := p) e) (bern_vge (2 * e + 2)))
        (mm_vge_nat_dvd hP)) h24
      exact vge_mono this (by norm_num)
    · have := vge_mul (vge_mul (vge_mul (mm_vge_negone_pow (p := p) e)
        (bern_int (by omega) (2 * e + 2) (Or.inr hdiv)))
        (mm_vge_nat ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)))) h24
      exact vge_mono this (by norm_num)

/-- §4.2: `v_p(µ(tᵉ)) ≥ -1`, and `µ(tᵉ)` is `p`-integral for `e < 2p - 3`. -/
theorem muMono_padicVal' (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (e : ℕ) (he : muMono e ≠ 0) :
    -1 ≤ padicValRat p (muMono e) ∧ (e < 2 * p - 3 → 0 ≤ padicValRat p (muMono e)) := by
  obtain ⟨h1, h2⟩ := muMono_vge (p := p) hp e
  refine ⟨by exact_mod_cast h1 he, fun hlt => by exact_mod_cast h2 hlt he⟩

/-! ## `κ_d` -/

theorem kappa_eq (m : ℕ) : kappa (m + 3) =
    (((m + 3).descFactorial 3 : ℕ) : ℚ) * _root_.bernoulli m * (24 : ℚ)⁻¹ := by
  unfold kappa
  simp only [Nat.descFactorial, Nat.add_sub_cancel]
  push_cast
  ring

theorem kappa_of_lt {d : ℕ} (hd : d < 3) : kappa d = 0 := by
  interval_cases d <;> simp [kappa]

/-- The bound `v_p(κ_d) ≥ -1` fails at `p = 2`: `κ₃ = 1/4`. -/
theorem kappa_three : kappa 3 = 1 / 4 := by
  rw [show 3 = 0 + 3 from rfl, kappa_eq]; simp [Nat.descFactorial]; norm_num

theorem padicValRat_two_kappa_three : padicValRat 2 (kappa 3) = -2 := by
  rw [kappa_three, show (1 / 4 : ℚ) = ((2 ^ 2 : ℕ) : ℚ)⁻¹ by norm_num, padicValRat.inv,
    padicValRat.of_nat, padicValNat.prime_pow]
  norm_num

/-- §3.1: `v_p(κ_d) ≥ -1` for every **odd** prime `p` (false for `p = 2`, see `kappa_three`). -/
theorem kappa_padicVal_ge' (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (d : ℕ) (hd : kappa d ≠ 0) :
    -1 ≤ padicValRat p (kappa d) := by
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · exact absurd (kappa_of_lt hlt) hd
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  have hv : vge p (kappa (m + 3)) (-1) := by
    rw [kappa_eq]
    have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
    rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with rfl | rfl | h5
    · have h6 : 3 ∣ (m + 3).descFactorial 3 :=
        (show 3 ∣ Nat.factorial 3 by decide).trans (Nat.factorial_dvd_descFactorial _ _)
      have h24 : vge 3 ((24 : ℚ)⁻¹) (-1) := by
        have := mm_vge_inv_nat (p := 3) (n := 24) (by norm_num) 1 (by decide)
        simpa using this
      have := vge_mul (vge_mul (mm_vge_nat_dvd (p := 3) h6) (bern_vge m)) h24
      exact vge_mono this (by norm_num)
    · exact absurd (Fact.out : Nat.Prime 4) (by decide)
    · have := vge_mul (vge_mul (mm_vge_nat (p := p) ((m + 3).descFactorial 3)) (bern_vge m))
        (mm_vge_inv24 h5)
      exact vge_mono this (by norm_num)
  exact_mod_cast hv hd

/-- §3.1: `κ_d ∈ ℤ_p` for `d ≤ p + 1` (with `p ≥ 7`). -/
theorem kappa_integral' (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (d : ℕ) (hd : d ≤ p + 1)
    (hk : kappa d ≠ 0) : 0 ≤ padicValRat p (kappa d) := by
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · exact absurd (kappa_of_lt hlt) hk
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  have hB : vge p (_root_.bernoulli m) 0 := by
    refine bern_int (by omega) m ?_
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr fun hdvd => ?_
      have := Nat.le_of_dvd hpos hdvd
      omega
  have hv : vge p (kappa (m + 3)) 0 := by
    rw [kappa_eq]
    have := vge_mul (vge_mul (mm_vge_nat (p := p) ((m + 3).descFactorial 3)) hB)
      (mm_vge_inv24 (by omega))
    exact vge_mono this (by norm_num)
  exact_mod_cast hv hk

/-! ## The modified moments -/

theorem mm_vge_int_dvd {z : ℤ} (h : (p : ℤ) ∣ z) : vge p (z : ℚ) 1 := by
  intro hz
  have hz0 : z ≠ 0 := by exact_mod_cast hz
  rw [padicValRat.of_int]
  have := (padicValInt_dvd_iff 1 z).mp (by simpa using h)
  rcases this with h0 | h1
  · exact absurd h0 hz0
  · exact_mod_cast h1

/-- A `p`-integral rational has denominator prime to `p`. -/
theorem not_dvd_den_of_vge {r : ℚ} (h : vge p r 0) : ¬ p ∣ r.den := by
  intro hd
  by_cases hr : r = 0
  · subst hr; simp at hd; exact (Fact.out : p.Prime).one_lt.ne' hd
  have hv := h hr
  have hnum : ¬ (p : ℤ) ∣ r.num := by
    intro hn
    have h1 : p ∣ r.num.natAbs := Int.natCast_dvd.mp hn
    have h2 : p ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hd
    rw [r.reduced] at h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum] at hv
  have h1 : 1 ≤ padicValNat p r.den := one_le_padicValNat_of_dvd r.den_nz hd
  have hv' : (0 : ℤ) ≤ 0 - (padicValNat p r.den : ℤ) := by exact_mod_cast hv
  omega

/-- The modified moments `µ(tᵉ) - c_e/p` are `p`-integral. -/
theorem muMod_vge (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (e : ℕ) :
    vge p (muMono e - cCorr p e / p) 0 := by
  obtain ⟨h1, h2⟩ := muMono_vge (p := p) hp e
  unfold cCorr
  split_ifs with he
  · simpa using h2 he
  · dsimp only
    set x := muMono e
    set r : ℚ := p * x with hr
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hrv : vge p r 0 := by
      have := vge_mul (mm_vge_nat_dvd (p := p) (dvd_refl p)) h1
      exact vge_mono this (by norm_num)
    have hden := not_dvd_den_of_vge hrv
    set c : ℕ := ((r.num : ZMod p) * ((r.den : ℕ) : ZMod p)⁻¹).val with hc
    set z : ℤ := r.num - c * r.den with hz
    have hdenZ : ((r.den : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact fun h => hden (Int.natCast_dvd_natCast.mp h)
    have hzdvd : (p : ℤ) ∣ z := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hz]
      push_cast
      rw [hc, ZMod.natCast_zmod_val]
      have : ((r.den : ℕ) : ZMod p) ≠ 0 := by exact_mod_cast hdenZ
      rw [mul_assoc, inv_mul_cancel₀ this, mul_one, sub_self]
    have hkey : x - (c : ℚ) / p = (z : ℚ) * ((r.den : ℕ) : ℚ)⁻¹ * (p : ℚ)⁻¹ := by
      have hd0 : ((r.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
      have hx : x = (r.num : ℚ) / r.den / p := by
        rw [Rat.num_div_den, hr]; field_simp
      rw [hx, hz]
      push_cast
      field_simp
    rw [hkey]
    have := vge_mul (vge_mul (mm_vge_int_dvd hzdvd)
      (mm_vge_inv_nat (p := p) r.den_nz 0 (by simpa using hden))) (vge_inv_p (p := p))
    exact vge_mono this (by norm_num)

/-! ## The decomposition (4.10) -/

/-- `D_m` over `ℤ`. -/
def Dz (m : ℕ) : ℤ[X] := ∏ j ∈ Icc 1 m, (X + C ((j : ℤ) ^ 2))

theorem Dz_monic (m : ℕ) : (Dz m).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem Dz_map (m : ℕ) : (Dz m).map (Int.castRingHom ℚ) = D m := by
  simp [Dz, D, Polynomial.map_prod]

/-- The polynomial quotient `Q_ij` has integer coefficients. -/
theorem quot_coeff_int (N K e : ℕ) (n : ℕ) :
    ∃ z : ℤ, ((D N ^ 6 * X ^ n) /ₘ sqPoleProd (Icc 1 K)).coeff e = z := by
  have hQ : (D N ^ 6 * X ^ n) /ₘ sqPoleProd (Icc 1 K) =
      ((Dz N ^ 6 * X ^ n) /ₘ Dz K).map (Int.castRingHom ℚ) := by
    rw [map_divByMonic _ (Dz_monic K), Polynomial.map_mul, Polynomial.map_pow, Dz_map,
      Polynomial.map_pow, map_X, Dz_map]
    rfl
  exact ⟨_, by rw [hQ, coeff_map]; rfl⟩

theorem cCorr_vge (e : ℕ) : vge p (cCorr p e) 0 := by
  unfold cCorr
  split_ifs
  · exact vge_zero _
  · exact mm_vge_nat _

theorem cCorr_of_lt {e : ℕ} (he : e < 2 * p - 3) : cCorr p e = 0 := by
  unfold cCorr; simp [he]

theorem D_natDeg (m : ℕ) : (D m).natDegree = m := by
  rw [show D m = sqPoleProd (Icc 1 m) from rfl, sqPoleProd_natDegree]; simp

/-- Rows outside `T` vanish, so the rank is at most `|T|`. -/
theorem rank_le_of_rows_zero {h : ℕ} (L : Matrix (Fin h) (Fin h) ℚ) (T : Finset (Fin h))
    (hz : ∀ i ∉ T, ∀ j, L i j = 0) : L.rank ≤ T.card := by
  rw [Matrix.rank_eq_finrank_span_row]
  have hsub : Submodule.span ℚ (Set.range L.row) ≤
      Submodule.span ℚ ((T.image L.row : Finset (Fin h → ℚ)) : Set (Fin h → ℚ)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ T
    · exact Submodule.subset_span (by simp; exact ⟨i, hi, rfl⟩)
    · have : L.row i = 0 := funext fun j => hz i hi j
      rw [this]; exact Submodule.zero_mem _
  refine (Submodule.finrank_mono hsub).trans ?_
  exact (finrank_span_finset_le_card _).trans card_image_le

theorem muX_eq_muXmod_add (S : Finset ℕ) (P : ℚ[X]) :
    muX S P = muXmod p S P +
      C ((p : ℚ)⁻¹ * ((P /ₘ sqPoleProd S).sum fun e c => c * cCorr p e)) := by
  unfold muX muXmod muPoly
  generalize P /ₘ sqPoleProd S = Q
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have : (Q.sum fun e c => c * muMono e) =
      (Q.sum fun e c => c * (muMono e - cCorr p e / p)) +
        (p : ℚ)⁻¹ * (Q.sum fun e c => c * cCorr p e) := by
    simp only [Polynomial.sum_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    field_simp
    ring
  rw [this, C_add]
  ring

/-- **(4.10)**: `G_K = A + p⁻¹L` with `L` constant, integral, and of rank at most `r_p`. -/
theorem decomp_4_10' {K p : ℕ} [Fact p.Prime] (hK : 40 ∣ K) (h : OuterHyp K p) :
    ∃ L : Matrix (Fin (hof K)) (Fin (hof K)) ℚ,
      G K = Aout K p + L.map (fun c => C ((p : ℚ)⁻¹ * c)) ∧
      (∀ i j, L i j ≠ 0 → 0 ≤ padicValRat p (L i j)) ∧ L.rank ≤ rOut K p := by
  set Q : Fin (hof K) → Fin (hof K) → ℚ[X] := fun i j =>
    (D (Nof K) ^ 6 * X ^ ((i : ℕ) + j)) /ₘ sqPoleProd (Icc 1 K) with hQ
  refine ⟨Matrix.of fun i j => (Q i j).sum fun e c => c * cCorr p e, ?_, ?_, ?_⟩
  · ext1 i j
    simp only [G, Aout, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply]
    exact muX_eq_muXmod_add _ _
  · intro i j hij
    have hv : vge p ((Q i j).sum fun e c => c * cCorr p e) 0 := by
      rw [Polynomial.sum_def]
      refine vge_sum _ _ fun e _ => ?_
      obtain ⟨z, hz⟩ := quot_coeff_int (Nof K) K e ((i : ℕ) + j)
      have := vge_mul (mm_vge_int (p := p) z) (cCorr_vge e)
      simp only [hQ]; rw [hz]; simpa using this
    exact_mod_cast hv hij
  · obtain ⟨n, rfl⟩ := hK
    obtain ⟨h7, hpK, hK3, h2K, h2N, h5N⟩ := h
    have hN : Nof (40 * n) = 3 * n := by unfold Nof; omega
    have hh : hof (40 * n) = 37 * n := by unfold hof; omega
    rw [hN] at h2N h5N
    set m0 := 2 * p - 2 - 5 * (3 * n)
    set T := (Finset.univ : Finset (Fin (hof (40 * n)))).filter
      fun i : Fin (hof (40 * n)) => m0 ≤ i.val
    have hzero : ∀ i ∉ T, ∀ j, (Matrix.of fun i j => (Q i j).sum fun e c => c * cCorr p e) i j = 0 := by
      intro i hi j
      have hi' : (i : ℕ) < m0 := by simpa [T] using hi
      have hj : (j : ℕ) < 37 * n := by have := j.2; omega
      simp only [Matrix.of_apply]
      rw [Polynomial.sum_def]
      refine Finset.sum_eq_zero fun e he => ?_
      have hdeg : (Q i j).natDegree ≤ 6 * (3 * n) + ((i : ℕ) + j) - 40 * n := by
        simp only [hQ]
        rw [natDegree_divByMonic _ (sqPoleProd_monic _), sqPoleProd_natDegree, Nat.card_Icc,
          Nat.add_sub_cancel]
        refine Nat.sub_le_sub_right ?_ _
        refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_pow_le _))
        refine natDegree_pow_le.trans ?_
        rw [D_natDeg, hN]
      have he' := le_natDegree_of_mem_supp e he
      rw [cCorr_of_lt (by omega), mul_zero]
    refine (rank_le_of_rows_zero _ T hzero).trans ?_
    have hcard : T.card ≤ 37 * n - m0 := by
      have hsub : T.map Fin.valEmbedding ⊆ Ico m0 (37 * n) := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
        have h1 : m0 ≤ i.val := (mem_filter.mp hi).2
        have h2 := i.2
        simp only [Fin.valEmbedding_apply, mem_Ico]
        omega
      have := card_le_card hsub
      rw [card_map, Nat.card_Ico] at this
      exact this
    unfold rOut
    rw [hN]
    omega

end Zeta5