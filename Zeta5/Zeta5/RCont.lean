import Zeta5.Defs

/-!
# Continuity of the limiting functions `R` and the outer integrand

`Lim.R` is continuous off a countable set (the points where one of the floors in (5.4)–(5.5)
jumps), and so is the integrand of (5.10); the latter is bounded on `[1/3, 2λ]`.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace Zeta5

namespace RCont

/-- `⌊·⌋` (as a real) is continuous at every non-integer. -/
lemma floor_continuousAt {y₀ : ℝ} (h : ∀ n : ℤ, y₀ ≠ n) :
    ContinuousAt (fun y : ℝ => ((⌊y⌋ : ℤ) : ℝ)) y₀ := by
  have h1 : (⌊y₀⌋ : ℝ) < y₀ := lt_of_le_of_ne (Int.floor_le y₀) (fun e => h _ e.symm)
  have h2 : y₀ < (⌊y₀⌋ : ℝ) + 1 := Int.lt_floor_add_one y₀
  have hmem : Set.Ico (⌊y₀⌋ : ℝ) ((⌊y₀⌋ : ℝ) + 1) ∈ 𝓝 y₀ :=
    Ico_mem_nhds h1 h2
  exact ((continuousOn_floor (α := ℝ) ⌊y₀⌋).continuousAt hmem)

/-- `x ↦ ⌊c x⌋` is continuous at `x₀` when `c x₀` is not an integer. -/
lemma floor_mul_continuousAt {c x₀ : ℝ} (h : ∀ n : ℤ, c * x₀ ≠ n) :
    ContinuousAt (fun x : ℝ => ((⌊c * x⌋ : ℤ) : ℝ)) x₀ :=
  (floor_continuousAt h).comp (continuousAt_const.mul continuousAt_id)

lemma pos_continuous : Continuous Lim.pos := continuous_id.max continuous_const

lemma abs_floor_le (w : ℝ) : |((⌊w⌋ : ℤ) : ℝ)| ≤ |w| + 1 := by
  have h1 := Int.floor_le w
  have h2 := Int.lt_floor_add_one w
  rw [abs_le]
  constructor <;> cases abs_cases w <;> linarith

lemma abs_ell_le (y z : ℝ) (hz : |z| ≤ 1) : |Lim.ell y z| ≤ 2 * |y| + 5 := by
  unfold Lim.ell
  have h1 := abs_floor_le (y - z)
  have h2 := abs_floor_le (y + z)
  have h3 : |y - z| ≤ |y| + |z| := abs_sub _ _
  have h4 : |y + z| ≤ |y| + |z| := abs_add_le _ _
  calc |((⌊y - z⌋ : ℤ) : ℝ) + ((⌊y + z⌋ : ℤ) : ℝ) + 1|
      ≤ |((⌊y - z⌋ : ℤ) : ℝ) + ((⌊y + z⌋ : ℤ) : ℝ)| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ |((⌊y - z⌋ : ℤ) : ℝ)| + |((⌊y + z⌋ : ℤ) : ℝ)| + 1 := by
        rw [abs_one]; linarith [abs_add_le ((⌊y - z⌋ : ℤ) : ℝ) ((⌊y + z⌋ : ℤ) : ℝ)]
    _ ≤ 2 * |y| + 5 := by linarith

/-- `x ↦ ℓ(c x, z)` is continuous at `x₀` unless `z ≡ ±c x₀ (mod 1)`. -/
lemma ell_continuousAt {c x₀ z : ℝ} (h1 : ∀ n : ℤ, c * x₀ - z ≠ n) (h2 : ∀ n : ℤ, c * x₀ + z ≠ n) :
    ContinuousAt (fun x : ℝ => Lim.ell (c * x) z) x₀ := by
  unfold Lim.ell
  have hc : Continuous fun x : ℝ => c * x := continuous_const.mul continuous_id
  refine ContinuousAt.add (ContinuousAt.add ?_ ?_) continuousAt_const
  · exact ContinuousAt.comp (g := fun y : ℝ => ((⌊y⌋ : ℤ) : ℝ)) (f := fun x => c * x - z)
      (floor_continuousAt h1) (by fun_prop)
  · exact ContinuousAt.comp (g := fun y : ℝ => ((⌊y⌋ : ℤ) : ℝ)) (f := fun x => c * x + z)
      (floor_continuousAt h2) (by fun_prop)

/-- The exceptional `z` for a given `x₀`. -/
def badZ (x₀ : ℝ) : Set ℝ :=
  ⋃ n : ℤ, ({Lim.α * x₀ - n, n - Lim.α * x₀, x₀ - n, n - x₀} : Set ℝ)

lemma badZ_countable (x₀ : ℝ) : (badZ x₀).Countable :=
  Set.countable_iUnion fun _ => Set.Finite.countable (by simp)

lemma ell_continuousAt' {c x₀ z : ℝ} (hz : ∀ n : ℤ, z ≠ c * x₀ - n ∧ z ≠ n - c * x₀) :
    ContinuousAt (fun x : ℝ => Lim.ell (c * x) z) x₀ := by
  refine ell_continuousAt (fun n e => (hz n).1 (by linarith)) (fun n e => (hz n).2 (by linarith))

/-- The z-integral in `Γ` is continuous at `x₀` when `2 Hc x₀` is not an integer. -/
lemma gamInt_continuousAt {x₀ : ℝ} (hT : ∀ n : ℤ, 2 * Lim.Hc * x₀ ≠ n) :
    ContinuousAt (fun x : ℝ => ∫ z in (0 : ℝ)..(1 / 2),
      (((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ) - 3 * Lim.ell (Lim.α * x) z) *
        (((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ) + 3 * Lim.ell (Lim.α * x) z - Lim.ell x z - 5)) x₀ := by
  set X := |x₀| + 1 with hX
  set A : ℝ := 3 * X + 1 + 3 * (2 * X + 5) with hA
  set B : ℝ := A + (2 * X + 5) + 5 with hB
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => A * B)
  · refine Eventually.of_forall fun x => ?_
    apply Measurable.aestronglyMeasurable
    unfold Lim.ell
    fun_prop
  · have hnb : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ 𝓝 x₀ := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hnb] with x hx
    refine Eventually.of_forall fun z hz => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hz
    have hz1 : |z| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    have hxX : |x| ≤ X := by
      rw [hX, abs_le]; constructor <;> cases abs_cases x₀ <;> linarith [hx.1, hx.2]
    have hX0 : 0 ≤ X := by positivity
    have hα : |Lim.α * x| ≤ X := by
      rw [abs_mul, Lim.α]; norm_num; linarith [abs_nonneg x]
    have hT' : |((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ)| ≤ 3 * X + 1 := by
      refine (abs_floor_le _).trans ?_
      rw [abs_mul, Lim.Hc]; norm_num; linarith
    have e1 := abs_ell_le (Lim.α * x) z hz1
    have e2 := abs_ell_le x z hz1
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
    · calc _ ≤ |((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ)| + |3 * Lim.ell (Lim.α * x) z| := abs_sub _ _
        _ ≤ A := by rw [abs_mul, hA]; norm_num; linarith
    · calc _ ≤ |((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ) + 3 * Lim.ell (Lim.α * x) z - Lim.ell x z| + |(5:ℝ)| :=
            abs_sub _ _
        _ ≤ |((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ) + 3 * Lim.ell (Lim.α * x) z| + |Lim.ell x z| + 5 := by
            norm_num; exact abs_sub _ _
        _ ≤ |((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ)| + |3 * Lim.ell (Lim.α * x) z| + |Lim.ell x z| + 5 := by
            linarith [abs_add_le ((⌊2 * Lim.Hc * x⌋ : ℤ) : ℝ) (3 * Lim.ell (Lim.α * x) z)]
        _ ≤ B := by rw [abs_mul, hB, hA]; norm_num; linarith
  · exact intervalIntegrable_const
  · have h0 : volume (badZ x₀) = 0 := (badZ_countable x₀).measure_zero volume
    rw [measure_eq_zero_iff_ae_notMem] at h0
    filter_upwards [h0] with z hz _
    have hz' : ∀ c : ℝ, (c = Lim.α ∨ c = 1) → ∀ n : ℤ, z ≠ c * x₀ - n ∧ z ≠ n - c * x₀ := by
      intro c hc n
      simp only [badZ, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, not_exists,
        not_or] at hz
      obtain ⟨a, b, c', d⟩ := hz n
      rcases hc with rfl | rfl
      · exact ⟨a, b⟩
      · simp only [one_mul]; exact ⟨c', d⟩
    have hA' := ell_continuousAt' (hz' _ (Or.inl rfl))
    have hB' : ContinuousAt (fun x : ℝ => Lim.ell x z) x₀ := by
      simpa using ell_continuousAt' (c := 1) (hz' _ (Or.inr rfl))
    have hT'' := floor_mul_continuousAt hT
    simp only [mul_assoc] at hT'' ⊢
    exact (hT''.sub (continuousAt_const.mul hA')).mul
      (((hT''.add (continuousAt_const.mul hA')).sub hB').sub continuousAt_const)

/-- The exceptional set for `R`. -/
def DR : Set ℝ :=
  ⋃ n : ℤ, ({(n : ℝ) / (2 * Lim.Hc), (n : ℝ) / 2, (n : ℝ), (n : ℝ) / Lim.α,
    (n : ℝ) / (2 * Lim.lam)} : Set ℝ)

lemma DR_countable : DR.Countable :=
  Set.countable_iUnion fun _ => Set.Finite.countable (by simp)

lemma not_int_of_notMem {c x : ℝ} (hc : c ≠ 0) (h : ∀ n : ℤ, x ≠ n / c) : ∀ n : ℤ, c * x ≠ n := by
  intro n e
  exact h n (by rw [← e]; field_simp)

end RCont

open RCont

theorem R_continuousAt_off : ∃ D : Set ℝ, D.Countable ∧
    ∀ x : ℝ, 0 < x → x ∉ D → ContinuousAt Lim.R x := by
  refine ⟨DR, DR_countable, fun x _ hx => ?_⟩
  simp only [DR, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, not_exists,
    not_or] at hx
  have hHc : (2 * Lim.Hc) ≠ 0 := by rw [Lim.Hc]; norm_num
  have hlam : (2 * Lim.lam) ≠ 0 := by rw [Lim.lam]; norm_num
  have hα0 : Lim.α ≠ 0 := by rw [Lim.α]; norm_num
  have hT := not_int_of_notMem hHc fun n => (hx n).1
  have hq := not_int_of_notMem (two_ne_zero) fun n => (hx n).2.1
  have h1 := not_int_of_notMem (one_ne_zero) fun n => by simpa using (hx n).2.2.1
  have hα := not_int_of_notMem hα0 fun n => (hx n).2.2.2.1
  have hl := not_int_of_notMem hlam fun n => (hx n).2.2.2.2
  have cT := floor_mul_continuousAt hT
  have cq := floor_mul_continuousAt hq
  have c1 : ContinuousAt (fun x : ℝ => ((⌊x⌋ : ℤ) : ℝ)) x := by
    simpa using floor_mul_continuousAt h1
  have cα := floor_mul_continuousAt hα
  have cl : ContinuousAt (fun x : ℝ => ((⌊2 * (Lim.lam * x)⌋ : ℤ) : ℝ)) x := by
    simpa only [mul_assoc] using floor_mul_continuousAt hl
  have cI := gamInt_continuousAt hT
  have cpos := pos_continuous
  unfold Lim.R Lim.Gam Lim.Nfun Lim.J
  simp only
  refine ((cI.add ?_).add ?_).neg.sub ?_
  · exact ((continuousAt_const.mul continuousAt_id).sub (cT.div_const _)).mul
      ((continuousAt_const.mul cT).sub cq |>.sub continuousAt_const)
  · exact cpos.continuousAt.comp
      (((continuousAt_const.mul continuousAt_id).sub (cT.div_const _)).sub
        (((continuousAt_const.mul continuousAt_id).sub cq).div_const _))
  · refine ((((continuousAt_const.mul continuousAt_id).mul c1).sub
      ((continuousAt_const.mul continuousAt_id).mul cα)).sub (continuousAt_const.mul ?_))
    exact (cl.mul (continuousAt_const.mul continuousAt_id)).sub
      ((cl.mul (cl.add continuousAt_const)).div_const _)

namespace RCont

/-- The exceptional set for the outer integrand. -/
def DO : Set ℝ := {1 / 3, 1 / 2, 1} ∪ ⋃ n : ℤ, ({1 / (n : ℝ)} : Set ℝ)

lemma DO_countable : DO.Countable :=
  (Set.Finite.countable (by simp)).union (Set.countable_iUnion fun _ => Set.countable_singleton _)

lemma R0_continuousAt {y : ℝ} (h1 : y ≠ 1 / 3) (h2 : y ≠ 1 / 2) (h3 : y ≠ 1) :
    ContinuousAt Lim.R0 y := by
  have cp := pos_continuous
  have e1 : Continuous fun y : ℝ =>
      8 - 9 * y - 8 * Lim.α - 5 * min Lim.α (1 - 2 * y) - 5 * Lim.pos (1 + Lim.α - 3 * y) := by
    fun_prop
  have e2 : Continuous fun y : ℝ =>
      7 * (1 - y) - 6 * min Lim.α (1 - y) - 6 * Lim.pos (1 + Lim.α - 2 * y) +
        Lim.pos (1 + 4 * Lim.α - 2 * y) := by
    fun_prop
  rcases lt_or_gt_of_ne h1 with ha | ha
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds ha] with w hw
    simp only [Lim.R0, Set.mem_Iio] at hw ⊢
    rw [if_neg (by intro h; linarith [h.1]), if_neg (by intro h; linarith [h.1])]
  rcases lt_or_gt_of_ne h2 with hb | hb
  · refine e1.continuousAt.congr ?_
    filter_upwards [Ioo_mem_nhds ha hb] with w hw
    simp only [Lim.R0]
    rw [if_pos (show 1 / 3 < w ∧ w < 1 / 2 from hw)]
  rcases lt_or_gt_of_ne h3 with hc | hc
  · refine e2.continuousAt.congr ?_
    filter_upwards [Ioo_mem_nhds hb hc] with w hw
    simp only [Lim.R0]
    rw [if_neg (by intro h; linarith [h.2, hw.1]), if_pos (show 1 / 2 < w ∧ w < 1 from hw)]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds hc] with w hw
    simp only [Lim.R0, Set.mem_Ioi] at hw ⊢
    rw [if_neg (by intro h; linarith [h.2]), if_neg (by intro h; linarith [h.2])]

lemma dfun_continuousAt {y : ℝ} (h1 : y ≠ 1 / 3) (h2 : y ≠ 1 / 2) :
    ContinuousAt Lim.dfun y := by
  have cp := pos_continuous
  have e1 : Continuous fun y : ℝ =>
      Lim.pos ((1 + 4 * Lim.α - 3 * y) - Lim.pos (1 + Lim.α - 3 * y)) := by fun_prop
  rcases lt_or_gt_of_ne h1 with ha | ha
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds ha] with w hw
    simp only [Lim.dfun, Set.mem_Iio] at hw ⊢
    rw [if_neg (by intro h; linarith [h.1])]
  rcases lt_or_gt_of_ne h2 with hb | hb
  · refine e1.continuousAt.congr ?_
    filter_upwards [Ioo_mem_nhds ha hb] with w hw
    simp only [Lim.dfun]
    rw [if_pos (show 1 / 3 < w ∧ w < 1 / 2 from hw)]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds hb] with w hw
    simp only [Lim.dfun, Set.mem_Ioi] at hw ⊢
    rw [if_neg (by intro h; linarith [h.2])]

end RCont

theorem outerIntegrand_continuousAt_off : ∃ D : Set ℝ, D.Countable ∧
    ∀ y : ℝ, 0 < y → y ∉ D → ContinuousAt Lim.outerIntegrand y := by
  refine ⟨DO, DO_countable, fun y hy hyD => ?_⟩
  simp only [DO, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iUnion,
    not_or, not_exists] at hyD
  obtain ⟨⟨h1, h2, h3⟩, hn⟩ := hyD
  have hfl : ContinuousAt (fun y : ℝ => ((⌊1 / y⌋ : ℤ) : ℝ)) y := by
    refine (floor_continuousAt fun n e => hn n ?_).comp
      (continuousAt_const.div continuousAt_id hy.ne')
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0; rw [h0] at e; simp [hy.ne'] at e
    field_simp at e ⊢
    linarith
  have cp := pos_continuous
  unfold Lim.outerIntegrand
  refine (((R0_continuousAt h1 h2 h3).sub (dfun_continuousAt h1 h2)).sub
    (continuousAt_const.mul hfl)).add ?_
  exact (continuous_finset_sum _ fun j _ => by fun_prop).continuousAt

theorem outerIntegrand_bounded : ∃ B : ℝ, ∀ y ∈ Set.Icc (1 / 3 : ℝ) (2 * Lim.lam),
    |Lim.outerIntegrand y| ≤ B := by
  refine ⟨100, fun y ⟨hy1, hy2⟩ => ?_⟩
  rw [Lim.lam] at hy2
  have hα : Lim.α = 3 / 40 := rfl
  have pos0 : ∀ v, 0 ≤ Lim.pos v := fun v => le_max_right _ _
  have posle : ∀ v w, v ≤ w → 0 ≤ w → Lim.pos v ≤ w := fun v w h hw => max_le h hw
  have hR0 : |Lim.R0 y| ≤ 20 := by
    unfold Lim.R0
    split_ifs with c1 c2
    · have m1 : min Lim.α (1 - 2 * y) ≤ Lim.α := min_le_left _ _
      have m2 : 0 ≤ min Lim.α (1 - 2 * y) := le_min (by rw [hα]; norm_num) (by linarith [c1.2])
      have p1 := posle (1 + Lim.α - 3 * y) 1 (by rw [hα]; linarith [c1.1]) (by norm_num)
      have p0 := pos0 (1 + Lim.α - 3 * y)
      rw [abs_le]; constructor <;> linarith [c1.1, c1.2]
    · have m1 : min Lim.α (1 - y) ≤ Lim.α := min_le_left _ _
      have m2 : 0 ≤ min Lim.α (1 - y) := le_min (by rw [hα]; norm_num) (by linarith [c2.2])
      have p1 := posle (1 + Lim.α - 2 * y) 1 (by rw [hα]; linarith [c2.1]) (by norm_num)
      have p0 := pos0 (1 + Lim.α - 2 * y)
      have q1 := posle (1 + 4 * Lim.α - 2 * y) 2 (by rw [hα]; linarith [c2.1]) (by norm_num)
      have q0 := pos0 (1 + 4 * Lim.α - 2 * y)
      rw [abs_le]; constructor <;> linarith [c2.1, c2.2]
    · norm_num
  have hd : |Lim.dfun y| ≤ 20 := by
    unfold Lim.dfun
    split_ifs with c1
    · have p0 := pos0 (1 + Lim.α - 3 * y)
      have q0 := pos0 ((1 + 4 * Lim.α - 3 * y) - Lim.pos (1 + Lim.α - 3 * y))
      have q1 := posle ((1 + 4 * Lim.α - 3 * y) - Lim.pos (1 + Lim.α - 3 * y)) 2
        (by linarith [c1.1, p0, hα]) (by norm_num)
      rw [abs_le]; constructor <;> linarith
    · norm_num
  have hfl : |((⌊1 / y⌋ : ℤ) : ℝ)| ≤ 4 := by
    have hy0 : 0 < y := by linarith
    have : 1 / y ≤ 3 := by rw [div_le_iff₀ hy0]; linarith
    have h0 : 0 ≤ 1 / y := by positivity
    refine (abs_floor_le _).trans ?_
    rw [abs_of_nonneg h0]; linarith
  have hs : |∑ j ∈ Finset.Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - (j : ℝ) * y)| ≤ 10 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ Finset.Icc (1 : ℕ) 5, |Lim.pos (2 * Lim.lam - (j : ℝ) * y)| ≤ 2 := by
      intro j _
      rw [abs_of_nonneg (pos0 _)]
      have hj : 0 ≤ (j : ℝ) * y := by positivity
      exact posle _ _ (by rw [Lim.lam]; linarith) (by norm_num)
    refine (Finset.sum_le_sum this).trans ?_
    simp; norm_num
  unfold Lim.outerIntegrand
  have hl : |2 * Lim.lam * ((⌊1 / y⌋ : ℤ) : ℝ)| ≤ 8 := by
    have e : |2 * Lim.lam| = 37 / 20 := by rw [Lim.lam]; norm_num
    rw [abs_mul, e]; linarith
  calc _ ≤ |Lim.R0 y - Lim.dfun y - 2 * Lim.lam * ((⌊1 / y⌋ : ℤ) : ℝ)| +
        |∑ j ∈ Finset.Icc (1 : ℕ) 5, Lim.pos (2 * Lim.lam - (j : ℝ) * y)| := abs_add_le _ _
    _ ≤ |Lim.R0 y - Lim.dfun y| + |2 * Lim.lam * ((⌊1 / y⌋ : ℤ) : ℝ)| + 10 := by
        linarith [abs_sub (Lim.R0 y - Lim.dfun y) (2 * Lim.lam * ((⌊1 / y⌋ : ℤ) : ℝ))]
    _ ≤ 100 := by linarith [abs_sub (Lim.R0 y) (Lim.dfun y)]

end Zeta5
