set_option maxHeartbeats 4000000 in
lemma log2_enc : (6931471805599453094172152 / 10 ^ 25 : ℝ) ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ 6931471805599453094172323 / 10 ^ 25 := by
  have h := log_series_bounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = (2 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 4000000 in
lemma logy_enc_0 : (2639034991761707930494974 / 10 ^ 25 : ℝ) ≤ Real.log (1017189489 / 781250000 : ℝ) ∧ Real.log (1017189489 / 781250000 : ℝ) ≤ 2639034991761707930494975 / 10 ^ 25 := by
  have h := log_series_bounds (235939489 / 1798439489 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (235939489 / 1798439489 : ℝ)) / (1 - (235939489 / 1798439489 : ℝ)) = (1017189489 / 781250000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_0 : Lk 0 = Real.log (1017189489 / 781250000 : ℝ) - 10 * Real.log 2 := by
  have : (B 0 - A 0) / 4 = (1017189489 / 781250000 : ℝ) / 2 ^ 10 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_1 : (5114334076167610199456728 / 10 ^ 25 : ℝ) ≤ Real.log (13028749591 / 7812500000 : ℝ) ∧ Real.log (13028749591 / 7812500000 : ℝ) ≤ 5114334076167610199456729 / 10 ^ 25 := by
  have h := log_series_bounds (5216249591 / 20841249591 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (5216249591 / 20841249591 : ℝ)) / (1 - (5216249591 / 20841249591 : ℝ)) = (13028749591 / 7812500000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_1 : Lk 1 = Real.log (13028749591 / 7812500000 : ℝ) - 9 * Real.log 2 := by
  have : (B 1 - A 1) / 4 = (13028749591 / 7812500000 : ℝ) / 2 ^ 9 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_2 : (4427514000489370722782089 / 10 ^ 25 : ℝ) ≤ Real.log (24327894059 / 15625000000 : ℝ) ∧ Real.log (24327894059 / 15625000000 : ℝ) ≤ 4427514000489370722782090 / 10 ^ 25 := by
  have h := log_series_bounds (8702894059 / 39952894059 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (8702894059 / 39952894059 : ℝ)) / (1 - (8702894059 / 39952894059 : ℝ)) = (24327894059 / 15625000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_2 : Lk 2 = Real.log (24327894059 / 15625000000 : ℝ) - 8 * Real.log 2 := by
  have : (B 2 - A 2) / 4 = (24327894059 / 15625000000 : ℝ) / 2 ^ 8 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_3 : (2722317986562477655062526 / 10 ^ 25 : ℝ) ≤ Real.log (4102785289 / 3125000000 : ℝ) ∧ Real.log (4102785289 / 3125000000 : ℝ) ≤ 2722317986562477655062527 / 10 ^ 25 := by
  have h := log_series_bounds (977785289 / 7227785289 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (977785289 / 7227785289 : ℝ)) / (1 - (977785289 / 7227785289 : ℝ)) = (4102785289 / 3125000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_3 : Lk 3 = Real.log (4102785289 / 3125000000 : ℝ) - 7 * Real.log 2 := by
  have : (B 3 - A 3) / 4 = (4102785289 / 3125000000 : ℝ) / 2 ^ 7 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_4 : (434102579263321756742153 / 10 ^ 25 : ℝ) ≤ Real.log (65272891657 / 62500000000 : ℝ) ∧ Real.log (65272891657 / 62500000000 : ℝ) ≤ 434102579263321756742154 / 10 ^ 25 := by
  have h := log_series_bounds (2772891657 / 127772891657 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (2772891657 / 127772891657 : ℝ)) / (1 - (2772891657 / 127772891657 : ℝ)) = (65272891657 / 62500000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_4 : Lk 4 = Real.log (65272891657 / 62500000000 : ℝ) - 6 * Real.log 2 := by
  have : (B 4 - A 4) / 4 = (65272891657 / 62500000000 : ℝ) / 2 ^ 6 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_5 : (4608086171046564701853377 / 10 ^ 25 : ℝ) ≤ Real.log (99084713271 / 62500000000 : ℝ) ∧ Real.log (99084713271 / 62500000000 : ℝ) ≤ 4608086171046564701853378 / 10 ^ 25 := by
  have h := log_series_bounds (36584713271 / 161584713271 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (36584713271 / 161584713271 : ℝ)) / (1 - (36584713271 / 161584713271 : ℝ)) = (99084713271 / 62500000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_5 : Lk 5 = Real.log (99084713271 / 62500000000 : ℝ) - 6 * Real.log 2 := by
  have : (B 5 - A 5) / 4 = (99084713271 / 62500000000 : ℝ) / 2 ^ 6 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_6 : (1417899108615240211499012 / 10 ^ 25 : ℝ) ≤ Real.log (144041816267 / 125000000000 : ℝ) ∧ Real.log (144041816267 / 125000000000 : ℝ) ≤ 1417899108615240211499013 / 10 ^ 25 := by
  have h := log_series_bounds (19041816267 / 269041816267 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (19041816267 / 269041816267 : ℝ)) / (1 - (19041816267 / 269041816267 : ℝ)) = (144041816267 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_6 : Lk 6 = Real.log (144041816267 / 125000000000 : ℝ) - 5 * Real.log 2 := by
  have : (B 6 - A 6) / 4 = (144041816267 / 125000000000 : ℝ) / 2 ^ 5 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_7 : (4744614610375889389052186 / 10 ^ 25 : ℝ) ≤ Real.log (200893556541 / 125000000000 : ℝ) ∧ Real.log (200893556541 / 125000000000 : ℝ) ≤ 4744614610375889389052187 / 10 ^ 25 := by
  have h := log_series_bounds (75893556541 / 325893556541 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (75893556541 / 325893556541 : ℝ)) / (1 - (75893556541 / 325893556541 : ℝ)) = (200893556541 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_7 : Lk 7 = Real.log (200893556541 / 125000000000 : ℝ) - 5 * Real.log 2 := by
  have : (B 7 - A 7) / 4 = (200893556541 / 125000000000 : ℝ) / 2 ^ 5 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_8 : (739227235165382858563697 / 10 ^ 25 : ℝ) ≤ Real.log (269180899217 / 250000000000 : ℝ) ∧ Real.log (269180899217 / 250000000000 : ℝ) ≤ 739227235165382858563698 / 10 ^ 25 := by
  have h := log_series_bounds (19180899217 / 519180899217 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (19180899217 / 519180899217 : ℝ)) / (1 - (19180899217 / 519180899217 : ℝ)) = (269180899217 / 250000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_8 : Lk 8 = Real.log (269180899217 / 250000000000 : ℝ) - 4 * Real.log 2 := by
  have : (B 8 - A 8) / 4 = (269180899217 / 250000000000 : ℝ) / 2 ^ 4 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_9 : (3277376495783627238092016 / 10 ^ 25 : ℝ) ≤ Real.log (21684762939 / 15625000000 : ℝ) ∧ Real.log (21684762939 / 15625000000 : ℝ) ≤ 3277376495783627238092017 / 10 ^ 25 := by
  have h := log_series_bounds (6059762939 / 37309762939 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (6059762939 / 37309762939 : ℝ)) / (1 - (6059762939 / 37309762939 : ℝ)) = (21684762939 / 15625000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_9 : Lk 9 = Real.log (21684762939 / 15625000000 : ℝ) - 4 * Real.log 2 := by
  have : (B 9 - A 9) / 4 = (21684762939 / 15625000000 : ℝ) / 2 ^ 4 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_10 : (5439396883934419370169222 / 10 ^ 25 : ℝ) ≤ Real.log (430695182301 / 250000000000 : ℝ) ∧ Real.log (430695182301 / 250000000000 : ℝ) ≤ 5439396883934419370169223 / 10 ^ 25 := by
  have h := log_series_bounds (180695182301 / 680695182301 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (180695182301 / 680695182301 : ℝ)) / (1 - (180695182301 / 680695182301 : ℝ)) = (430695182301 / 250000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_10 : Lk 10 = Real.log (430695182301 / 250000000000 : ℝ) - 4 * Real.log 2 := by
  have : (B 10 - A 10) / 4 = (430695182301 / 250000000000 : ℝ) / 2 ^ 4 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_11 : (304623689623510702107029 / 10 ^ 25 : ℝ) ≤ Real.log (128866386789 / 125000000000 : ℝ) ∧ Real.log (128866386789 / 125000000000 : ℝ) ≤ 304623689623510702107030 / 10 ^ 25 := by
  have h := log_series_bounds (3866386789 / 253866386789 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (3866386789 / 253866386789 : ℝ)) / (1 - (3866386789 / 253866386789 : ℝ)) = (128866386789 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_11 : Lk 11 = Real.log (128866386789 / 125000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 11 - A 11) / 4 = (128866386789 / 125000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_12 : (1745631428282761730092773 / 10 ^ 25 : ℝ) ≤ Real.log (595362962907 / 500000000000 : ℝ) ∧ Real.log (595362962907 / 500000000000 : ℝ) ≤ 1745631428282761730092774 / 10 ^ 25 := by
  have h := log_series_bounds (95362962907 / 1095362962907 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (95362962907 / 1095362962907 : ℝ)) / (1 - (95362962907 / 1095362962907 : ℝ)) = (595362962907 / 500000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_12 : Lk 12 = Real.log (595362962907 / 500000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 12 - A 12) / 4 = (595362962907 / 500000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_13 : (2839190749069400025615562 / 10 ^ 25 : ℝ) ≤ Real.log (166040678943 / 125000000000 : ℝ) ∧ Real.log (166040678943 / 125000000000 : ℝ) ≤ 2839190749069400025615563 / 10 ^ 25 := by
  have h := log_series_bounds (41040678943 / 291040678943 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (41040678943 / 291040678943 : ℝ)) / (1 - (41040678943 / 291040678943 : ℝ)) = (166040678943 / 125000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_13 : Lk 13 = Real.log (166040678943 / 125000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 13 - A 13) / 4 = (166040678943 / 125000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_14 : (3591927980478393943451068 / 10 ^ 25 : ℝ) ≤ Real.log (716086447547 / 500000000000 : ℝ) ∧ Real.log (716086447547 / 500000000000 : ℝ) ≤ 3591927980478393943451069 / 10 ^ 25 := by
  have h := log_series_bounds (216086447547 / 1216086447547 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (216086447547 / 1216086447547 : ℝ)) / (1 - (216086447547 / 1216086447547 : ℝ)) = (716086447547 / 500000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_14 : Lk 14 = Real.log (716086447547 / 500000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 14 - A 14) / 4 = (716086447547 / 500000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma logy_enc_15 : (4008753303197060018486061 / 10 ^ 25 : ℝ) ≤ Real.log (746565554359 / 500000000000 : ℝ) ∧ Real.log (746565554359 / 500000000000 : ℝ) ≤ 4008753303197060018486062 / 10 ^ 25 := by
  have h := log_series_bounds (246565554359 / 1246565554359 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (246565554359 / 1246565554359 : ℝ)) / (1 - (246565554359 / 1246565554359 : ℝ)) = (746565554359 / 500000000000 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Lk_15 : Lk 15 = Real.log (746565554359 / 500000000000 : ℝ) - 3 * Real.log 2 := by
  have : (B 15 - A 15) / 4 = (746565554359 / 500000000000 : ℝ) / 2 ^ 3 := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma log65_enc : (1823215567939546262117180 / 10 ^ 25 : ℝ) ≤ Real.log (6 / 5 : ℝ) ∧ Real.log (6 / 5 : ℝ) ≤ 1823215567939546262117181 / 10 ^ 25 := by
  have h := log_series_bounds (1 / 11 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (1 / 11 : ℝ)) / (1 - (1 / 11 : ℝ)) = (6 / 5 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 4000000 in
lemma log3720_enc : (6151856390902334509328719 / 10 ^ 25 : ℝ) ≤ Real.log (37 / 20 : ℝ) ∧ Real.log (37 / 20 : ℝ) ≤ 6151856390902334509328721 / 10 ^ 25 := by
  have h := log_series_bounds (17 / 57 : ℝ) (by norm_num) (by norm_num) 22
  rw [show (1 + (17 / 57 : ℝ)) / (1 - (17 / 57 : ℝ)) = (37 / 20 : ℝ) by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]
