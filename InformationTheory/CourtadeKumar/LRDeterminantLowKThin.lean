import InformationTheory.CourtadeKumar.LRDeterminantLowKAnalytic

/-!
# Analytic thin branch of the audited low-`k` determinant bridge

This proves the `k <= 1/32` field of `LRLowKIdealReplayCertificate`
without a numerical certificate.  The proof uses the exact separation (DA2):
the linear coefficient is positive, the constant term is already above
`3/5`, and the reciprocal correction is nonnegative.
-/

open Set

namespace CourtadeKumar

private lemma lrLowK_log_mono
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  exact Real.strictMonoOn_log.monotoneOn
    (show x ∈ Ioi (0 : ℝ) from hx)
    (show y ∈ Ioi (0 : ℝ) from hx.trans_le hxy) hxy

lemma lrLowK_log_four_thirds_lower :
    (2 / 7 : ℝ) ≤ Real.log (4 / 3) := by
  have h := lr_log_one_add_lower
    (v := (1 / 3 : ℝ)) (by norm_num)
  convert h using 1 <;> norm_num

lemma lrLowK_log_four_thirds_upper :
    Real.log (4 / 3 : ℝ) < 36 / 125 := by
  have hart := artanh_le_cubicPade_unit
    (u := (1 / 7 : ℝ)) (show (1 / 7 : ℝ) ∈ Ico 0 1 by norm_num)
  have hid : Real.artanh (1 / 7 : ℝ) = Real.log (4 / 3) / 2 := by
    rw [Real.artanh_eq_half_log
      (show (1 / 7 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)]
    norm_num
    ring
  rw [hid] at hart
  norm_num at hart ⊢
  linarith

lemma lrLowKIdealH_le_one_add_log
    {t : ℝ} (ht : 0 ≤ t) :
    lrLowKIdealH (1 + t) ≤ 1 + Real.log (1 + t) := by
  rcases ht.eq_or_lt with rfl | htPos
  · norm_num [lrLowKIdealH]
  · have hone : 0 < 1 + t := by linarith
    have hlog := Real.log_le_sub_one_of_pos hone
    unfold lrLowKIdealH
    rw [if_neg (by linarith : 1 + t ≠ 1)]
    rw [show 1 + t - 1 = t by ring, div_le_iff₀ htPos]
    nlinarith

lemma lrLowKIdealH_ge_one
    {t : ℝ} (ht : 0 < t) :
    1 ≤ lrLowKIdealH (1 + t) := by
  have hlog := lr_log_one_add_lower ht.le
  have hden : 0 < 2 + t := by linarith
  have hscaled : t ≤ (1 + t) * (2 * t / (2 + t)) := by
    rw [← sub_nonneg]
    have hid : (1 + t) * (2 * t / (2 + t)) - t =
        t ^ 2 / (2 + t) := by
      field_simp [hden.ne']
      ring
    rw [hid]
    positivity
  have hone : 0 ≤ 1 + t := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hone
  unfold lrLowKIdealH
  rw [if_neg (by linarith : 1 + t ≠ 1)]
  rw [show 1 + t - 1 = t by ring, le_div_iff₀ ht]
  simpa using hscaled.trans hmul

lemma lrLowKIdealA_le_log_one_add
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowKIdealA k chi ≤ Real.log (1 + k) := by
  have hkchi : 0 ≤ k * chi := mul_nonneg hk.le hchi.1
  have hargChi : 0 < 1 + k * chi := by linarith
  have hkchi_le : k * chi ≤ k := by
    simpa using mul_le_mul_of_nonneg_left hchi.2 hk.le
  have hargOrder : 1 + k * chi ≤ 1 + k := by linarith
  have hlogOrder := lrLowK_log_mono hargChi hargOrder
  have hweighted := mul_le_mul_of_nonneg_left hlogOrder hchi.1
  have hden : 0 < 1 + chi := by linarith [hchi.1]
  unfold lrLowKIdealA
  rw [div_le_iff₀ hden]
  nlinarith

lemma lrLowKIdealAH_le_one_add_log
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowKIdealAH k chi ≤ 1 + Real.log (1 + k) := by
  have hkchi : 0 ≤ k * chi := mul_nonneg hk.le hchi.1
  have hargChi : 0 < 1 + k * chi := by linarith
  have hkchi_le : k * chi ≤ k := by
    simpa using mul_le_mul_of_nonneg_left hchi.2 hk.le
  have hargOrder : 1 + k * chi ≤ 1 + k := by linarith
  have hlogOrder := lrLowK_log_mono hargChi hargOrder
  have hHChi := lrLowKIdealH_le_one_add_log
    (t := k * chi) (mul_nonneg hk.le hchi.1)
  have hHChi' : lrLowKIdealH (1 + k * chi) ≤
      1 + Real.log (1 + k) := by linarith
  have hHK := lrLowKIdealH_le_one_add_log (t := k) hk.le
  have hweighted := mul_le_mul_of_nonneg_left hHChi' hchi.1
  have hden : 0 < 1 + chi := by linarith [hchi.1]
  unfold lrLowKIdealAH
  rw [div_le_iff₀ hden]
  nlinarith

lemma lrLowKIdealAH_ge_one
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    1 ≤ lrLowKIdealAH k chi := by
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · simpa [lrLowKIdealAH] using lrLowKIdealH_ge_one (t := k) hk
  · have hHChi := lrLowKIdealH_ge_one
      (t := k * chi) (mul_pos hk hchiPos)
    have hHK := lrLowKIdealH_ge_one (t := k) hk
    have hweighted := mul_le_mul_of_nonneg_left hHChi hchiPos.le
    have hden : 0 < 1 + chi := by linarith
    unfold lrLowKIdealAH
    rw [le_div_iff₀ hden]
    nlinarith

lemma lrLowKIdealD_eq_rho_add
    {k : ℝ} (hk : 0 < k) :
    lrLowKIdealD k =
      -Real.log k / 2 +
        (Real.log (1 + 2 * k) / 2 - Real.log 2 / 2 +
          1 / (4 * k + 3)) := by
  have hk2 : 2 * k ≠ 0 := (mul_pos (by norm_num) hk).ne'
  have hnum : 1 + 2 * k ≠ 0 := (by positivity : 0 < 1 + 2 * k).ne'
  have harg : 1 + 1 / (2 * k) = (1 + 2 * k) / (2 * k) := by
    field_simp [hk.ne']
    ring
  unfold lrLowKIdealD
  rw [harg, Real.log_div hnum hk2,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hk.ne']
  ring

private noncomputable def lrLowKThinP (k : ℝ) : ℝ :=
  2 * Real.log 2 + 1 - Real.log (1 + k)

private noncomputable def lrLowKThinS (k : ℝ) : ℝ :=
  Real.log k - 2 / 7 - Real.log (1 + k)

private noncomputable def lrLowKThinT (k : ℝ) : ℝ :=
  2 * Real.log 2 - Real.log (1 + k)

private noncomputable def lrLowKThinDBar (k : ℝ) : ℝ :=
  Real.log (1 + 2 * k) / 2 - Real.log 2 / 2 + 1 / (4 * k + 3)

private noncomputable def lrLowKThinLambda (k : ℝ) : ℝ :=
  2 * lrLowKIdealD k + lrLowKThinS k + 1 / 3

private noncomputable def lrLowKThinRInf (k : ℝ) : ℝ :=
  lrLowKIdealD k * lrLowKThinP k +
    lrLowKIdealBOffset k * lrLowKThinS k +
    (lrLowKThinT k - lrLowKIdealC) / 6 +
    (lrLowKIdealBOffset k - lrLowKIdealD k) / 3

lemma lrLowKThin_log_k_upper
    {k : ℝ} (hk : 0 < k) (hk32 : k ≤ 1 / 32) :
    Real.log k ≤ -5 * Real.log 2 := by
  have hlog := lrLowK_log_mono hk hk32
  have hendpoint : Real.log (1 / 32 : ℝ) = -5 * Real.log 2 := by
    rw [show (1 / 32 : ℝ) = 1 / 2 ^ 5 by norm_num,
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 ^ 5 : ℝ) ≠ 0),
      Real.log_one, Real.log_pow]
    norm_num
  rw [hendpoint] at hlog
  exact hlog

lemma lrLowKThin_log_one_add_bounds
    {k : ℝ} (hk : 0 < k) :
    0 < Real.log (1 + k) ∧ Real.log (1 + k) ≤ k := by
  constructor
  · exact Real.log_pos (by linarith)
  · simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + k by linarith)

lemma lrLowKThinDBar_gt
    {k : ℝ} (hk : 0 < k) :
    -1 / 60 < lrLowKThinDBar k := by
  have hlog := lr_log_one_add_lower (v := 2 * k) (by positivity)
  have hlogHalf : k / (1 + k) ≤ Real.log (1 + 2 * k) / 2 := by
    convert (mul_le_mul_of_nonneg_right hlog (by norm_num : (0 : ℝ) ≤ 1 / 2)) using 1 <;>
      field_simp
  have hdenOne : 0 < 1 + k := by positivity
  have hdenFour : 0 < 4 * k + 3 := by positivity
  have hrat : (1 / 3 : ℝ) ≤ k / (1 + k) + 1 / (4 * k + 3) := by
    rw [← sub_nonneg]
    have hid :
        k / (1 + k) + 1 / (4 * k + 3) - 1 / 3 =
          k * (8 * k + 5) / (3 * (1 + k) * (4 * k + 3)) := by
      field_simp [hdenOne.ne', hdenFour.ne']
      ring
    rw [hid]
    positivity
  have hlogTwo : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrLowKThinDBar
  nlinarith

lemma lrLowKThin_correction_nonneg
    {k : ℝ} (hk : 0 < k) :
    0 ≤ Real.log (1 + 2 * k) - Real.log (1 + k) +
      2 / (4 * k + 3) - 2 / 3 := by
  let u := k / (1 + k)
  have hdenOne : 0 < 1 + k := by positivity
  have hdenTwo : 0 < 2 + 3 * k := by positivity
  have hdenFour : 0 < 4 * k + 3 := by positivity
  have hu : 0 ≤ u := by positivity
  have hlog := lr_log_one_add_lower hu
  have hlogIdentity : Real.log (1 + u) =
      Real.log (1 + 2 * k) - Real.log (1 + k) := by
    have hnum : 1 + 2 * k ≠ 0 := (by positivity : 0 < 1 + 2 * k).ne'
    have hden : 1 + k ≠ 0 := hdenOne.ne'
    rw [← Real.log_div hnum hden]
    congr 1
    dsimp [u]
    field_simp [hden]
    ring
  have hfracIdentity : 2 * u / (2 + u) = 2 * k / (2 + 3 * k) := by
    dsimp [u]
    field_simp [hdenOne.ne', hdenTwo.ne']
    ring
  have hlogDiff : 2 * k / (2 + 3 * k) ≤
      Real.log (1 + 2 * k) - Real.log (1 + k) := by
    rw [← hlogIdentity, ← hfracIdentity]
    exact hlog
  have hrat : 8 * k / (3 * (4 * k + 3)) ≤ 2 * k / (2 + 3 * k) := by
    rw [← sub_nonneg]
    have hid :
        2 * k / (2 + 3 * k) - 8 * k / (3 * (4 * k + 3)) =
          2 * k / ((2 + 3 * k) * (3 * (4 * k + 3))) := by
      field_simp [hdenTwo.ne', hdenFour.ne']
      ring
    rw [hid]
    positivity
  have hrecip : 2 / (4 * k + 3) - 2 / 3 =
      -(8 * k / (3 * (4 * k + 3))) := by
    field_simp [hdenFour.ne']
    ring
  linarith

lemma lrLowKThinLambda_gt
    {k : ℝ} (hk : 0 < k) :
    1 / 70 < lrLowKThinLambda k := by
  have hD := lrLowKIdealD_eq_rho_add hk
  have hcorr := lrLowKThin_correction_nonneg hk
  have hlogTwo : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hid : lrLowKThinLambda k =
      (Real.log (1 + 2 * k) - Real.log (1 + k) +
        2 / (4 * k + 3) - 2 / 3) +
      (5 / 7 - Real.log 2) := by
    unfold lrLowKThinLambda lrLowKThinS
    rw [hD]
    ring
  rw [hid]
  nlinarith

lemma lrLowKThinRInf_gt
    {k : ℝ} (hk : 0 < k) (hk32 : k ≤ 1 / 32) :
    3 / 5 < lrLowKThinRInf k := by
  have hD := lrLowKIdealD_eq_rho_add hk
  have hlogk := lrLowKThin_log_k_upper hk hk32
  have hell := lrLowKThin_log_one_add_bounds hk
  have hlogTwoLower : (693 / 1000 : ℝ) < Real.log 2 := by
    exact (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlogTwoUpper : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlog43Upper := lrLowK_log_four_thirds_upper
  have hd := lrLowKThinDBar_gt hk
  have hformula : lrLowKThinRInf k =
      (-Real.log k) / 3 +
        lrLowKThinDBar k *
          (2 * Real.log 2 + 2 / 3 - Real.log (1 + k)) +
        lrLowKIdealBOffset k *
          (1 / 3 - 2 / 7 - Real.log (1 + k)) +
        (2 * Real.log 2 - Real.log (1 + k) - lrLowKIdealC) / 6 := by
    unfold lrLowKThinRInf lrLowKThinP lrLowKThinS lrLowKThinT
    rw [hD]
    unfold lrLowKThinDBar lrLowKIdealBOffset
    ring
  rw [hformula]
  have hrho : 231 / 200 < (-Real.log k) / 3 := by
    nlinarith
  let coeff := 2 * Real.log 2 + 2 / 3 - Real.log (1 + k)
  have hcoeffPos : 0 < coeff := by
    dsimp [coeff]
    nlinarith
  have hcoeffUpper : coeff < 31 / 15 := by
    dsimp [coeff]
    nlinarith
  have hdTerm : -31 / 900 < lrLowKThinDBar k * coeff := by
    have hshift : 0 < (lrLowKThinDBar k + 1 / 60) * coeff :=
      mul_pos (by linarith) hcoeffPos
    have hbase : -(1 / 60 : ℝ) * coeff > -31 / 900 := by
      have h := mul_lt_mul_of_neg_left hcoeffUpper
        (show (-1 / 60 : ℝ) < 0 by norm_num)
      norm_num at h ⊢
      exact h
    nlinarith
  have hbPos : 0 < lrLowKIdealBOffset k := by
    unfold lrLowKIdealBOffset
    nlinarith
  have hbCoeff : 0 ≤ 1 / 3 - 2 / 7 - Real.log (1 + k) := by
    nlinarith
  have hbTerm : 0 ≤ lrLowKIdealBOffset k *
      (1 / 3 - 2 / 7 - Real.log (1 + k)) :=
    mul_nonneg hbPos.le hbCoeff
  have hlast :
      (693 / 250 - 1 - 1 / 32 - 576 / 125) / 6 <
        (2 * Real.log 2 - Real.log (1 + k) - lrLowKIdealC) / 6 := by
    unfold lrLowKIdealC
    nlinarith
  have htotal :
      (46273 / 72000 : ℝ) <
        (-Real.log k) / 3 + lrLowKThinDBar k * coeff +
          lrLowKIdealBOffset k *
            (1 / 3 - 2 / 7 - Real.log (1 + k)) +
          (2 * Real.log 2 - Real.log (1 + k) - lrLowKIdealC) / 6 := by
    dsimp [coeff] at hdTerm ⊢
    nlinarith
  exact (by norm_num : (3 / 5 : ℝ) < 46273 / 72000).trans htotal

lemma lrLowKIdealD_pos
    {k : ℝ} (hk : 0 < k) : 0 < lrLowKIdealD k := by
  have hinv : 0 < 1 / (2 * k) := by positivity
  have hlog : 0 < Real.log (1 + 1 / (2 * k)) :=
    Real.log_pos (by linarith)
  unfold lrLowKIdealD
  positivity

lemma lrLowKIdealC1_nonneg_thin
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowKIdealC1 k chi := by
  have hell := lrLowKThin_log_one_add_bounds hk
  have hAH := lrLowKIdealAH_ge_one hk hchi
  have hD := lrLowKIdealD_pos hk
  have hlogTwo : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlog43 := lrLowK_log_four_thirds_lower
  have hfirst : lrLowKIdealT k chi - lrLowKIdealC ≤ 0 := by
    unfold lrLowKIdealT lrLowKIdealC
    nlinarith
  have hsecond :
      lrLowKIdealBOffset k - lrLowKIdealD k - lrLowKIdealC / 2 ≤ 0 := by
    unfold lrLowKIdealBOffset lrLowKIdealC
    nlinarith
  unfold lrLowKIdealC1
  exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hfirst hsecond) (by norm_num)

lemma lrLowKIdealLambda_ge_thin
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowKThinLambda k ≤ lrLowKIdealLambda k chi := by
  have hq := lrSmallSBridgeQChi_lower hchi
  have hqDef : lrLowKIdealQChi chi = lrSmallSBridgeQChi chi := by rfl
  have hA := lrLowKIdealA_le_log_one_add hk hchi
  unfold lrLowKThinLambda lrLowKThinS lrLowKIdealLambda lrLowKIdealS
  rw [hqDef]
  linarith

lemma lrLowKIdealRInf_gt_thinRInf
    {k chi : ℝ} (hk : 0 < k) (hk32 : k ≤ 1 / 32)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowKThinRInf k < lrLowKIdealRInf k chi := by
  have hq := lrSmallSBridgeQChi_lower hchi
  have hqDef : lrLowKIdealQChi chi = lrSmallSBridgeQChi chi := by rfl
  have hA := lrLowKIdealA_le_log_one_add hk hchi
  have hAH := lrLowKIdealAH_le_one_add_log hk hchi
  have hD := lrLowKIdealD_pos hk
  have hell := lrLowKThin_log_one_add_bounds hk
  have hb : 0 < lrLowKIdealBOffset k := by
    unfold lrLowKIdealBOffset
    nlinarith [Real.log_two_gt_d9]
  have hP : lrLowKThinP k ≤ lrLowKIdealP k chi := by
    unfold lrLowKThinP lrLowKIdealP
    linarith
  have hS : lrLowKThinS k < lrLowKIdealS k chi := by
    unfold lrLowKThinS lrLowKIdealS
    rw [hqDef]
    linarith
  have hT : lrLowKThinT k ≤ lrLowKIdealT k chi := by
    unfold lrLowKThinT lrLowKIdealT
    linarith
  have hDP := mul_le_mul_of_nonneg_left hP hD.le
  have hbS := mul_lt_mul_of_pos_left hS hb
  unfold lrLowKThinRInf lrLowKIdealRInf
  linarith

/-- The audited thin ideal-core inequality.  This is the exact proposition
needed for the `thin` field of `LRLowKIdealReplayCertificate`. -/
theorem lrLowKIdealCore_gt_three_fifths_thin
    {L k chi : ℝ} (hL : lrLowKIdealL0 ≤ L)
    (hk : 0 < k) (hk32 : k ≤ 1 / 32)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    3 / 5 < lrLowKIdealCore L k chi := by
  have hden : 0 < L + lrLowKIdealC := by
    linarith [lrLowKIdealL0_add_C_pos]
  rw [lrLowKIdealCore_eq_separated hden.ne']
  unfold lrLowKIdealSeparated
  have hLambdaBar := lrLowKThinLambda_gt hk
  have hLambdaCompare := lrLowKIdealLambda_ge_thin hk hchi
  have hLambda : 0 < lrLowKIdealLambda k chi := by linarith
  have hLNonneg : 0 ≤ L := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold lrLowKIdealL0 at hL
    nlinarith
  have hlinear : 0 ≤ L * lrLowKIdealLambda k chi / 2 := by positivity
  have hRbar := lrLowKThinRInf_gt hk hk32
  have hRCompare := lrLowKIdealRInf_gt_thinRInf hk hk32 hchi
  have hR : 3 / 5 < lrLowKIdealRInf k chi := hRbar.trans hRCompare
  have hC1 := lrLowKIdealC1_nonneg_thin hk hchi
  have hreciprocal : 0 ≤ lrLowKIdealC1 k chi / (L + lrLowKIdealC) :=
    div_nonneg hC1 hden.le
  linarith


/-- The analytic thin theorem removes the noncompact field from the remaining
low-`k` replay obligation.  Only the two compact endpoint replays remain. -/
theorem lrLowKIdealReplayCertificate_of_middle_upper
    (middle : ∀ k chi : ℝ,
      k ∈ Icc (1 / 32 : ℝ) (5 / 32) → chi ∈ Icc (0 : ℝ) 1 →
        19 / 50 <
            lrLowKIdealCore lrLowKIdealL0 k chi -
              lrLowKIdealC1 k chi /
                (lrLowKIdealL0 + lrLowKIdealC) ∧
          0 < lrLowKIdealLambda k chi / 2 ∧
          0 < lrLowKIdealC1 k chi)
    (upper : ∀ k chi : ℝ,
      k ∈ Icc (5 / 32 : ℝ) 1 → chi ∈ Icc (0 : ℝ) 1 →
        19 / 50 < lrLowKIdealCore lrLowKIdealL0 k chi ∧
          0 < lrLowKIdealLambda k chi / 2 -
            lrLowKIdealC1 k chi /
              (lrLowKIdealL0 + lrLowKIdealC) ^ 2 ∧
          0 < lrLowKIdealC1 k chi) :
    LRLowKIdealReplayCertificate where
  thin := by
    intro L k chi hL hk hk32 _hLk hchi
    exact lrLowKIdealCore_gt_three_fifths_thin hL hk hk32 hchi
  middle := middle
  upper := upper

end CourtadeKumar
