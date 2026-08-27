import InformationTheory.CourtadeKumar.LRSmallSBridgeFrozen

/-!
# The `v`-channel loss in the small-`s` bridge

This file proves the elementary coordinate and rational estimates behind
manuscript (M31).  In particular, the exact cancellation-coordinate value
of `v` satisfies `1-v ≤ (501/1000)sk`, and the resulting normalized loss is
at most the stated rational `epsilon_v`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallSBridgeEpsilonV : ℝ := 355543 / 819200000

lemma lr_exp_five_thirds_gt_five :
    (5 : ℝ) < Real.exp (5 / 3) := by
  have hsum := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 5 / 3 by norm_num) 5
  norm_num [Finset.sum_range_succ] at hsum ⊢
  exact (by norm_num : (5 : ℝ) < 10009 / 1944).trans_le hsum

lemma lr_log_five_lt_five_thirds :
    Real.log 5 < (5 / 3 : ℝ) :=
  (Real.log_lt_iff_lt_exp (by norm_num)).2 lr_exp_five_thirds_gt_five

lemma lrSmallSBridgeD_mem
    {s k : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4) :
    lrSmallSBridgeD s k ∈ Icc (0 : ℝ) (5 / 6) := by
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hinvLower : (1 / 4 : ℝ) ≤ 1 / k := by
    rw [le_div_iff₀ hkPos]
    nlinarith [hk.2]
  have hinvUpper : 1 / k ≤ (4 : ℝ) := by
    rw [div_le_iff₀ hkPos]
    nlinarith [hk.1]
  have hrewrite : (1 + (1 - s) * k) / k = 1 / k + 1 - s := by
    field_simp [hkPos.ne']
    ring
  have hargLower : 1 < (1 + (1 - s) * k) / k := by
    rw [hrewrite]
    nlinarith [hs.2]
  have hargUpper : (1 + (1 - s) * k) / k ≤ 5 := by
    rw [hrewrite]
    nlinarith [hs.1]
  have hlogNonneg : 0 ≤ Real.log ((1 + (1 - s) * k) / k) :=
    (Real.log_pos hargLower).le
  have hlogUpper := Real.log_le_log
    (show (0 : ℝ) < (1 + (1 - s) * k) / k by linarith [hargLower])
    hargUpper
  unfold lrSmallSBridgeD
  constructor
  · positivity
  · nlinarith [lr_log_five_lt_five_thirds]

lemma lrSmallSBridgeE_upper
    {s k : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4) :
    0 < s * k ∧ s * k ≤ 1 / 4096 := by
  constructor
  · exact mul_pos hs.1 ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1)
  · have := mul_le_mul hs.2 hk.2
      ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hk.1) (by norm_num)
    norm_num at this ⊢
    exact this

/-- The square-root coordinate estimate quoted before (M31). -/
theorem lrSmallSBridge_one_sub_v_le
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    1 - lrCertificateV ⟨s, k, chi⟩ ≤
      (501 / 1000 : ℝ) * (s * k) := by
  let e := s * k
  let x := 1 - chi * e
  let v := lrCertificateV (⟨s, k, chi⟩ : CertificatePoint)
  have he := lrSmallSBridgeE_upper hs hk
  have heLt : e < 1 := he.2.trans_lt (by norm_num)
  have hxPos : 0 < x := by
    unfold x
    have hprod : chi * e ≤ 1 * e :=
      mul_le_mul_of_nonneg_right hchi.2 he.1.le
    nlinarith
  have hxLe : x ≤ 1 := by
    unfold x
    exact sub_le_self _ (mul_nonneg hchi.1 he.1.le)
  have hnumNonneg : 0 ≤ 1 - e := sub_nonneg.mpr heLt.le
  have hradPos : 0 < (1 - e) / x := div_pos (sub_pos.mpr heLt) hxPos
  have hvSq : v ^ 2 = (1 - e) / x := by
    unfold v lrCertificateV lrCertificateE lrCertificateX
    exact Real.sq_sqrt hradPos.le
  have hvNonneg : 0 ≤ v := by
    unfold v lrCertificateV
    exact Real.sqrt_nonneg _
  have hradLower : 1 - e ≤ (1 - e) / x := by
    rw [le_div_iff₀ hxPos]
    exact mul_le_of_le_one_right hnumNonneg hxLe
  have hvLower : (999 / 1000 : ℝ) ≤ v := by
    have heNumeric : (999 / 1000 : ℝ) ^ 2 ≤ 1 - e := by
      nlinarith [he.2]
    nlinarith [hvSq, hradLower]
  have hnumLeX : 1 - e ≤ x := by
    unfold x
    have hchie : chi * e ≤ e := by
      simpa using mul_le_mul_of_nonneg_right hchi.2 he.1.le
    linarith
  have hradLe : (1 - e) / x ≤ 1 := by
    rw [div_le_one hxPos]
    exact hnumLeX
  have hvLe : v ≤ 1 := by nlinarith [hvSq, hradLe]
  have hgap : (1 - v) * (1 + v) ≤ e := by
    calc
      (1 - v) * (1 + v) = 1 - v ^ 2 := by ring
      _ ≤ e := by
        rw [hvSq]
        linarith [hradLower]
  have hdNonneg : 0 ≤ 1 - v := sub_nonneg.mpr hvLe
  have hfactor : (1999 / 1000 : ℝ) * (1 - v) ≤
      (1 - v) * (1 + v) := by
    nlinarith [mul_nonneg hdNonneg (sub_nonneg.mpr hvLower)]
  change 1 - v ≤ (501 / 1000 : ℝ) * e
  nlinarith

lemma lrSmallSBridge_a_le_d
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    (1 - v) / (1 + v) ≤ 1 - v := by
  have hden : 0 < 1 + v := by linarith [hv.1]
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) hv.1]

/-- The rational payment in (M31), isolated from the preceding exact
subtraction identity. -/
theorem lrSmallSBridge_v_loss_bound
    {s k d a D : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hd : d ∈ Icc (0 : ℝ) ((501 / 1000) * (s * k)))
    (ha : a ∈ Icc (0 : ℝ) d)
    (hD : D ∈ Icc (0 : ℝ) (5 / 6)) :
    D * (2 * d ^ 2 / s + a / 4) ≤ lrSmallSBridgeEpsilonV := by
  have hkNonneg : 0 ≤ k := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hk.1
  have hdLinear : d ≤ (501 / 250 : ℝ) * s := by
    have hsk : s * k ≤ s * 4 := mul_le_mul_of_nonneg_left hk.2 hs.1.le
    nlinarith [hd.2]
  have hdSq : d ^ 2 ≤ ((501 / 250 : ℝ) * s) ^ 2 := by
    nlinarith [hd.1]
  have hdSqDiv : d ^ 2 / s ≤ (501 / 250 : ℝ) ^ 2 * s := by
    rw [div_le_iff₀ hs.1]
    nlinarith
  have haQuarter : a / 4 ≤ (501 / 1000 : ℝ) * s := by
    nlinarith [ha.2, hdLinear]
  have htwo : 2 * d ^ 2 / s ≤ 2 * (501 / 250 : ℝ) ^ 2 * s := by
    calc
      2 * d ^ 2 / s = 2 * (d ^ 2 / s) := by ring
      _ ≤ 2 * ((501 / 250 : ℝ) ^ 2 * s) :=
        mul_le_mul_of_nonneg_left hdSqDiv (by norm_num)
      _ = 2 * (501 / 250 : ℝ) ^ 2 * s := by ring
  have hinner : 2 * d ^ 2 / s + a / 4 ≤
      (2 * (501 / 250 : ℝ) ^ 2 + (501 / 1000 : ℝ)) * s := by
    nlinarith
  have hinnerNonneg : 0 ≤ 2 * d ^ 2 / s + a / 4 :=
    add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg d)) hs.1.le)
      (div_nonneg ha.1 (by norm_num))
  calc
    D * (2 * d ^ 2 / s + a / 4) ≤
        (5 / 6 : ℝ) * (2 * d ^ 2 / s + a / 4) :=
      mul_le_mul_of_nonneg_right hD.2 hinnerNonneg
    _ ≤ (5 / 6 : ℝ) *
        ((2 * (501 / 250 : ℝ) ^ 2 + (501 / 1000 : ℝ)) * s) :=
      mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ ≤ lrSmallSBridgeEpsilonV := by
      unfold lrSmallSBridgeEpsilonV
      nlinarith [hs.2]

end CourtadeKumar
