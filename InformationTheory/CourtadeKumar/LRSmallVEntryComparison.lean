import InformationTheory.CourtadeKumar.LRSmallVEntryBounds

/-!
# The index-two small-odds comparison

The positive main part of `F₂` has a uniform `ξ/[48(1+v)]` margin.
The geometric `R₂` tail costs at most exactly that margin.  This closes
the sole entry inequality needed by the strengthened tail propagation.
-/

open Set

namespace CourtadeKumar

lemma lrLowQ_two_eq_vt
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowQ (v ^ 2 * t ^ 2) 2 = lrL (v * t) -
      (v ^ 2 * t ^ 2) * (1 - lrLowAlpha 1) / 2 := by
  have hξ0 : 0 < v ^ 2 * t ^ 2 := mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hξ1 : v ^ 2 * t ^ 2 < 1 := by
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  rw [lrLowQ_two_eq hξ0 hξ1]
  rw [lrLow_sqrt_vsq_mul (x := t ^ 2) hv.1.le,
    Real.sqrt_sq_eq_abs, abs_of_pos ht.1]

theorem lrSmallVEntry_main_margin
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    v ^ 2 * t ^ 2 / (48 * (1 + v)) ≤
      lrLowVComparisonConstant v (t ^ 2) * lrLowAlpha 2 -
        lrLowDelta v (t ^ 2) * lrLowQ (v ^ 2 * t ^ 2) 2 := by
  let ξ : ℝ := v ^ 2 * t ^ 2
  let y : ℝ := v * t ^ 2
  have hξ0 : 0 < ξ := by
    dsimp [ξ]
    exact mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hξ1 : ξ < 1 := by
    dsimp [ξ]
    have hvt : v * t < 1 := calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  have hy : y ≤ 1 / 3 := by
    dsimp [y]
    have htSq : t ^ 2 ≤ 1 := by
      nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    calc
      v * t ^ 2 ≤ v * 1 := mul_le_mul_of_nonneg_left htSq hv.1.le
      _ ≤ 1 / 3 := by simpa using hvSmall
  have hcoef : lrLowAlpha 2 - 1 + y ≤ 0 := by
    have ha2le : lrLowAlpha 2 ≤ lrLowAlpha 1 :=
      lrLowAlpha_antitone (by norm_num : 1 ≤ 2)
    have ha1 := lrLowAlpha_one_lt_quarter.le
    linarith
  have hL := lrL_le_geometric
    (mul_nonneg hv.1.le ht.1.le)
    (show v * t < 1 by
      calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2)
  have hL' : lrL (v * t) ≤ ξ / (2 * (1 - ξ)) := by
    dsimp [ξ]
    simpa [show (v * t) ^ 2 = v ^ 2 * t ^ 2 by ring] using hL
  have hscaled :
      (lrLowAlpha 2 - 1 + y) * (ξ / (2 * (1 - ξ))) ≤
        (lrLowAlpha 2 - 1 + y) * lrL (v * t) :=
    mul_le_mul_of_nonpos_left hL' hcoef
  have hbracket := lrSmallVEntryBracket_ge hv.1 hvSmall
    (show t ^ 2 ∈ Icc (0 : ℝ) 1 from
      ⟨sq_nonneg t, by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]⟩)
  have hdenV : 1 + v ≠ 0 := by linarith [hv.1]
  have hdenξ : 1 - ξ ≠ 0 := by linarith
  have hdenξ' : 1 - v ^ 2 * t ^ 2 ≠ 0 := by simpa [ξ] using hdenξ
  have hidentity :
      ξ / (2 * (1 + v)) * lrSmallVEntryBracket v (t ^ 2) =
        ((lrLowAlpha 2 - 1 + y) * (ξ / (2 * (1 - ξ))) +
          (1 - y) * ξ * (1 - lrLowAlpha 1) / 2 +
          lrLowAlpha 2 * lrFlowBeta v * v * t ^ 2) / (1 + v) := by
    unfold lrSmallVEntryBracket
    dsimp [ξ, y]
    field_simp [hdenV, hdenξ', hv.1.ne']
    ring
  have hmainIdentity :
      lrLowVComparisonConstant v (t ^ 2) * lrLowAlpha 2 -
          lrLowDelta v (t ^ 2) * lrLowQ (v ^ 2 * t ^ 2) 2 =
        ((lrLowAlpha 2 - 1 + y) * lrL (v * t) +
          (1 - y) * ξ * (1 - lrLowAlpha 1) / 2 +
          lrLowAlpha 2 * lrFlowBeta v * v * t ^ 2) / (1 + v) := by
    rw [lrLowQ_two_eq_vt hv ht]
    unfold lrLowVComparisonConstant lrLowDelta lrFlowM
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
    dsimp [ξ, y]
    field_simp [hdenV]
    ring
  have hpref : 0 ≤ ξ / (2 * (1 + v)) :=
    div_nonneg hξ0.le (mul_nonneg (by norm_num) (by linarith [hv.1]))
  calc
    v ^ 2 * t ^ 2 / (48 * (1 + v)) =
        ξ / (2 * (1 + v)) * (1 / 24) := by
          dsimp [ξ]
          field_simp [hdenV]
          ring
    _ ≤ ξ / (2 * (1 + v)) * lrSmallVEntryBracket v (t ^ 2) :=
      mul_le_mul_of_nonneg_left hbracket hpref
    _ = ((lrLowAlpha 2 - 1 + y) * (ξ / (2 * (1 - ξ))) +
          (1 - y) * ξ * (1 - lrLowAlpha 1) / 2 +
          lrLowAlpha 2 * lrFlowBeta v * v * t ^ 2) / (1 + v) := hidentity
    _ ≤ ((lrLowAlpha 2 - 1 + y) * lrL (v * t) +
          (1 - y) * ξ * (1 - lrLowAlpha 1) / 2 +
          lrLowAlpha 2 * lrFlowBeta v * v * t ^ 2) / (1 + v) := by
      exact div_le_div_of_nonneg_right (by linarith) (by linarith [hv.1])
    _ = lrLowVComparisonConstant v (t ^ 2) * lrLowAlpha 2 -
          lrLowDelta v (t ^ 2) * lrLowQ (v ^ 2 * t ^ 2) 2 := hmainIdentity.symm

theorem lrSmallVEntry_tail_margin
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrGShape t v * lrLowRTail (v ^ 2 * t ^ 2) 2 ≤
      v ^ 2 * t ^ 2 / (48 * (1 + v)) := by
  let ξ : ℝ := v ^ 2 * t ^ 2
  have hξ0 : 0 < ξ := by
    dsimp [ξ]
    exact mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hξ1 : ξ < 1 := by
    dsimp [ξ]
    have hvt : v * t < 1 := calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  have htSq : t ^ 2 ≤ 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hξv : ξ ≤ v ^ 2 := by
    dsimp [ξ]
    simpa using mul_le_mul_of_nonneg_left htSq (sq_nonneg v)
  have hG0 : 0 ≤ lrGShape t v := lrGShape_nonneg hv ht
  have hphiT : 0 ≤ topPhi t :=
    topPhi_nonneg ⟨by linarith [ht.1], ht.2.le⟩
  have hvtMem : v * t ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hv.1 ht.1]
    · have hvt : v * t < 1 := calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
      exact hvt.le
  have hphiVT : 0 ≤ topPhi (v * t) := topPhi_nonneg hvtMem
  have hGle : lrGShape t v ≤ lrG v := by
    unfold lrGShape
    have hquot : 0 ≤ topPhi (v * t) / v := div_nonneg hphiVT hv.1.le
    linarith
  have hg0 : 0 ≤ lrG v := hG0.trans hGle
  have hR0 : 0 ≤ lrLowRTail ξ 2 := lrLowRTail_nonneg hξ0.le 2
  have hR := lrLowRTail_two_le_geometric hξ0.le hξ1
  have hprod : lrGShape t v * lrLowRTail ξ 2 ≤
      lrG v * (ξ ^ 3 / (2 * (1 - ξ))) :=
    mul_le_mul hGle hR hR0 hg0
  have hvg : v * lrG v ≤ 3 / 4 := by
    simpa [lrSmallVG] using lrSmallVG_le_three_fourths hv.1 hvSmall
  have hξSq : ξ ^ 2 ≤ v ^ 4 := by
    have hmul := mul_le_mul hξv hξv hξ0.le (sq_nonneg v)
    nlinarith
  have hpoly : 18 * (1 + v) * v ^ 4 ≤ v * (1 - v ^ 2) := by
    have hfac : 0 ≤ (1 + v) * (1 - 3 * v) * (6 * v ^ 2 + 2 * v + 1) :=
      mul_nonneg
        (mul_nonneg (by linarith [hv.1]) (by linarith [hvSmall]))
        (by nlinarith [sq_nonneg v])
    rw [← sub_nonneg]
    rw [show v * (1 - v ^ 2) - 18 * (1 + v) * v ^ 4 =
      v * ((1 + v) * (1 - 3 * v) * (6 * v ^ 2 + 2 * v + 1)) by ring]
    exact mul_nonneg hv.1.le hfac
  have hpolyξ : 18 * (1 + v) * ξ ^ 2 ≤ v * (1 - ξ) := by
    have hfactor18 : 0 ≤ 18 * (1 + v) :=
      mul_nonneg (by norm_num) (by linarith [hv.1])
    have hfirst := mul_le_mul_of_nonneg_left hξSq
      hfactor18
    have hsecond : v * (1 - v ^ 2) ≤ v * (1 - ξ) :=
      mul_le_mul_of_nonneg_left (by linarith [hξv]) hv.1.le
    exact hfirst.trans (hpoly.trans hsecond)
  have hcore : 24 * (1 + v) * lrG v * ξ ^ 2 ≤ 1 - ξ := by
    have hfactor24 : 0 ≤ 24 * (1 + v) * ξ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith [hv.1])) (sq_nonneg ξ)
    have hscale := mul_le_mul_of_nonneg_left hvg
      hfactor24
    have hwithV :
        v * (24 * (1 + v) * lrG v * ξ ^ 2) ≤ v * (1 - ξ) := by
      calc
        v * (24 * (1 + v) * lrG v * ξ ^ 2) =
            24 * (1 + v) * ξ ^ 2 * (v * lrG v) := by ring
        _ ≤ 24 * (1 + v) * ξ ^ 2 * (3 / 4) := hscale
        _ = 18 * (1 + v) * ξ ^ 2 := by ring
        _ ≤ v * (1 - ξ) := hpolyξ
    exact le_of_mul_le_mul_left hwithV hv.1
  have hgeom : lrG v * (ξ ^ 3 / (2 * (1 - ξ))) ≤
      ξ / (48 * (1 + v)) := by
    have hdenLeft : 0 < 2 * (1 - ξ) := mul_pos (by norm_num) (sub_pos.mpr hξ1)
    have hdenRight : 0 < 48 * (1 + v) := mul_pos (by norm_num) (by linarith [hv.1])
    rw [show lrG v * (ξ ^ 3 / (2 * (1 - ξ))) =
      (lrG v * ξ ^ 3) / (2 * (1 - ξ)) by ring]
    rw [div_le_div_iff₀ hdenLeft hdenRight]
    have htwoξ : 0 ≤ 2 * ξ := mul_nonneg (by norm_num) hξ0.le
    have hscaled := mul_le_mul_of_nonneg_left hcore htwoξ
    calc
      lrG v * ξ ^ 3 * (48 * (1 + v)) =
          (2 * ξ) * (24 * (1 + v) * lrG v * ξ ^ 2) := by ring
      _ ≤ (2 * ξ) * (1 - ξ) := hscaled
      _ = ξ * (2 * (1 - ξ)) := by ring
  dsimp [ξ] at hprod hgeom ⊢
  exact hprod.trans hgeom

theorem lrLowVComparison_two_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) 2 := by
  have hmain := lrSmallVEntry_main_margin hv hvSmall ht
  have htail := lrSmallVEntry_tail_margin hv hvSmall ht
  have hF : 0 ≤ lrLowFComparison v (t ^ 2) (lrGShape t v) 2 := by
    rw [lrLowFComparison_eq_C_alpha_sub_tails hv.1 (sq_pos_of_pos ht.1)
      (show v ^ 2 * t ^ 2 < 1 by
        have hvt : v * t < 1 := calc
          v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
          _ < 1 := by simpa using ht.2
        rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
        nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)])
      (by norm_num)]
    linarith
  unfold lrLowFComparison at hF
  linarith [lrLowVStar_nonneg_smallV hv hvSmall ht]

end CourtadeKumar
