import InformationTheory.CourtadeKumar.LRDeterminantLowKRestoration

/-!
# Low-`k` analytic determinant bridge: exact interface

This module formalizes the symbolic part of the audited low-`k` bridge
(DA2), and imports the exact rational restoration ledger (DA7).  It leaves
two explicit certificate inputs:

* the ideal-core bounds: the analytic thin branch and two compact replays
  in `(k, chi)`;
* the ideal-to-exact restoration inequality.

No executable shortcut is used: every conclusion below is a theorem checked
by the Lean kernel.
-/

open Set

namespace CourtadeKumar

/-! ## The exact ideal logarithmic core -/

noncomputable def lrLowKIdealC : ℝ :=
  1 - 2 * Real.log 2 + 16 * Real.log (4 / 3)

/-- The function `h(z) = z log z / (z - 1)`, with its continuous value at
`z = 1`. -/
noncomputable def lrLowKIdealH (z : ℝ) : ℝ :=
  if z = 1 then 1 else z * Real.log z / (z - 1)

noncomputable def lrLowKIdealA (k chi : ℝ) : ℝ :=
  (chi * Real.log (1 + k * chi) + Real.log (1 + k)) / (1 + chi)

noncomputable def lrLowKIdealAH (k chi : ℝ) : ℝ :=
  (chi * lrLowKIdealH (1 + k * chi) + lrLowKIdealH (1 + k)) /
    (1 + chi)

noncomputable def lrLowKIdealQChi (chi : ℝ) : ℝ :=
  chi * Real.log chi / (1 + chi)

noncomputable def lrLowKIdealD (k : ℝ) : ℝ :=
  Real.log (1 + 1 / (2 * k)) / 2 + 1 / (4 * k + 3)

noncomputable def lrLowKIdealBOffset (k : ℝ) : ℝ :=
  Real.log 2 - Real.log (1 + k) / 2

noncomputable def lrLowKIdealP (k chi : ℝ) : ℝ :=
  2 * Real.log 2 + 1 - lrLowKIdealA k chi

noncomputable def lrLowKIdealS (k chi : ℝ) : ℝ :=
  Real.log k + lrLowKIdealQChi chi - lrLowKIdealA k chi

noncomputable def lrLowKIdealT (k chi : ℝ) : ℝ :=
  2 * Real.log 2 + 1 - lrLowKIdealAH k chi

noncomputable def lrLowKIdealLambda (k chi : ℝ) : ℝ :=
  2 * lrLowKIdealD k + lrLowKIdealS k chi + 1 / 3

noncomputable def lrLowKIdealRInf (k chi : ℝ) : ℝ :=
  lrLowKIdealD k * lrLowKIdealP k chi +
    lrLowKIdealBOffset k * lrLowKIdealS k chi +
    (lrLowKIdealT k chi - lrLowKIdealC) / 6 +
    (lrLowKIdealBOffset k - lrLowKIdealD k) / 3

noncomputable def lrLowKIdealC1 (k chi : ℝ) : ℝ :=
  (lrLowKIdealT k chi - lrLowKIdealC) *
    (lrLowKIdealBOffset k - lrLowKIdealD k - lrLowKIdealC / 2) / 3

/-- The ideal determinant in its original DA1-style form. -/
noncomputable def lrLowKIdealCore (L k chi : ℝ) : ℝ :=
  lrLowKIdealD k * (L + lrLowKIdealP k chi) +
    (L / 2 + lrLowKIdealBOffset k) * lrLowKIdealS k chi +
    (L / 2 + lrLowKIdealBOffset k - lrLowKIdealD k) *
      (L + lrLowKIdealT k chi) / (3 * (L + lrLowKIdealC))

/-- The separated right side of (DA2). -/
noncomputable def lrLowKIdealSeparated (L k chi : ℝ) : ℝ :=
  L * lrLowKIdealLambda k chi / 2 + lrLowKIdealRInf k chi +
    lrLowKIdealC1 k chi / (L + lrLowKIdealC)

/-- Pure algebra behind the exact separation (DA2). -/
lemma lrLowKIdealCore_separation_algebra
    {L D P S T b C : ℝ} (hLC : L + C ≠ 0) :
    D * (L + P) + (L / 2 + b) * S +
        (L / 2 + b - D) * (L + T) / (3 * (L + C)) =
      L * (2 * D + S + 1 / 3) / 2 +
        (D * P + b * S + (T - C) / 6 + (b - D) / 3) +
        ((T - C) * (b - D - C / 2) / 3) / (L + C) := by
  field_simp [hLC]
  ring

/-- Formula (DA2), specialized to the audited ideal core. -/
theorem lrLowKIdealCore_eq_separated
    {L k chi : ℝ} (hLC : L + lrLowKIdealC ≠ 0) :
    lrLowKIdealCore L k chi = lrLowKIdealSeparated L k chi := by
  unfold lrLowKIdealCore lrLowKIdealSeparated lrLowKIdealLambda
    lrLowKIdealRInf lrLowKIdealC1
  exact lrLowKIdealCore_separation_algebra hLC

noncomputable def lrLowKIdealL0 : ℝ := 7 * Real.log 2

lemma lrLowKIdealL0_add_C_pos :
    0 < lrLowKIdealL0 + lrLowKIdealC := by
  have hlog43 : 0 < Real.log (4 / 3 : ℝ) := by
    exact Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrLowKIdealL0 lrLowKIdealC
  nlinarith

/-! ## Exact propagation from the fixed-`L` replay -/

/-- Abstract lower-band propagation used on `1/32 ≤ k ≤ 5/32`.
The endpoint replay deliberately subtracts the entire positive reciprocal
term, leaving a lower bound that is stable for all larger `L`. -/
lemma lrLowKSeparated_lower_of_endpointReserve
    {L0 L Lambda R C1 C margin : ℝ}
    (hu0 : 0 < L0 + C) (hL : L0 ≤ L)
    (hLambda : 0 ≤ Lambda / 2) (hC1 : 0 ≤ C1)
    (hendpoint : margin <
      (L0 * Lambda / 2 + R + C1 / (L0 + C)) - C1 / (L0 + C)) :
    margin < L * Lambda / 2 + R + C1 / (L + C) := by
  have hu : 0 < L + C := by linarith
  have hlinear : 0 ≤ (L - L0) * (Lambda / 2) :=
    mul_nonneg (sub_nonneg.mpr hL) hLambda
  have hratio : 0 ≤ C1 / (L + C) := div_nonneg hC1 hu.le
  nlinarith

/-- Abstract upper-band propagation used on `5/32 ≤ k ≤ 1`.
The derivative in (DA2) can only increase, because `C1 ≥ 0`. -/
lemma lrLowKSeparated_mono_of_endpointDerivative
    {L0 L Lambda R C1 C : ℝ}
    (hu0 : 0 < L0 + C) (hL : L0 ≤ L) (hC1 : 0 ≤ C1)
    (hderivative : 0 < Lambda / 2 - C1 / (L0 + C) ^ 2) :
    L0 * Lambda / 2 + R + C1 / (L0 + C) ≤
      L * Lambda / 2 + R + C1 / (L + C) := by
  have hu : 0 < L + C := by linarith
  have hprod : (L0 + C) ^ 2 ≤ (L0 + C) * (L + C) := by
    nlinarith
  have hquot : C1 / ((L0 + C) * (L + C)) ≤
      C1 / (L0 + C) ^ 2 := by
    exact div_le_div_of_nonneg_left hC1 (sq_pos_of_pos hu0) hprod
  have hfactor : 0 < Lambda / 2 -
      C1 / ((L0 + C) * (L + C)) := by
    linarith
  have hdelta : 0 ≤ (L - L0) *
      (Lambda / 2 - C1 / ((L0 + C) * (L + C))) :=
    mul_nonneg (sub_nonneg.mpr hL) hfactor.le
  have hid :
      L * Lambda / 2 + R + C1 / (L + C) =
        (L0 * Lambda / 2 + R + C1 / (L0 + C)) +
          (L - L0) *
            (Lambda / 2 - C1 / ((L0 + C) * (L + C))) := by
    field_simp [hu0.ne', hu.ne']
    ring
  rw [hid]
  linarith

/-- The exact ideal-core obligations.  The `thin` field is the analytic
`k ≤ 1/32` argument; `middle` and `upper` are the two compact interval
replays at `L₀ = 7 log 2`. -/
structure LRLowKIdealReplayCertificate : Prop where
  thin : ∀ L k chi : ℝ,
    lrLowKIdealL0 ≤ L → 0 < k → k ≤ 1 / 32 →
      -Real.log k ≤ L → chi ∈ Icc (0 : ℝ) 1 →
      3 / 5 < lrLowKIdealCore L k chi
  middle : ∀ k chi : ℝ,
    k ∈ Icc (1 / 32 : ℝ) (5 / 32) → chi ∈ Icc (0 : ℝ) 1 →
      19 / 50 <
          lrLowKIdealCore lrLowKIdealL0 k chi -
            lrLowKIdealC1 k chi /
              (lrLowKIdealL0 + lrLowKIdealC) ∧
        0 < lrLowKIdealLambda k chi / 2 ∧
        0 < lrLowKIdealC1 k chi
  upper : ∀ k chi : ℝ,
    k ∈ Icc (5 / 32 : ℝ) 1 → chi ∈ Icc (0 : ℝ) 1 →
      19 / 50 < lrLowKIdealCore lrLowKIdealL0 k chi ∧
        0 < lrLowKIdealLambda k chi / 2 -
          lrLowKIdealC1 k chi /
            (lrLowKIdealL0 + lrLowKIdealC) ^ 2 ∧
        0 < lrLowKIdealC1 k chi

/-- Sound propagation of the compact replay from `L0 = 7 log 2` to every
larger logarithmic scale. -/
theorem lrLowKIdealCore_gt_nineteen_fiftieths
    (certificate : LRLowKIdealReplayCertificate)
    {L k chi : ℝ} (hL : lrLowKIdealL0 ≤ L)
    (hLk : -Real.log k ≤ L)
    (hk : k ∈ Ioc (0 : ℝ) 1) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    19 / 50 < lrLowKIdealCore L k chi := by
  by_cases hkThin : k ≤ 1 / 32
  · have hthin := certificate.thin L k chi hL hk.1 hkThin hLk hchi
    norm_num at hthin ⊢
    linarith
  have hkLower : 1 / 32 ≤ k := le_of_lt (lt_of_not_ge hkThin)
  by_cases hkMiddle : k ≤ 5 / 32
  · rcases certificate.middle k chi ⟨hkLower, hkMiddle⟩ hchi with
      ⟨hendpoint, hLambda, hC1⟩
    have hu0ne : lrLowKIdealL0 + lrLowKIdealC ≠ 0 :=
      lrLowKIdealL0_add_C_pos.ne'
    rw [lrLowKIdealCore_eq_separated hu0ne] at hendpoint
    unfold lrLowKIdealSeparated at hendpoint
    have hsep := lrLowKSeparated_lower_of_endpointReserve
      (L0 := lrLowKIdealL0) (L := L)
      (Lambda := lrLowKIdealLambda k chi)
      (R := lrLowKIdealRInf k chi) (C1 := lrLowKIdealC1 k chi)
      (C := lrLowKIdealC) (margin := 19 / 50)
      lrLowKIdealL0_add_C_pos hL hLambda.le hC1.le hendpoint
    rw [lrLowKIdealCore_eq_separated
      (by linarith [lrLowKIdealL0_add_C_pos])]
    unfold lrLowKIdealSeparated
    exact hsep
  · have hkFive : 5 / 32 ≤ k := le_of_lt (lt_of_not_ge hkMiddle)
    rcases certificate.upper k chi ⟨hkFive, hk.2⟩ hchi with
      ⟨hendpoint, hderivative, hC1⟩
    have hu0ne : lrLowKIdealL0 + lrLowKIdealC ≠ 0 :=
      lrLowKIdealL0_add_C_pos.ne'
    rw [lrLowKIdealCore_eq_separated hu0ne] at hendpoint
    unfold lrLowKIdealSeparated at hendpoint
    have hmono := lrLowKSeparated_mono_of_endpointDerivative
      (L0 := lrLowKIdealL0) (L := L)
      (Lambda := lrLowKIdealLambda k chi)
      (R := lrLowKIdealRInf k chi) (C1 := lrLowKIdealC1 k chi)
      (C := lrLowKIdealC)
      lrLowKIdealL0_add_C_pos hL hC1.le hderivative
    rw [lrLowKIdealCore_eq_separated
      (by linarith [lrLowKIdealL0_add_C_pos])]
    unfold lrLowKIdealSeparated
    exact hendpoint.trans_le hmono

/-- The exact DA7 ledger turns the ideal `19/50` margin and the analytic
restoration comparison into the required positive `2/25` margin. -/
lemma lrLowK_margin_after_restoration
    {ideal actual : ℝ} (hideal : 19 / 50 < ideal)
    (hrestore : ideal - lrDA7RestoreEndpoint ≤ actual) :
    2 / 25 < actual :=
  lrDA7_final_of_total_restore hideal le_rfl hrestore

/-! ## Sound adapter to the determinant ledger -/

/-- Manuscript normalization `n = e(1+chi)/4`. -/
noncomputable def lrLowKNormalization (point : CertificatePoint) : ℝ :=
  lrCertificateE point * (1 + point.chi) / 4

/-- The exact normalized singular determinant `mathcal E` in (DA1). -/
noncomputable def lrLowKActualNormalized (point : CertificatePoint) : ℝ :=
  lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point) /
    lrLowKNormalization point

/-- The remaining analytic restoration statement.  Its right side is the
actual determinant, not a surrogate, so this interface cannot admit a
certificate for the wrong function. -/
def LRLowKRestorationCertificate : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantLowKRegion point →
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrDA7RestoreEndpoint ≤
      lrLowKActualNormalized point

lemma lrLowK_log_scale_ge_L0
    {point : CertificatePoint} (hinterior : LRHighShapeInterior point)
    (hsSmall : point.s ≤ 1 / 128) :
    lrLowKIdealL0 ≤ Real.log (1 / point.s) := by
  have harg : (128 : ℝ) ≤ 1 / point.s := by
    rw [le_div_iff₀ hinterior.1.1]
    nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 128) harg
  have hpow : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  simpa [lrLowKIdealL0, hpow] using hlog

lemma lrLowKNormalization_pos
    {point : CertificatePoint} (hinterior : LRHighShapeInterior point) :
    0 < lrLowKNormalization point := by
  unfold lrLowKNormalization
  exact div_pos
    (mul_pos hinterior.2.1.1 (by linarith [hinterior.2.2.1]))
    (by norm_num)

/-- End-to-end low-`k` region theorem, conditional only on the explicit
ideal replay and restoration certificates above. -/
theorem lrDeterminantLowKRegion_certificate_of_analyticData
    (ideal : LRLowKIdealReplayCertificate)
    (restoration : LRLowKRestorationCertificate) :
    LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion := by
  intro point hinterior hrelevant hregion
  have hL := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hk : point.k ∈ Ioc (0 : ℝ) 1 := by
    have hkPos : 0 < point.k := by
      have hePos := hinterior.2.1.1
      unfold lrCertificateE at hePos
      exact pos_of_mul_pos_left (by simpa [mul_comm] using hePos)
        hinterior.1.1.le
    exact ⟨hkPos, hregion.2.2⟩
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hLk : -Real.log point.k ≤ Real.log (1 / point.s) := by
    have hlogs : Real.log point.s ≤ Real.log point.k :=
      Real.log_le_log hinterior.1.1 hregion.2.1
    rw [one_div, Real.log_inv]
    linarith
  have hideal := lrLowKIdealCore_gt_nineteen_fiftieths
    ideal hL hLk hk hchi
  have hactual := lrLowK_margin_after_restoration hideal
    (restoration point hinterior hrelevant hregion)
  have hnormalized : 0 < lrLowKActualNormalized point := by
    norm_num at hactual ⊢
    linarith
  have hn := lrLowKNormalization_pos hinterior
  have hcleared : 0 < lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point) := by
    have hproduct := mul_pos hnormalized hn
    unfold lrLowKActualNormalized at hproduct
    rw [div_mul_cancel₀ _ hn.ne'] at hproduct
    exact hproduct
  exact Or.inr hcleared.le

end CourtadeKumar
