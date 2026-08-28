import InformationTheory.CourtadeKumar.LRDeterminantWronskianResummation

/-!
# Concrete radial series for the determinant Wronskian

This file identifies all four abstract series in the Wronskian resummation
with the analytic quantities of the audited determinant proof.  In
particular, it proves the full analytic Wronskian inequality from the finite
coefficient theorem.
-/

open Set

namespace CourtadeKumar

/-- Generating-function identity for a sequence of tails satisfying
`p_n = d_{n+1} + p_{n+1}`. -/
theorem lrTailGeneratingFunction_hasSum
    {R Q : ℝ} {p d : ℕ → ℝ}
    (hR : R < 1)
    (hp : Summable (fun n : ℕ => p (n + 1) * R ^ (n + 1)))
    (hrec : ∀ n, p n = d (n + 1) + p (n + 1))
    (hd : HasSum (fun n : ℕ => d (n + 1) * R ^ (n + 1)) Q) :
    HasSum (fun n : ℕ => p (n + 1) * R ^ (n + 1))
      ((R * p 0 - Q) / (1 - R)) := by
  let f : ℕ → ℝ := fun n => p (n + 1) * R ^ (n + 1)
  let S : ℝ := ∑' n : ℕ, f n
  have hf : HasSum f S := by
    exact (show Summable f by simpa [f] using hp).hasSum
  let shifted : ℕ → ℝ
    | 0 => 0
    | n + 1 => R * f n
  have hshift : HasSum shifted (R * S) := by
    simpa [shifted] using lr_hasSum_power_shift f R S hf
  have hdiff := hf.sub hshift
  have hhead := hasSum_ite_eq (0 : ℕ) (R * p 0)
  have halt := hhead.sub hd
  have hterms : ∀ n : ℕ,
      f n - shifted n =
        (if n = 0 then R * p 0 else 0) - d (n + 1) * R ^ (n + 1) := by
    intro n
    rcases n with _ | n
    · simp [f, shifted]
      have h := hrec 0
      ring_nf at h ⊢
      nlinarith
    · simp only [f, shifted, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte]
      have h := hrec (n + 1)
      rw [pow_succ R (n + 1)]
      linear_combination -(R ^ (n + 1) * R) * h
  have hvalue : S - R * S = R * p 0 - Q := by
    exact hdiff.unique (halt.congr_fun fun n => hterms n)
  have hden : 1 - R ≠ 0 := sub_ne_zero.mpr hR.ne'
  have hS : S = (R * p 0 - Q) / (1 - R) := by
    rw [eq_div_iff hden]
    nlinarith
  simpa [f, hS] using hf

theorem lrLowB_radial_summable
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    Summable (fun n : ℕ => lrLowB (n + 1) * R ^ (n + 1)) := by
  have hgeom : Summable (fun n : ℕ => Real.log 2 * R ^ (n + 1)) := by
    have hnorm : ‖R‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hR.1]
      exact hR.2
    exact ((summable_geometric_of_norm_lt_one hnorm).mul_left
      (Real.log 2)).mul_right R |>.congr (fun n => by rw [pow_succ]; ring)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (lrLowB_pos _).le (pow_nonneg hR.1.le _)) _ hgeom
  intro n
  exact mul_le_mul_of_nonneg_right (lrLowB_le_log_two _)
    (pow_nonneg hR.1.le _)

/-- The radial tail coefficients `b_j` sum to normalized endpoint energy. -/
theorem lrLowB_radial_hasSum
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => lrLowB (n + 1) * R ^ (n + 1))
      (lrNormalizedEnergy R 1) := by
  have hd0 := topPhi_sqrt_hasSum hR
  have hd : HasSum (fun n : ℕ => lrLowA (n + 1) * R ^ (n + 1))
      (topPhi (Real.sqrt R)) := by
    convert hd0 using 1
    funext n
    unfold lrLowA
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have h := lrTailGeneratingFunction_hasSum hR.2
    (lrLowB_radial_summable hR) lrLowB_recursion hd
  convert h using 1
  unfold lrNormalizedEnergy lrLowB
  rw [topPhi_one]
  simp

theorem lrLowP_radial_summable
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Summable (fun n : ℕ =>
      lrLowP v (t ^ 2) (n + 1) * R ^ (n + 1)) := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have htClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hb := (lrLowB_radial_summable hR).mul_left 2
  apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by
        rw [← (lrLowP_hasSum hvClosed htClosed (n + 1)).tsum_eq]
        exact tsum_nonneg fun k => mul_nonneg
          (lrLowA_pos (by omega)).le
          (lrLowT_nonneg hvClosed.1 htClosed.1 _))
        (pow_nonneg hR.1.le _)) _ hb
  intro n
  have hp := lrLowP_le_first_mul_B hvClosed htClosed (n + 1)
  have hT := lrLowT_le_two hvClosed htClosed (n + 2)
  have hpBound : lrLowP v (t ^ 2) (n + 1) ≤ 2 * lrLowB (n + 1) :=
    hp.trans (mul_le_mul_of_nonneg_right hT (lrLowB_pos _).le)
  have hpow := pow_nonneg hR.1.le (n + 1)
  nlinarith [mul_le_mul_of_nonneg_right hpBound hpow]

/-- The radial weighted tails `p_j` sum to the two normalized channel
energies in the determinant proof. -/
theorem lrLowP_radial_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ =>
      lrLowP v (t ^ 2) (n + 1) * R ^ (n + 1))
      (lrNormalizedEnergy R t + lrNormalizedEnergy R (v * t) / v) := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have htClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  let rt : ℝ := Real.sqrt R * t
  have hsqrt : Real.sqrt R ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hR.1
    · simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hrt : rt ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rt]
    constructor
    · exact mul_pos hsqrt.1 ht.1
    · calc
        Real.sqrt R * t < 1 * t := mul_lt_mul_of_pos_right hsqrt.2 ht.1
        _ < 1 := by simpa using ht.2
  have hrtSq : rt ^ 2 = R * t ^ 2 := by
    dsimp [rt]
    rw [mul_pow, Real.sq_sqrt hR.1.le]
  have hrtClosed : rt ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg hrt.1.le (sub_nonneg.mpr hrt.2.le)]
  have hd0 := lrLowP_hasSum hvClosed hrtClosed 0
  have hd : HasSum (fun n : ℕ =>
      lrLowA (n + 1) * lrLowT v (t ^ 2) (n + 1) * R ^ (n + 1))
      (topPhi rt + topPhi (v * rt) / v) := by
    rw [← lrLowP_zero_eq_phi hv ⟨hrt.1, hrt.2.le⟩]
    convert hd0 using 1
    funext n
    unfold lrLowT
    rw [hrtSq, mul_pow]
    ring
  have h := lrTailGeneratingFunction_hasSum
    (R := R)
    (Q := topPhi rt + topPhi (v * rt) / v)
    (p := fun j => lrLowP v (t ^ 2) j)
    (d := fun j => lrLowA j * lrLowT v (t ^ 2) j)
    hR.2 (lrLowP_radial_summable hR hv ht)
    (fun n => lrLowP_recursion hvClosed htClosed n) hd
  convert h using 1
  unfold lrNormalizedEnergy
  change _ =
    (R * lrLowP v (t ^ 2) 0 - (topPhi rt + topPhi (v * rt) / v)) /
      (1 - R)
  rw [lrLowP_zero_eq_phi hv ⟨ht.1, ht.2.le⟩]
  dsimp [rt]
  have hden : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  field_simp [hden, hv.1.ne']
  ring

theorem lrDeterminantHSeries_hasSum
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ =>
      lrWronskianHSeriesCoefficient (lrLowHalfSlopeBase v)
        lrDeterminantRadialC n * R ^ n)
      (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1) := by
  let hseq : ℕ → ℝ := fun n =>
    lrWronskianHSeriesCoefficient (lrLowHalfSlopeBase v)
      lrDeterminantRadialC n * R ^ n
  have htail : HasSum (fun n : ℕ => hseq (n + 1))
      (4 * lrNormalizedEnergy R 1) := by
    convert (lrLowB_radial_hasSum hR).mul_left 4 using 1
    funext n
    simp [hseq, lrWronskianHSeriesCoefficient, lrDeterminantRadialC]
    ring
  have hfull := (hasSum_nat_add_iff (f := hseq) 1).mp htail
  simpa [hseq, lrWronskianHSeriesCoefficient, add_comm] using hfull

theorem lrDeterminantHDerivativeSeries_hasSum
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ =>
      lrWronskianHDerivativeSeriesCoefficient lrDeterminantRadialC n * R ^ n)
      (4 * lrWKernel R 1 / (1 - R) ^ 2) := by
  convert (lrLowB_derivative_hasSum hR).mul_left 4 using 1
  · funext n
    unfold lrWronskianHDerivativeSeriesCoefficient lrDeterminantRadialC
    ring
  · ring

theorem lrDeterminantFSeries_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ =>
      lrWronskianFSeriesCoefficient (lrDeterminantRadialF v t) n * R ^ n)
      (lrFlowGap R v t / (1 - R)) := by
  have hnorm : ‖R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hR.1]
    exact hR.2
  have hg : HasSum (fun n : ℕ => lrGShape t v * R ^ (n + 1))
      (lrGShape t v * R / (1 - R)) := by
    convert (hasSum_geometric_of_norm_lt_one hnorm).mul_left
      (lrGShape t v * R) using 1
    funext n
    rw [pow_succ]
    ring
  have hp := lrLowP_radial_hasSum hR hv ht
  have hb := (lrLowB_radial_hasSum hR).mul_left (4 / (1 + v))
  have hradial : HasSum (fun n : ℕ =>
      lrDeterminantRadialF v t (n + 1) * R ^ (n + 1))
      (lrFlowGap R v t / (1 - R)) := by
    have htotal := hg.add hp |>.sub hb
    convert htotal using 1
    · funext n
      unfold lrDeterminantRadialF
      ring
    · have hM : lrFlowM v ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := by
        unfold lrFlowM
        constructor
        · exact div_pos hv.1 (by linarith [hv.1])
        · rw [div_lt_iff₀ (by linarith [hv.1] : 0 < 1 + v)]
          linarith [hv.2]
      have hodds : lrProbabilityToOdds (lrFlowM v) = v := by
        unfold lrProbabilityToOdds lrFlowM
        have hden : 1 + v ≠ 0 := by linarith [hv.1]
        field_simp [hden]
        ring
      have hpref := lrPrefixEll_eq_lrObjectiveTarget hR hM
      rw [hodds] at hpref
      have hsquare := lrSquareObjective_eq (R := R) (u := v) hR
      have hprefSquare : lrPrefixEll R (lrFlowM v) = lrSquareObjective R v :=
        hpref.trans hsquare.symm
      unfold lrFlowGap
      rw [hprefSquare]
      unfold lrSquareTarget lrSquareObjective lrGShape lrNormalizedEnergy
      rw [show v * (Real.sqrt R * t) = Real.sqrt R * (v * t) by ring]
      rw [topPhi_one]
      have hdenR : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
      have hdenV : 1 + v ≠ 0 := by linarith [hv.1]
      field_simp [hdenR, hdenV]
      ring
  let fseq : ℕ → ℝ := fun n =>
    lrWronskianFSeriesCoefficient (lrDeterminantRadialF v t) n * R ^ n
  have htail : HasSum (fun n : ℕ => fseq (n + 1))
      (lrFlowGap R v t / (1 - R)) := by
    simpa [fseq, lrWronskianFSeriesCoefficient] using hradial
  have hfull := (hasSum_nat_add_iff (f := fseq) 1).mp htail
  simpa [fseq, lrWronskianFSeriesCoefficient] using hfull

theorem lrDeterminantFDerivativeSeries_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ =>
      lrWronskianFDerivativeSeriesCoefficient
        (lrDeterminantRadialF v t) n * R ^ n)
      (lrFlowC R v t / (1 - R) ^ 2) := by
  simpa [lrWronskianFDerivativeSeriesCoefficient, lrLowFDerivCoeff,
    lrDeterminantRadialF] using lrLowFDerivCoeff_hasSum hR hv ht

/-- The concrete analytic Wronskian inequality from the audited determinant
proof, obtained by resumming its nonnegative coefficients. -/
theorem lrDeterminantWronskian_nonnegative
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤
      (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1) *
          (lrFlowC R v t / (1 - R) ^ 2) -
        (4 * Real.log 2) * (4 * lrWKernel R 1 / (1 - R) ^ 2) *
          (lrFlowGap R v t / (1 - R)) := by
  exact lrWronskian_nonnegative_of_hasSum hR.1.le
    (lrDeterminantHSeries_hasSum hR)
    (lrDeterminantHDerivativeSeries_hasSum hR)
    (lrDeterminantFSeries_hasSum hR hv ht)
    (lrDeterminantFDerivativeSeries_hasSum hR hv ht)
    (lrDeterminantConcreteWronskianCoefficient_nonnegative hv ht)

/-- Certificate-coordinate form of the analytic Wronskian bound (D3). -/
theorem lrCertificateDeterminantWronskian
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    12 * Real.log 2 * lrDeterminantC0 point * lrDeterminantT point ≤
      lrDeterminantPsi point := by
  let R := lrCertificateR point
  let v := lrCertificateV point
  let t := lrCertificateT point
  have hs : 0 < point.s := hinterior.1.1
  have hR : R ∈ Ioo (0 : ℝ) 1 := by
    dsimp [R, lrCertificateR]
    constructor <;> linarith [hinterior.1.2]
  have hv : v ∈ Ioo (0 : ℝ) 1 := by
    simpa [v] using lrCertificateV_mem_Ioo hinterior
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    simpa [t] using lrCertificateT_mem_Ioo hinterior
  have hwr := lrDeterminantWronskian_nonnegative hR hv ht
  have hW : lrCertificateW point = lrWKernel R 1 := by
    simpa [R] using lrCertificateW_eq_lrWKernel hinterior.1
  have hPW : lrCertificatePW point = lrFlowPW R v t := by
    simpa [R, v, t] using lrCertificatePW_eq_lrFlowPW
      hinterior.1 hinterior.2.1
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hG : lrCertificateGShape point = lrGShape t v := by
    simpa [v, t] using lrCertificateGShape_eq_lrGShape
      hinterior.2.1 ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hgap : lrCertificateGap point = lrFlowGap R v t := by
    simpa [R, v, t] using lrCertificateGap_eq_flow
      hinterior.1 hinterior.2.1
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hhalf : lrCertificateHalfSlope point = lrFlowHalfSlope R v := by
    simpa [R, v] using lrCertificateHalfSlope_eq_flow
      hinterior.1 hinterior.2.1
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hscale : 1 - R = point.s := by
    dsimp [R, lrCertificateR]
    ring
  have hHd : lrDeterminantHd point =
      lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1 := by
    unfold lrDeterminantHd
    rw [hhalf, lrFlowHalfSlope_eq_normalized hR.2.ne]
    rw [hscale]
    field_simp [hs.ne']
  have hPsi : lrDeterminantPsi point = lrFlowC R v t := by
    unfold lrDeterminantPsi lrFlowC
    rw [hG, hPW, hW]
  rw [hPsi]
  unfold lrDeterminantC0 lrDeterminantT
  rw [hW, hgap, hHd]
  change
    12 * Real.log 2 *
          (4 * R * lrWKernel R 1 /
            (3 * point.s *
              (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1))) *
          (lrFlowGap R v t / R) ≤
      lrFlowC R v t
  have hHdPos : 0 < lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1 := by
    rw [← hHd]
    exact lrDeterminantHd_pos hinterior
  have hdenR : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  have hR0 : R ≠ 0 := hR.1.ne'
  rw [← hscale]
  have hlhs :
      12 * Real.log 2 *
            (4 * R * lrWKernel R 1 /
              (3 * (1 - R) *
                (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1))) *
            (lrFlowGap R v t / R) =
        16 * Real.log 2 * lrWKernel R 1 * lrFlowGap R v t /
          ((1 - R) *
            (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1)) := by
    field_simp [hdenR, hR0]
    ring
  rw [hlhs, div_le_iff₀ (mul_pos (sub_pos.mpr hR.2) hHdPos)]
  field_simp [hdenR] at hwr
  have hnum := mul_nonneg hwr (pow_nonneg (sub_pos.mpr hR.2).le 3)
  field_simp [hdenR] at hnum
  nlinarith

/-- The D3 coefficient sign is now unconditional on every regular
certificate interior point. -/
theorem lrCertificateDeterminantCoefficient_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrDeterminantPsi point / lrCertificateGShape point -
      lrDeterminantC0 point *
        (lrDeterminantT point / lrCertificateGShape point) := by
  exact lrDeterminantCoefficient_nonnegative_of_wronskian hinterior
    (lrCertificateDeterminantWronskian hinterior)

/-- After the analytic Wronskian is discharged, the first-bracket ledger is
the only substantive input remaining in the determinant sign chain. -/
theorem lrCertificateTTarget_nonnegative_of_firstBracket_analytic
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hfirst : 0 ≤ lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)) :
    0 ≤ lrCertificateTTarget point := by
  exact lrCertificateTTarget_nonnegative_of_firstBracket_core
    hinterior hrelevant
    (lrCertificateDeterminantCoefficient_nonnegative hinterior) hfirst

end CourtadeKumar
