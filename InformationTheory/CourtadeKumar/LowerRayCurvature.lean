import InformationTheory.CourtadeKumar.ChannelCap
import InformationTheory.CourtadeKumar.RadialDerivative

/-! Concavity of the one-ray lower-bound gap. -/

open Set

namespace CourtadeKumar

/-- A convenient consequence of the channel-cap estimate. -/
theorem topEll_le_rho_sq_div_four
    {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    topEll rho ≤ rho ^ 2 / 4 := by
  have hS : 0 < topS rho := by
    unfold topS topR
    nlinarith [mul_pos (sub_pos.2 hrho.2) (by linarith [hrho.1] : 0 < 1 + rho)]
  have hlog := Real.one_sub_inv_le_log_of_pos hS
  have hscaled := mul_le_mul_of_nonneg_left hlog hS.le
  have hcap := topEll_le_channelCap
    (show rho ∈ Icc (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2.le⟩)
  have haux : -(topS rho) * Real.log (topS rho) ≤ rho ^ 2 := by
    have hid : topS rho * (1 - (topS rho)⁻¹) = topS rho - 1 := by
      field_simp [hS.ne']
    rw [hid] at hscaled
    unfold topS topR at hscaled ⊢
    nlinarith
  calc
    topEll rho ≤ -(topS rho) / 4 * Real.log (topS rho) := hcap
    _ ≤ rho ^ 2 / 4 := by nlinarith

noncomputable def lowerRayNatEnvelope (rho m : ℝ) : ℝ :=
  topS rho * Real.binEntropy m +
    4 * topEll rho * m * (1 - m)

noncomputable def lowerRayGap (rho m : ℝ) : ℝ :=
  radialNatEntropy rho 1 m - lowerRayNatEnvelope rho m

noncomputable def lowerRayGapDeriv (rho m : ℝ) : ℝ :=
  radialNatEntropyDeriv rho 1 m -
    topS rho * (Real.log (1 - m) - Real.log m) -
    4 * topEll rho * (1 - 2 * m)

noncomputable def radialNatEntropyDeriv2 (c r z : ℝ) : ℝ :=
  -((1 - c * r) / (z * (1 - (1 - c * r) * z)) +
      (1 + c * r) / (z * (1 - (1 + c * r) * z))) / 2

noncomputable def lowerRayGapDeriv2 (rho m : ℝ) : ℝ :=
  radialNatEntropyDeriv2 rho 1 m +
    topS rho / (m * (1 - m)) + 8 * topEll rho

theorem hasDerivAt_lowerRayGap
    {rho m : ℝ}
    (hminus : (1 - rho) * m ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + rho) * m ∈ Ioo (0 : ℝ) 1)
    (hm : m ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lowerRayGap rho) (lowerRayGapDeriv rho m) m := by
  have hradial := hasDerivAt_radialNatEntropy
    (c := rho) (r := (1 : ℝ)) (z := m)
    (by simpa using hminus) (by simpa using hplus)
  have hentropy := Real.hasDerivAt_binEntropy hm.1.ne' hm.2.ne
  have hquadratic : HasDerivAt (fun x : ℝ ↦ x * (1 - x))
      (1 - 2 * m) m := by
    convert (hasDerivAt_id m).mul
      ((hasDerivAt_const m 1).sub (hasDerivAt_id m)) using 1 <;>
      simp [id_eq] <;> ring
  have henvelope := (hentropy.const_mul (topS rho)).add
    (hquadratic.const_mul (4 * topEll rho))
  unfold lowerRayGap lowerRayGapDeriv lowerRayNatEnvelope
  change HasDerivAt
    (fun x ↦ radialNatEntropy rho 1 x -
      (topS rho * Real.binEntropy x + 4 * topEll rho * x * (1 - x)))
    _ m
  convert hradial.sub henvelope using 1
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · ring

theorem hasDerivAt_radialNatEntropyDeriv
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatEntropyDeriv c r)
      (radialNatEntropyDeriv2 c r z) z := by
  let A : ℝ := 1 - c * r
  let B : ℝ := 1 + c * r
  have hz : z ≠ 0 := by
    intro hz
    subst z
    norm_num at hminus
  have hA : A ≠ 0 := by
    intro hA
    have : A * z = 0 := by rw [hA, zero_mul]
    linarith [hminus.1]
  have hB : B ≠ 0 := by
    intro hB
    have : B * z = 0 := by rw [hB, zero_mul]
    linarith [hplus.1]
  have hOneA : 1 - A * z ≠ 0 := by linarith [hminus.2]
  have hOneB : 1 - B * z ≠ 0 := by linarith [hplus.2]
  have hAz : HasDerivAt (fun w : ℝ ↦ A * w) A z := by
    simpa [id_eq] using (hasDerivAt_id z).const_mul A
  have hBz : HasDerivAt (fun w : ℝ ↦ B * w) B z := by
    simpa [id_eq] using (hasDerivAt_id z).const_mul B
  have hOneAz : HasDerivAt (fun w : ℝ ↦ 1 - A * w) (-A) z := by
    convert (hasDerivAt_const z 1).sub hAz using 1 <;> simp
  have hOneBz : HasDerivAt (fun w : ℝ ↦ 1 - B * w) (-B) z := by
    convert (hasDerivAt_const z 1).sub hBz using 1 <;> simp
  have hlogOneA := (Real.hasDerivAt_log hOneA).comp z hOneAz
  have hlogA := (Real.hasDerivAt_log (mul_ne_zero hA hz)).comp z hAz
  have hlogOneB := (Real.hasDerivAt_log hOneB).comp z hOneBz
  have hlogB := (Real.hasDerivAt_log (mul_ne_zero hB hz)).comp z hBz
  have hleft := (hlogOneA.sub hlogA).const_mul A
  have hright := (hlogOneB.sub hlogB).const_mul B
  have htotal := (hleft.add hright).div_const 2
  have hleftValue :
      A * ((1 - A * z)⁻¹ * -A - (A * z)⁻¹ * A) =
        -A / (z * (1 - A * z)) := by
    field_simp [hz, hA, hOneA]
    ring
  have hrightValue :
      B * ((1 - B * z)⁻¹ * -B - (B * z)⁻¹ * B) =
        -B / (z * (1 - B * z)) := by
    field_simp [hz, hB, hOneB]
    ring
  dsimp [A, B] at hminus hplus htotal ⊢
  unfold radialNatEntropyDeriv radialNatEntropyDeriv2
  convert htotal using 1
  dsimp [A, B] at hleftValue hrightValue
  rw [hleftValue, hrightValue]
  ring

theorem hasDerivAt_lowerRayGapDeriv
    {rho m : ℝ}
    (hminus : (1 - rho) * m ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + rho) * m ∈ Ioo (0 : ℝ) 1)
    (hm : m ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lowerRayGapDeriv rho)
      (lowerRayGapDeriv2 rho m) m := by
  have hradial := hasDerivAt_radialNatEntropyDeriv
    (c := rho) (r := (1 : ℝ)) (z := m)
    (by simpa using hminus) (by simpa using hplus)
  have hOne : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) m := by
    simpa [id_eq] using (hasDerivAt_const m 1).sub (hasDerivAt_id m)
  have hOneNe : 1 - m ≠ 0 := by linarith [hm.2]
  have hlogOne := (Real.hasDerivAt_log hOneNe).comp m hOne
  have hlog := Real.hasDerivAt_log hm.1.ne'
  have hslope := hlogOne.sub hlog |>.const_mul (topS rho)
  have hlinear : HasDerivAt (fun x : ℝ ↦ 1 - 2 * x) (-2) m := by
    convert (hasDerivAt_const m 1).sub ((hasDerivAt_id m).const_mul 2) using 1 <;>
      simp
  have hquadratic := hlinear.const_mul (4 * topEll rho)
  unfold lowerRayGapDeriv lowerRayGapDeriv2
  convert (hradial.sub hslope).sub hquadratic using 1
  field_simp [hm.1.ne', hm.2.ne]
  ring

lemma lowerRay_entropyArgs
    {rho m : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hm : m ∈ Ioo (0 : ℝ) (1 / 2)) :
    (1 - rho) * m ∈ Ioo (0 : ℝ) 1 ∧
      (1 + rho) * m ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · constructor
    · exact mul_pos (sub_pos.2 hrho.2) hm.1
    · calc
        (1 - rho) * m < 1 * m :=
          mul_lt_mul_of_pos_right (by linarith [hrho.1]) hm.1
        _ < 1 := by linarith [hm.2]
  · constructor
    · exact mul_pos (by linarith [hrho.1]) hm.1
    · calc
        (1 + rho) * m < 2 * m :=
          mul_lt_mul_of_pos_right (by linarith [hrho.2]) hm.1
        _ < 1 := by linarith [hm.2]

theorem lowerRayGapDeriv2_nonpos
    {rho m : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hm : m ∈ Ioo (0 : ℝ) (1 / 2)) :
    lowerRayGapDeriv2 rho m ≤ 0 := by
  let S : ℝ := topS rho
  let D : ℝ := 1 - 2 * m + S * m ^ 2
  let N : ℝ := 1 - m + S * m ^ 2
  have hS : 0 < S := by
    dsimp [S]
    unfold topS topR
    nlinarith [mul_pos (sub_pos.2 hrho.2)
      (by linarith [hrho.1] : 0 < 1 + rho)]
  obtain ⟨hminus, hplus⟩ := lowerRay_entropyArgs hrho hm
  have hminusDen : 0 < 1 - (1 - rho) * m := by linarith [hminus.2]
  have hplusDen : 0 < 1 - (1 + rho) * m := by linarith [hplus.2]
  have hminusDen' : 1 - m + rho * m ≠ 0 := by
    nlinarith [hminusDen]
  have hplusDen' : 1 - m - rho * m ≠ 0 := by
    nlinarith [hplusDen]
  have hminusDen'' : 1 + (rho * m - m) ≠ 0 := by
    nlinarith [hminusDen]
  have hplusDen'' : 1 + (-(rho * m) - m) ≠ 0 := by
    nlinarith [hplusDen]
  have hDfactor : D =
      (1 - (1 - rho) * m) * (1 - (1 + rho) * m) := by
    dsimp [D, S]
    unfold topS topR
    ring
  have hD : 0 < D := by
    rw [hDfactor]
    exact mul_pos hminusDen hplusDen
  have hden : 0 < m * (1 - m) * D :=
    mul_pos (mul_pos hm.1 (by linarith [hm.2])) hD
  have hDexp : 0 < 1 - 2 * m + (1 - rho ^ 2) * m ^ 2 := by
    simpa [D, S, topS, topR] using hD
  have hsum :
      (1 - rho) / (1 - (1 - rho) * m) +
          (1 + rho) / (1 - (1 + rho) * m) =
        2 * (1 - S * m) / D := by
    rw [div_add_div (1 - rho) (1 + rho) hminusDen.ne' hplusDen.ne']
    rw [← hDfactor]
    congr 1
    dsimp [S]
    unfold topS topR
    ring
  have hfactor : radialNatEntropyDeriv2 rho 1 m =
      -(1 / (2 * m)) *
        ((1 - rho) / (1 - (1 - rho) * m) +
          (1 + rho) / (1 - (1 + rho) * m)) := by
    unfold radialNatEntropyDeriv2
    field_simp [hm.1.ne', hminusDen.ne', hplusDen.ne']
  have hradialFormula : radialNatEntropyDeriv2 rho 1 m =
      -(1 - S * m) / (m * D) := by
    rw [hfactor, hsum]
    field_simp [hm.1.ne']
  have hformula : lowerRayGapDeriv2 rho m =
      -(rho ^ 2 * N / (m * (1 - m) * D)) + 8 * topEll rho := by
    rw [lowerRayGapDeriv2, hradialFormula]
    field_simp [hm.1.ne', (by linarith [hm.2] : 1 - m ≠ 0), hD.ne']
    dsimp [N, D, S]
    unfold topS topR
    ring
  have hcoef : 0 ≤ 2 * m * (1 - m) ∧ 2 * m * (1 - m) ≤ 1 := by
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) hm.1.le)
        (by linarith [hm.2] : 0 ≤ 1 - m)
    · nlinarith [hm.1, hm.2, sq_nonneg (m - 1 / 2)]
  have hDN : D ≤ N := by
    dsimp [D, N]
    linarith [hm.1]
  have hcore : 2 * m * (1 - m) * D ≤ N := by
    calc
      2 * m * (1 - m) * D ≤ 1 * D :=
        mul_le_mul_of_nonneg_right hcoef.2 hD.le
      _ = D := one_mul D
      _ ≤ N := hDN
  have hfraction : 2 * rho ^ 2 ≤
      rho ^ 2 * N / (m * (1 - m) * D) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hcore (sq_nonneg rho)]
  have hell : 8 * topEll rho ≤ 2 * rho ^ 2 := by
    nlinarith [topEll_le_rho_sq_div_four hrho]
  rw [hformula]
  linarith

@[simp] theorem lowerRayGap_zero (rho : ℝ) : lowerRayGap rho 0 = 0 := by
  simp [lowerRayGap, lowerRayNatEnvelope, radialNatEntropy,
    Real.binEntropy_zero]

@[simp] theorem lowerRayGap_half (rho : ℝ) :
    lowerRayGap rho (1 / 2) = 0 := by
  have hsym : Real.binEntropy ((1 + rho) / 2) =
      Real.binEntropy ((1 - rho) / 2) := by
    rw [← Real.binEntropy_one_sub]
    congr 1
    ring
  unfold lowerRayGap lowerRayNatEnvelope radialNatEntropy
    topS topR topEll topPhi
  rw [show (1 - rho * 1) * (1 / 2) = (1 - rho) / 2 by ring,
    show (1 + rho * 1) * (1 / 2) = (1 + rho) / 2 by ring,
    hsym]
  have hhalf : Real.binEntropy (1 / 2) = Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.binEntropy_two_inv]
  rw [hhalf]
  unfold topR
  ring

theorem lowerRayGap_concaveOn
    {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) (1 / 2)) (lowerRayGap rho) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (convex_Icc (0 : ℝ) (1 / 2))
  · unfold lowerRayGap lowerRayNatEnvelope radialNatEntropy
    fun_prop
  · intro m hm
    rw [interior_Icc] at hm
    obtain ⟨hminus, hplus⟩ := lowerRay_entropyArgs hrho hm
    exact (hasDerivAt_lowerRayGap hminus hplus
      ⟨hm.1, hm.2.trans (by norm_num)⟩).hasDerivWithinAt
  · intro m hm
    rw [interior_Icc] at hm
    obtain ⟨hminus, hplus⟩ := lowerRay_entropyArgs hrho hm
    exact (hasDerivAt_lowerRayGapDeriv hminus hplus
      ⟨hm.1, hm.2.trans (by norm_num)⟩).hasDerivWithinAt
  · intro m hm
    rw [interior_Icc] at hm
    exact lowerRayGapDeriv2_nonpos hrho hm

theorem lowerRayGap_nonneg
    {rho m : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hm : m ∈ Icc (0 : ℝ) (1 / 2)) :
    0 ≤ lowerRayGap rho m := by
  have hconcave := lowerRayGap_concaveOn hrho
  have ha : 0 ≤ (1 - 2 * m : ℝ) := by linarith [hm.2]
  have hb : 0 ≤ (2 * m : ℝ) := by nlinarith [hm.1]
  have hab : (1 - 2 * m : ℝ) + 2 * m = 1 := by ring
  have h := hconcave.2
    (show (0 : ℝ) ∈ Icc 0 (1 / 2) by norm_num)
    (show (1 / 2 : ℝ) ∈ Icc 0 (1 / 2) by norm_num)
    ha hb hab
  simp only [smul_eq_mul, lowerRayGap_zero, lowerRayGap_half,
    mul_zero, add_zero] at h
  convert h using 1
  ring

end CourtadeKumar
