import InformationTheory.CourtadeKumar.TopNormalizedReserve
import InformationTheory.CourtadeKumar.TopPsiDerivativeCore

/-! Exact differentiation of the normalized corrected reserve along the
explicit TOP cap. -/

open Set

namespace CourtadeKumar

noncomputable def topChannelWDeriv (R : ℝ) : ℝ :=
  ((Real.log 2 - topPsiDeriv R) * (1 - R) +
      (R * Real.log 2 - topPhi (Real.sqrt R))) / (1 - R) ^ 2

noncomputable def topChannelKDeriv (R q : ℝ) : ℝ :=
  let N := R * topPhi (Real.sqrt q) -
    topPhi (Real.sqrt R * Real.sqrt q)
  let N' := topPhi (Real.sqrt q) -
    Real.artanh (Real.sqrt R * Real.sqrt q) *
      (Real.sqrt q / (2 * Real.sqrt R))
  (N' * ((1 - R) * q) + N * q) / (((1 - R) * q) ^ 2)

noncomputable def topCapRDeriv (c q : ℝ) : ℝ :=
  -2 * c * (1 - q) / (1 - c ^ 2 * q) ^ 2

noncomputable def topCapH (c q : ℝ) : ℝ :=
  topChannelH (topCapR c q) c q

/-- The exact negative derivative of the normalized reserve along the cap. -/
noncomputable def topCapJ (c q : ℝ) : ℝ :=
  let R := topCapR c q
  topChannelP c q + topChannelW R +
    topCapRDeriv c q *
      (c * topChannelWDeriv R - topChannelKDeriv R q)

/-- The common-primitive correction `B` in the manuscript, expressed
directly through the already differentiated channel functions. -/
noncomputable def topCapB (c q : ℝ) : ℝ :=
  let R := topCapR c q
  (1 - R) ^ 2 *
    (c * topChannelWDeriv R - topChannelKDeriv R q)

lemma hasDerivAt_topPsi {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ topPhi (Real.sqrt x)) (topPsiDeriv R) R := by
  have hsqrt := Real.hasDerivAt_sqrt hR.1.ne'
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hphi := (hasDerivAt_topPhi
    (show Real.sqrt R ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hsqrtLt⟩)).comp R hsqrt
  unfold topPsiDeriv
  convert hphi using 1
  field_simp [hsqrtPos.ne']

theorem hasDerivAt_topChannelW {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt topChannelW (topChannelWDeriv R) R := by
  have hnum := ((hasDerivAt_id R).mul_const (Real.log 2)).sub
    (hasDerivAt_topPsi hR)
  have hden := (hasDerivAt_const R 1).sub (hasDerivAt_id R)
  have hdenNe : 1 - R ≠ 0 := by linarith [hR.2]
  unfold topChannelW topChannelWDeriv
  convert hnum.div hden hdenNe using 1 <;>
    simp only [id_eq, Pi.sub_apply] <;> ring

theorem hasDerivAt_topChannelK {R q : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ topChannelK x q) (topChannelKDeriv R q) R := by
  have hsqrtR := Real.hasDerivAt_sqrt hR.1.ne'
  have hsqrtRPos := Real.sqrt_pos.2 hR.1
  have hsqrtRLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hsqrtqPos := Real.sqrt_pos.2 hq.1
  have hsqrtqLt : Real.sqrt q < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hq.1.le).2 hq.2
  have hprodPos : 0 < Real.sqrt R * Real.sqrt q :=
    mul_pos hsqrtRPos hsqrtqPos
  have hprodLt : Real.sqrt R * Real.sqrt q < 1 := by
    have hfirst : Real.sqrt R * Real.sqrt q < Real.sqrt R := by
      simpa using mul_lt_mul_of_pos_left hsqrtqLt hsqrtRPos
    exact hfirst.trans hsqrtRLt
  have harg := hsqrtR.mul_const (Real.sqrt q)
  have hphiArg := (hasDerivAt_topPhi
    (show Real.sqrt R * Real.sqrt q ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith, hprodLt⟩)).comp R harg
  have hlinear := (hasDerivAt_id R).mul_const (topPhi (Real.sqrt q))
  have hnum := hlinear.sub hphiArg
  have hden := ((hasDerivAt_const R 1).sub (hasDerivAt_id R)).mul_const q
  have hdenNe : (1 - R) * q ≠ 0 :=
    mul_ne_zero (by linarith [hR.2]) hq.1.ne'
  unfold topChannelK topChannelKDeriv
  dsimp only
  convert hnum.div hden hdenNe using 1
  simp only [id_eq, Pi.sub_apply, Function.comp_apply]
  field_simp [hsqrtRPos.ne', hq.1.ne', sub_ne_zero.mpr hR.2.ne]
  ring

theorem hasDerivAt_topCapR {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ ↦ topCapR u q) (topCapRDeriv c q) c := by
  have hid := hasDerivAt_id c
  have hsq : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * c) c := by
    convert hid.pow 2 using 1 <;> simp only [id_eq] <;> ring
  have hnum := (hasDerivAt_const c 1).sub hsq
  have hden := (hasDerivAt_const c 1).sub (hsq.mul_const q)
  have hdenNe := (topCapDen_pos hc hq).ne'
  unfold topCapR topCapRDeriv
  convert hnum.div hden hdenNe using 1
  simp only [Pi.sub_apply]
  field_simp [hdenNe]
  ring

lemma one_sub_topCapR {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    1 - topCapR c q = c ^ 2 * (1 - q) / (1 - c ^ 2 * q) := by
  have hden := (topCapDen_pos hc hq).ne'
  unfold topCapR
  field_simp [hden]
  ring

lemma topCapRDeriv_eq_scale {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapRDeriv c q =
      -2 * (1 - topCapR c q) / (c * (1 - c ^ 2 * q)) := by
  have hcne := hc.1.ne'
  have hden := (topCapDen_pos hc hq).ne'
  rw [one_sub_topCapR hc hq]
  unfold topCapRDeriv
  field_simp [hcne, hden]

/-- Exact common-primitive form of the cap derivative loss. -/
theorem topCapJ_eq_B {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapJ c q =
      topChannelP c q + topChannelW (topCapR c q) -
        2 * topCapB c q / (c ^ 3 * (1 - q)) := by
  have hcne := hc.1.ne'
  have hqne : 1 - q ≠ 0 := by linarith [hq.2]
  have hden := (topCapDen_pos hc hq).ne'
  have hs : 1 - topCapR c q ≠ 0 := by
    rw [one_sub_topCapR hc hq]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hcne) hqne) hden
  unfold topCapJ topCapB
  dsimp only
  rw [topCapRDeriv_eq_scale hc hq, one_sub_topCapR hc hq]
  field_simp [hcne, hqne, hden, hs]
  ring

/-- The named quantity `topCapJ` is exactly the negative derivative of the
normalized reserve along the moving cap. -/
theorem hasDerivAt_topCapH {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ ↦ topCapH u q) (-topCapJ c q) c := by
  have hR := topCapR_mem_Ioo hc hq
  have hcapR := hasDerivAt_topCapR hc hq
  have hQ := hasDerivAt_topNormalizedQ hc hq
  have hW := (hasDerivAt_topChannelW hR).comp c hcapR
  have hK := (hasDerivAt_topChannelK hR hq).comp c hcapR
  have hlinear := (hasDerivAt_id c).mul hW
  have htotal := (hQ.sub hlinear).add hK
  unfold topCapH topChannelH topCapJ
  dsimp only
  convert htotal using 1 <;>
    simp only [id_eq, Function.comp_apply] <;> ring

@[simp] theorem topCapH_one (q : ℝ) :
    topCapH 1 q = 0 := by
  have hR : topCapR 1 q = 0 := by
    unfold topCapR
    simp
  have hQ : topNormalizedQ 1 q = 0 := by
    have hp : topPerspectiveTerm 1 (Real.sqrt q) = 0 := by
      norm_num [topPerspectiveTerm]
    unfold topNormalizedQ
    rw [hp]
    simp
  have hW : topChannelW 0 = 0 := by
    simp [topChannelW]
  have hK : topChannelK 0 q = 0 := by
    simp [topChannelK]
  unfold topCapH topChannelH
  rw [hR, hQ, hW, hK]
  ring

end CourtadeKumar
