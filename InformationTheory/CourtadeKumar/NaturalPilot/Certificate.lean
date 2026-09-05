import InformationTheory.CourtadeKumar.NaturalPilot.ScalarAssembly
import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore

/-!
# Production first-bracket certificate for the natural-interval pilot

The scalar definitions are the unchanged production declarations relocated
to a lightweight core. This module closes the formula-identification step;
its final theorem states the actual LRDeterminantFirstBracketAt predicate.
It covers only the specified box, not the whole fixed16 region.
-/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalProductionPilot
open RationalEnclosure RootRatioBaseFaceD1Standalone RootRatioBaseFaceBStandalone
open RootRatioNaturalGeometry RootRatioNaturalComponents

theorem b_eq (p : CertificatePoint) : bValue p.s p.k p.chi = lrCertificateBFlow p := rfl
theorem v_eq (p : CertificatePoint) : vValue p.s p.k p.chi = lrCertificateV p := rfl
theorem g0_eq (v : ℝ) : g0Value v = lrCertificateG0 v := by
  simp only [g0Value, lrCertificateG0, one_div]
theorem w_eq (p : CertificatePoint) : wValue p.s = lrCertificateW p := by
  have hq : lrCertificateQ 0 = 0 := by simp [lrCertificateQ, topJ]
  simp only [lrCertificateW, lrCertificateOmega, lrCertificateB, wValue,
    mul_zero, add_zero, sub_zero, mul_one, hq]
theorem a_eq (s y : ℝ) :
    aValue s y = lrCertificateOmega s y + lrCertificateQ y - wValue s := by
  unfold aValue lrCertificateOmega lrCertificateB
  ring

theorem d1_eq (p : CertificatePoint) (hs : p.s ≠ 0) (hk : p.k ≠ 0) :
    d1Value p.s p.k = lrDeterminantD1 p := by
  have hy : lrDeterminantY p = (1 + p.k - p.s * p.k) / p.k := by
    unfold lrDeterminantY lrCertificateB lrCertificateE
    field_simp [hs, hk]
    <;> ring
  simp only [d1Value, lrDeterminantD1, hy]

theorem psi_eq (p : CertificatePoint)
    (hv : lrCertificateV p ≠ 0) (hplus : 1 + lrCertificateV p ≠ 0) :
    psiValue p.s p.k p.chi = lrDeterminantPsi p := by
  unfold psiValue
  rw [v_eq, a_eq, a_eq, g0_eq, w_eq]
  unfold lrDeterminantPsi lrCertificateGShape lrCertificateGShapeValue
    lrCertificatePW lrCertificatePWValue kappaValue
  dsimp only [lrCertificateY0, lrCertificateE]
  field_simp [hv, hplus]
  <;> ring

theorem c_eq (p : CertificatePoint) :
    cValue p.s p.k p.chi = psiValue p.s p.k p.chi - lrCertificateGShape p +
      4 * lrDeterminantDelta p * lrCertificateW p := by
  unfold cValue cScalar psiValue
  rw [v_eq, g0_eq, w_eq]
  unfold lrCertificateGShape lrCertificateGShapeValue lrDeterminantDelta deltaValue
  dsimp only [lrCertificateX, lrCertificateY0, lrCertificateE]
  simp only [div_eq_mul_inv]
  ring

theorem production_firstBracket_positive {p : CertificatePoint}
    (hs : p.s = 1 / 16)
    (hk : (767 / 256 : ℝ) ≤ p.k ∧ p.k ≤ 769 / 256)
    (hc : (767 / 2048 : ℝ) ≤ p.chi ∧ p.chi ≤ 769 / 2048) :
    0 < lrDeterminantFirstBracket
      (lrCertificateBFlow p) (lrDeterminantD1 p) (lrCertificateGShape p)
      (lrDeterminantPsi p) (lrDeterminantDelta p) (lrCertificateW p) := by
  have hsI : sI.Contains p.s := by norm_num [sI, point, Contains, hs]
  have hkI : kI.Contains p.k := by simpa [kI, Contains] using hk
  have hcI : chiI.Contains p.chi := by simpa [chiI, Contains] using hc
  have hs0 : p.s ≠ 0 := by rw [hs]; norm_num
  have hkpos : 0 < p.k := lt_of_lt_of_le (by norm_num) hk.1
  have hvBound := v_contains hsI hkI hcI
  have hvpos : 0 < lrCertificateV p := by
    rw [v_eq] at hvBound
    have hlo : (0 : ℝ) < (vBounds.lower : ℝ) := by exact_mod_cast v_positive
    exact hlo.trans_le hvBound.1
  have hp : 1 + lrCertificateV p ≠ 0 := by linarith
  have h := RootRatioNaturalPilotAssembly.firstBracket_positive hsI hkI hcI
  rw [b_eq, d1_eq p hs0 hkpos.ne', c_eq, psi_eq p hvpos.ne' hp] at h
  exact h

theorem production_pilot {p : CertificatePoint}
    (hs : p.s = 1 / 16)
    (hk : (767 / 256 : ℝ) ≤ p.k ∧ p.k ≤ 769 / 256)
    (hc : (767 / 2048 : ℝ) ≤ p.chi ∧ p.chi ≤ 769 / 2048) :
    LRDeterminantFirstBracketAt p :=
  (production_firstBracket_positive hs hk hc).le

/-- The actual closed certificate box. This is only a subbox of base-face-030. -/
def pilotBox : CertificateBox where
  sLo := 1 / 16
  sHi := 1 / 16
  kLo := 767 / 256
  kHi := 769 / 256
  chiLo := 767 / 2048
  chiHi := 769 / 2048

/-- Ready-to-use production leaf theorem: box membership is the only premise. -/
theorem certificate_sound {p : CertificatePoint} (hp : pilotBox.Contains p) :
    LRDeterminantFirstBracketAt p := by
  norm_num [CertificateBox.Contains, pilotBox] at hp
  rcases hp with ⟨hsLo, hsHi, hkLo, hkHi, hcLo, hcHi⟩
  exact production_pilot (le_antisymm hsHi hsLo) ⟨hkLo, hkHi⟩ ⟨hcLo, hcHi⟩

/-- Explicitly check that the certified box is nonempty. -/
theorem center_mem_box : pilotBox.Contains { s := 1 / 16, k := 3, chi := 3 / 8 } := by
  norm_num [pilotBox, CertificateBox.Contains]

#print axioms CourtadeKumar.RootRatioNaturalProductionPilot.production_firstBracket_positive
#print axioms CourtadeKumar.RootRatioNaturalProductionPilot.production_pilot
#print axioms CourtadeKumar.RootRatioNaturalProductionPilot.certificate_sound
end CourtadeKumar.RootRatioNaturalProductionPilot
