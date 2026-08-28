import InformationTheory.CourtadeKumar.IntervalMidpointSKCertificate
import InformationTheory.CourtadeKumar.LRHighShapeVZeroFaceSKEvaluator

/-!
# Centered direct-`V` certificates on boxes touching `χ = 0`

The center payload encloses the full `χ` interval after freezing only `s`
and `k`.  A separate whole-box payload encloses the genuine `s` and `k`
derivatives with the endpoint-safe evaluator.  The analytic mean-value step
is used only for points with positive `χ`, exactly the open chart occurring
in the final LR flow theorem.
-/

open Set

namespace CourtadeKumar

/-- Freeze only the two smooth coordinates of a box. -/
def CertificateBox.centerSKBox (box : CertificateBox) : CertificateBox :=
  let s := RationalEnclosure.center box.sInterval
  let k := RationalEnclosure.center box.kInterval
  { sLo := s, sHi := s, kLo := k, kHi := k,
    chiLo := box.chiLo, chiHi := box.chiHi }

theorem CertificateBox.centerSKBox_contains_anchorSK
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    box.centerSKBox.Contains (box.anchorSK point) := by
  simp only [CertificateBox.centerSKBox, CertificateBox.anchorSK,
    CertificateBox.midpoint]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl,
    hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩

/-- Closed-box conditions sufficient for every positive-`χ` point in the
box to belong to the ordinary high-shape interior. -/
def lrHighShapeSKOpenChartBoxCheck (box : CertificateBox) : Bool :=
  decide (
    (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
    (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      box.sHi * box.kHi < 1 ∧
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧ box.chiHi < 1)

theorem lrHighShapeSKOpenChartBoxCheck_sound
    {box : CertificateBox}
    (hcheck : lrHighShapeSKOpenChartBoxCheck box = true)
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hchi : 0 < point.chi) :
    LRHighShapeInterior point := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi < 1 := by
    simpa [lrHighShapeSKOpenChartBoxCheck] using hcheck
  have hsLo : (0 : ℝ) < box.sLo := by exact_mod_cast hparts.1
  have hsHi : (box.sHi : ℝ) < 1 := by exact_mod_cast hparts.2.2.1
  have hkLo : (0 : ℝ) < box.kLo := by exact_mod_cast hparts.2.2.2.1
  have hprodHi : ((box.sHi * box.kHi : ℚ) : ℝ) < 1 := by
    exact_mod_cast hparts.2.2.2.2.2.1
  have hchiHi : (box.chiHi : ℝ) < 1 := by
    exact_mod_cast hparts.2.2.2.2.2.2.2.2
  have hs : point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hsLo.trans_le hpoint.1, hpoint.2.1.trans_lt hsHi⟩
  have hkPos : 0 < point.k := hkLo.trans_le hpoint.2.2.1
  have hsHiNonneg : (0 : ℝ) ≤ box.sHi :=
    hsLo.le.trans (by exact_mod_cast hparts.2.1)
  have he : lrCertificateE point ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hs.1 hkPos
    · calc
        point.s * point.k ≤ (box.sHi : ℝ) * box.kHi :=
          mul_le_mul hpoint.2.1 hpoint.2.2.2.1 hkPos.le hsHiNonneg
        _ < 1 := by exact_mod_cast hprodHi
  exact ⟨hs, he, ⟨hchi, hpoint.2.2.2.2.2.trans_lt hchiHi⟩⟩

structure LRHighShapeVZeroFaceSKCenteredCertificate where
  center : LRHighShapeVZeroFaceCertificate
  derivative : LRHighShapeVZeroFaceCertificate

namespace LRHighShapeVZeroFaceSKCenteredCertificate

def payloadCheck (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceSKCenteredCertificate) : Bool :=
  lrHighShapeSKOpenChartBoxCheck box &&
    certificate.center.check box.centerSKBox &&
    certificate.derivative.skCheck box

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceSKCenteredCertificate) :
    MidpointSKCertificate :=
  let centerResult := certificate.center.evaluate terms box.centerSKBox
  let derivativeResult := certificate.derivative.evaluateSKAD terms box
  { value := centerResult
    derivS := derivativeResult.derivS
    derivK := derivativeResult.derivK }

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceSKCenteredCertificate) : Bool :=
  certificate.payloadCheck box && (certificate.evaluate terms box).check box

noncomputable def derivativeEnclosures (terms : ℕ)
    {box : CertificateBox}
    {certificate : LRHighShapeVZeroFaceSKCenteredCertificate}
    (hcheck : certificate.derivative.skCheck box = true)
    (hdomain : lrHighShapeSKOpenChartBoxCheck box = true) :
    BoxSKDerivativeEnclosuresOn lrCertificateVTarget box
      (certificate.evaluate terms box) (fun chi ↦ 0 < chi) := by
  refine
    { partialS := lrCertificateVTargetDerivS
      partialK := lrCertificateVTargetDerivK
      derivS := ?_
      derivK := ?_
      boundS := ?_
      boundK := ?_ }
  · intro point hpoint hchi
    exact hasDerivAt_lrCertificateVTarget_s
      (lrHighShapeSKOpenChartBoxCheck_sound hdomain hpoint hchi)
  · intro point hpoint hchi
    exact hasDerivAt_lrCertificateVTarget_k
      (lrHighShapeSKOpenChartBoxCheck_sound hdomain hpoint hchi)
  · intro point hpoint
    have h := certificate.derivative.evaluateSKAD_sound terms hcheck hpoint
    simpa [evaluate] using h.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateSKAD_sound terms hcheck hpoint
    simpa [evaluate] using h.2.2

theorem positive_of_accepts (terms : ℕ) {box : CertificateBox}
    {certificate : LRHighShapeVZeroFaceSKCenteredCertificate}
    (haccept : certificate.accepts terms box = true)
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hchi : 0 < point.chi) :
    0 < lrCertificateVTarget point := by
  have hacceptParts : certificate.payloadCheck box = true ∧
      (certificate.evaluate terms box).check box = true := by
    simpa [accepts] using haccept
  have hparts :
      (lrHighShapeSKOpenChartBoxCheck box = true ∧
        certificate.center.check box.centerSKBox = true) ∧
      certificate.derivative.skCheck box = true := by
    simpa [payloadCheck] using hacceptParts.1
  have hvalue : ∀ anchor, box.Contains anchor →
      (certificate.evaluate terms box).value.Contains
        (lrCertificateVTarget (box.anchorSK anchor)) := by
    intro anchor hanchor
    have hcenter := certificate.center.evaluate_sound terms hparts.1.2
      (box.centerSKBox_contains_anchorSK hanchor)
    simpa [evaluate] using hcenter
  exact (certificate.evaluate terms box).soundOn_of_derivativeEnclosures
    hvalue (certificate.derivativeEnclosures terms hparts.2 hparts.1.1)
    hacceptParts.2 hpoint hchi

/-- Reuse a whole-box base payload while recomputing the much narrower
center payload. -/
def autoFromBase (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (base : LRHighShapeVCertificate) :
    LRHighShapeVZeroFaceSKCenteredCertificate :=
  { center := LRHighShapeVZeroFaceCertificate.auto sqrtFuel logFuel
      box.centerSKBox
    derivative := LRHighShapeVZeroFaceCertificate.autoFromBase
      sqrtFuel logFuel box base }

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRHighShapeVZeroFaceSKCenteredCertificate :=
  autoFromBase sqrtFuel logFuel box
    (LRHighShapeVCertificate.auto sqrtFuel logFuel box)

end LRHighShapeVZeroFaceSKCenteredCertificate
end CourtadeKumar
