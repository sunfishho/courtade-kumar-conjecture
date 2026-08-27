import InformationTheory.CourtadeKumar.LRCompactVPhysicalDiscard

/-!
# Full-logarithm `D` mode for compact `V` leaves

The middle channel slabs use the exact identity `D=A-B` instead of a finite
positive head.  This module adds the corresponding accepted-leaf checker;
all other structured components are shared with the truncated mode.
-/

namespace CourtadeKumar

structure LRCompactVFullDLeafCertificate where
  b : LRCompactVBCertificate
  logOneSubY : RationalEnclosure.LogIntervalCertificate

namespace LRCompactVFullDLeafCertificate

def asDiscard (certificate : LRCompactVFullDLeafCertificate) :
    LRCompactVDiscardCertificate :=
  { b := certificate.b, logOneSubY := certificate.logOneSubY }

def aEnclosure (terms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVFullDLeafCertificate) : RationalEnclosure :=
  certificate.asDiscard.aEnclosure terms box

def dEnclosure (terms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVFullDLeafCertificate) : RationalEnclosure :=
  RationalEnclosure.sub (certificate.aEnclosure terms box)
    (certificate.b.evaluate terms box)

def groupedLower
    (logTerms pZeroTerms wTerms N : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVFullDLeafCertificate) : ℚ :=
  let pZero := lrCompactVPZeroEnclosure logTerms pZeroTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let q := lrCompactVQEnclosure N box pZero wOne
  lrCompactVSignedProductLower
      (certificate.b.evaluate logTerms box) q +
    (certificate.dEnclosure logTerms box).nonnegativeLower *
      (lrCompactVPsiPolynomialHeadEnclosure N box).nonnegativeLower

def check
    (logTerms pZeroTerms wTerms N : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVFullDLeafCertificate) : Bool :=
  decide (
    certificate.b.check box = true ∧
    certificate.logOneSubY.check
      (lrCompactVOneSubYEnclosure box) = true ∧
    0 ≤ certificate.groupedLower
      logTerms pZeroTerms wTerms N box)

theorem dEnclosure_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRCompactVFullDLeafCertificate}
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point)
    (hbcheck : certificate.b.check box = true)
    (hlogcheck : certificate.logOneSubY.check
      (lrCompactVOneSubYEnclosure box) = true) :
    (certificate.dEnclosure terms box).Contains
      (lrFlowD point.s point.k (Real.sqrt point.chi)) := by
  have hA := certificate.asDiscard.aEnclosure_sound
    terms hpoint hbcheck hlogcheck
  have hB := certificate.b.sound terms hpoint hinterior hbcheck
  have hsquare : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  have hAeq : lrCompactVAX point.k point.chi =
      lrFlowA point.k (Real.sqrt point.chi) := by
    calc
      lrCompactVAX point.k point.chi =
          lrCompactVAX point.k ((Real.sqrt point.chi) ^ 2) := by rw [hsquare]
      _ = lrFlowA point.k (Real.sqrt point.chi) := lrCompactVAX_flow
  rw [hAeq] at hA
  unfold dEnclosure lrFlowD
  exact RationalEnclosure.contains_sub hA hB

theorem sound
    (logTerms pZeroTerms wTerms N : ℕ)
    {box : CertificateBox}
    {certificate : LRCompactVFullDLeafCertificate}
    (hcheck : certificate.check
      logTerms pZeroTerms wTerms N box = true) :
    ∀ point, box.Contains point → LRCompactVInterior point →
      0 ≤ lrCompactVReserveTarget point := by
  have hparts :
      certificate.b.check box = true ∧
      certificate.logOneSubY.check
        (lrCompactVOneSubYEnclosure box) = true ∧
      0 ≤ certificate.groupedLower
        logTerms pZeroTerms wTerms N box := by
    simpa [check] using hcheck
  have hbparts :
      LRCompactVBoxValid.check box = true ∧
      certificate.b.logOnePlusV.check
        (lrCompactVOnePlusVEnclosure box) = true ∧
      certificate.b.logOneSubRY.check
        (lrCompactVOneSubRYEnclosure box) = true := by
    simpa [LRCompactVBCertificate.check] using hparts.1
  have hbox := LRCompactVBoxValid.of_check hbparts.1
  intro point hpoint hinterior
  let t := Real.sqrt point.chi
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa [t] using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2 hinterior.2.2.2
  have hsquare : t ^ 2 = point.chi := Real.sq_sqrt hinterior.2.2.1.le
  let b := certificate.b.evaluate logTerms box
  let pZero := lrCompactVPZeroEnclosure logTerms pZeroTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let q := lrCompactVQEnclosure N box pZero wOne
  let d := certificate.dEnclosure logTerms box
  have hb : b.Contains (lrFlowB point.s point.k t) := by
    dsimp [b, t]
    exact certificate.b.sound logTerms hpoint hinterior hparts.1
  have hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi) :=
    lrCompactVPZeroEnclosure_sound
      logTerms pZeroTerms hbox hpoint hinterior
  have hwOne : wOne.Contains (lrWKernel point.s 1) :=
    lrCompactVWOneEnclosure_sound
      logTerms wTerms hbox hpoint hinterior
  have hq : q.Contains (lrCompactVQX N point.s point.k point.chi) :=
    lrCompactVQEnclosure_sound hbox hpoint hpZero hwOne
  have hd : d.Contains (lrFlowD point.s point.k t) := by
    dsimp [d, t]
    exact certificate.dEnclosure_sound logTerms hpoint hinterior
      hparts.1 hparts.2.1
  have hBPos : 0 < lrFlowB point.s point.k t := by
    apply lrFlowB_pos hinterior.2.1.1 ht.1.le
    have hsqrtR : Real.sqrt point.s < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hinterior.1.1.le).2 hinterior.1.2
    calc
      Real.sqrt point.s * point.k * t < 1 * point.k * t := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hinterior.2.1.1) ht.1
      _ < 1 := by
        have := mul_lt_mul_of_pos_right hinterior.2.1.2 ht.1
        nlinarith [ht.2]
  have hD0 : 0 ≤ lrFlowD point.s point.k t := by
    have hhead0 := lrCompactVDHead_nonneg
      ⟨hinterior.1.1.le, hinterior.1.2.le⟩ (sq_nonneg (point.k * t)) 0
    exact hhead0.trans <|
      lrCompactVDHead_le_lrFlowD hinterior.1 hinterior.2.1 ht 0
  have hsigned := cast_lrCompactVSignedProductLower_le
    hb hq hBPos.le
  have hPW := lrCompactVPWLower_le_lrFlowPW
    hinterior.1 hinterior.2.1 ht N
  have hQActual :
      lrCompactVQX N point.s point.k point.chi ≤
        lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k)) := by
    unfold lrCompactVQX lrCompactVMx
    rw [hsquare]
    linarith
  have hsignedActual := hsigned.trans <|
    mul_le_mul_of_nonneg_left hQActual hBPos.le
  have hPsiFlow := lrCompactVPsiHead_le_lrFlowC
    hinterior.1 hinterior.2.1 ht N
  rw [hsquare] at hPsiFlow
  have hPsi0 := lrCompactVPsiHead_nonneg
    ⟨hinterior.1.1.le, hinterior.1.2.le⟩
    ⟨hinterior.2.1.1, hinterior.2.1.2.le⟩
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩ N
  have hPsiLower := lrCompactVPsiPolynomialHead_lower
    (N := N) hbox hpoint hinterior.2.1.1
  have hPsiClamp :
      ((lrCompactVPsiPolynomialHeadEnclosure N box).nonnegativeLower : ℝ) ≤
        lrCompactVPsiHead N point.s point.k point.chi := by
    change ((max 0
      (lrCompactVPsiPolynomialHeadEnclosure N box).lower : ℚ) : ℝ) ≤ _
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hPsi0 hPsiLower
  have hDClamp := RationalEnclosure.cast_nonnegativeLower_le hd hD0
  have hPsiClamp0 : (0 : ℝ) ≤
      (lrCompactVPsiPolynomialHeadEnclosure N box).nonnegativeLower := by
    exact_mod_cast RationalEnclosure.nonnegativeLower_nonnegative
      (lrCompactVPsiPolynomialHeadEnclosure N box)
  have hpayment := (mul_le_mul hDClamp hPsiClamp hPsiClamp0 hD0).trans <|
    mul_le_mul_of_nonneg_left hPsiFlow hD0
  have hlowerReal :
      (0 : ℝ) ≤
        (certificate.groupedLower
          logTerms pZeroTerms wTerms N box : ℝ) := by
    exact_mod_cast hparts.2.2
  have htotal : 0 ≤
      lrFlowB point.s point.k t *
          (lrFlowPW point.s point.k t -
            4 * lrWKernel point.s 1 *
              (point.k * t ^ 2 / (1 + point.k))) +
        lrFlowD point.s point.k t * lrFlowC point.s point.k t := by
    unfold groupedLower at hlowerReal
    dsimp [b, pZero, wOne, q, d] at hsignedActual hpayment hlowerReal
    norm_num only [Rat.cast_add, Rat.cast_mul] at hlowerReal
    linarith
  have hvNe : point.k ≠ -1 := by linarith [hinterior.2.1.1]
  rw [lrCompactVReserveTarget, lrLowVReserve_eq_compact_grouped hvNe]
  exact htotal

end LRCompactVFullDLeafCertificate

end CourtadeKumar
