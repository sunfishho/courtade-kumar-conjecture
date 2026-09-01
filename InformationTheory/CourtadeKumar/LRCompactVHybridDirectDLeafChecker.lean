import InformationTheory.CourtadeKumar.LRCompactVDirectD
import InformationTheory.CourtadeKumar.LRCompactVPhysicalDiscard

/-!
# Hybrid direct-`D` accepted leaves for compact `V`

This checker combines two independently sound `P_W` lower bounds and uses
the cancellation-free full-`D` enclosure.  Unlike the older full-`D` leaf,
its payload needs no separate certificate for `log (1-y)`.
-/

set_option autoImplicit false

namespace CourtadeKumar

structure LRCompactVHybridDirectDLeafCertificate where
  b : LRCompactVBCertificate

namespace LRCompactVHybridDirectDLeafCertificate

def groupedLower
    (logTerms pZeroTerms wTerms dTerms N : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVHybridDirectDLeafCertificate) : ℚ :=
  let b := certificate.b.evaluate logTerms box
  let pZero := lrCompactVPZeroEnclosure logTerms pZeroTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let qLower := lrCompactVHybridQLower N box pZero wOne
  let d := lrCompactVDirectDEnclosure dTerms box
  let psi := lrCompactVPsiPolynomialHeadEnclosure N box
  lrCompactVSignedProductScalarLower b qLower +
    d.nonnegativeLower * psi.nonnegativeLower

def check
    (logTerms pZeroTerms wTerms dTerms N : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVHybridDirectDLeafCertificate) : Bool :=
  decide (
    certificate.b.check box = true ∧
    LRCompactVDirectDValid.check box = true ∧
    0 ≤ certificate.groupedLower
      logTerms pZeroTerms wTerms dTerms N box)

theorem sound
    (logTerms pZeroTerms wTerms dTerms N : ℕ)
    {box : CertificateBox}
    {certificate : LRCompactVHybridDirectDLeafCertificate}
    (hcheck : certificate.check
      logTerms pZeroTerms wTerms dTerms N box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hparts :
      certificate.b.check box = true ∧
      LRCompactVDirectDValid.check box = true ∧
      0 ≤ certificate.groupedLower
        logTerms pZeroTerms wTerms dTerms N box := by
    simpa [check] using hcheck
  have hbparts :
      LRCompactVBoxValid.check box = true ∧
      certificate.b.logOnePlusV.check
        (lrCompactVOnePlusVEnclosure box) = true ∧
      certificate.b.logOneSubRY.check
        (lrCompactVOneSubRYEnclosure box) = true := by
    simpa [LRCompactVBCertificate.check] using hparts.1
  have hbox := LRCompactVBoxValid.of_check hbparts.1
  have hdvalid := LRCompactVDirectDValid.of_check hparts.2.1
  intro point hpoint hphysical
  have hinterior := hphysical.1
  let t := Real.sqrt point.chi
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa [t] using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2 hinterior.2.2.2
  have hsquare : t ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  let b := certificate.b.evaluate logTerms box
  let pZero := lrCompactVPZeroEnclosure logTerms pZeroTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let qLower := lrCompactVHybridQLower N box pZero wOne
  let d := lrCompactVDirectDEnclosure dTerms box
  let psi := lrCompactVPsiPolynomialHeadEnclosure N box
  have hb : b.Contains (lrFlowB point.s point.k t) := by
    dsimp [b, t]
    exact certificate.b.sound logTerms hpoint hinterior hparts.1
  have hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi) :=
    lrCompactVPZeroEnclosure_sound
      logTerms pZeroTerms hbox hpoint hinterior
  have hwOne : wOne.Contains (lrWKernel point.s 1) :=
    lrCompactVWOneEnclosure_sound
      logTerms wTerms hbox hpoint hinterior
  have hqRaw := cast_lrCompactVHybridQLower_le
    (N := N) hbox hpoint hinterior hpZero hwOne
  have hq : (qLower : ℝ) ≤
      lrFlowPW point.s point.k t -
        4 * lrWKernel point.s 1 *
          (point.k * t ^ 2 / (1 + point.k)) := by
    rw [hsquare]
    dsimp [qLower, t]
    simpa [lrCompactVMx] using hqRaw
  have hBPos : 0 < lrFlowB point.s point.k t := by
    apply lrFlowB_pos hinterior.2.1.1 ht.1.le
    have hsqrtR : Real.sqrt point.s < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hinterior.1.1.le).2
        hinterior.1.2
    calc
      Real.sqrt point.s * point.k * t < 1 * point.k * t := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hinterior.2.1.1) ht.1
      _ < 1 := by
        have := mul_lt_mul_of_pos_right hinterior.2.1.2 ht.1
        nlinarith [ht.2]
  have hD0 : 0 ≤ lrFlowD point.s point.k t := by
    have hhead0 := lrCompactVDHead_nonneg
      ⟨hinterior.1.1.le, hinterior.1.2.le⟩
      (sq_nonneg (point.k * t)) 0
    exact hhead0.trans <|
      lrCompactVDHead_le_lrFlowD hinterior.1 hinterior.2.1 ht 0
  have hdLowerRaw : (d.lower : ℝ) ≤
      lrFlowD point.s point.k t := by
    dsimp [d, t]
    exact lrCompactVDirectDEnclosure_lower_le_flowD
      dTerms hdvalid hpoint hinterior
  have hdLower : (d.nonnegativeLower : ℝ) ≤
      lrFlowD point.s point.k t := by
    change ((max 0 d.lower : ℚ) : ℝ) ≤ _
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hD0 hdLowerRaw
  have hPsiFlow := lrCompactVPsiHead_le_lrFlowC
    hinterior.1 hinterior.2.1 ht N
  rw [hsquare] at hPsiFlow
  have hPsi0 := lrCompactVPsiHead_nonneg
    ⟨hinterior.1.1.le, hinterior.1.2.le⟩
    ⟨hinterior.2.1.1, hinterior.2.1.2.le⟩
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩ N
  have hPsiLower := lrCompactVPsiPolynomialHead_lower
    (N := N) hbox hpoint hinterior.2.1.1
  have hPsiClamp : (psi.nonnegativeLower : ℝ) ≤
      lrCompactVPsiHead N point.s point.k point.chi := by
    change ((max 0 psi.lower : ℚ) : ℝ) ≤ _
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hPsi0 hPsiLower
  have hPsiLowerFlow : (psi.nonnegativeLower : ℝ) ≤
      lrFlowC point.s point.k t := hPsiClamp.trans hPsiFlow
  have hPsi0Q : (0 : ℚ) ≤ psi.nonnegativeLower :=
    RationalEnclosure.nonnegativeLower_nonnegative psi
  have hPsi0Real : (0 : ℝ) ≤ psi.nonnegativeLower := by
    exact_mod_cast hPsi0Q
  have hsigned := cast_lrCompactVSignedProductScalarLower_le
    hb hq hBPos.le
  have hpayment := mul_le_mul hdLower hPsiLowerFlow
    hPsi0Real hD0
  have hlowerReal :
      (0 : ℝ) ≤
        (certificate.groupedLower
          logTerms pZeroTerms wTerms dTerms N box : ℝ) := by
    exact_mod_cast hparts.2.2
  have htotal : 0 ≤
      lrFlowB point.s point.k t *
          (lrFlowPW point.s point.k t -
            4 * lrWKernel point.s 1 *
              (point.k * t ^ 2 / (1 + point.k))) +
        lrFlowD point.s point.k t * lrFlowC point.s point.k t := by
    unfold groupedLower at hlowerReal
    dsimp [b, pZero, wOne, qLower, d, psi] at hsigned hpayment hlowerReal
    norm_num only [Rat.cast_add, Rat.cast_mul] at hlowerReal
    linarith
  have hvNe : point.k ≠ -1 := by linarith [hinterior.2.1.1]
  rw [lrCompactVReserveTarget, lrLowVReserve_eq_compact_grouped hvNe]
  exact htotal

end LRCompactVHybridDirectDLeafCertificate

end CourtadeKumar
