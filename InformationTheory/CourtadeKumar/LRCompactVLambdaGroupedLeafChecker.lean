import InformationTheory.CourtadeKumar.LRCompactVLambdaGroupedInterval
import InformationTheory.CourtadeKumar.LRCompactVDirectD
import InformationTheory.CourtadeKumar.LRCompactVLeafAssembly
import InformationTheory.CourtadeKumar.LRCompactVPhysicalDiscard

/-!
# Staged grouped leaves with an independent `D/B` ratio

After the cheaper hybrid direct-`D` leaf fails, this checker sets

`lambda = max(0,D_lower) / B_upper`.

The grouped interval module certifies `Q + lambda C`, while the elementary
ratio inequality `lambda B ≤ D` lifts that result to `BQ + DC`.  The leaf
payload is still only the two logarithm certificates already needed for
`B`, together with a choice between the cheaper 128-term head and the
stronger 192-term head.  `D`, `W_R(1)`, and the selected grouped head are
deterministic rational computations replayed by the kernel.
-/

set_option autoImplicit false

namespace CourtadeKumar

/-- Independent box-wide ratio used by the minimal grouped fallback. -/
def lrCompactVIndependentLambda
    (b d : RationalEnclosure) : ℚ :=
  d.nonnegativeLower / b.upper

theorem lrCompactVIndependentLambda_nonnegative
    {b d : RationalEnclosure} (hbUpper : (0 : ℚ) < b.upper) :
    (0 : ℚ) ≤ lrCompactVIndependentLambda b d := by
  unfold lrCompactVIndependentLambda
  exact div_nonneg
    (RationalEnclosure.nonnegativeLower_nonnegative d) hbUpper.le

theorem cast_lrCompactVIndependentLambda_mul_le
    {b d : RationalEnclosure} {B D : ℝ}
    (hBUpper : B ≤ (b.upper : ℝ))
    (hbUpper : (0 : ℚ) < b.upper)
    (hdLower : (d.lower : ℝ) ≤ D) (hD0 : 0 ≤ D) :
    (lrCompactVIndependentLambda b d : ℝ) * B ≤ D := by
  have hlambdaQ := lrCompactVIndependentLambda_nonnegative
    (b := b) (d := d) hbUpper
  have hlambda : (0 : ℝ) ≤ lrCompactVIndependentLambda b d := by
    exact_mod_cast hlambdaQ
  have hfirst := mul_le_mul_of_nonneg_left hBUpper hlambda
  have hbNe : b.upper ≠ 0 := hbUpper.ne'
  have hcancelQ :
      lrCompactVIndependentLambda b d * b.upper =
        d.nonnegativeLower := by
    unfold lrCompactVIndependentLambda
    exact div_mul_cancel₀ _ hbNe
  have hcancel :
      (lrCompactVIndependentLambda b d : ℝ) * (b.upper : ℝ) =
        (d.nonnegativeLower : ℝ) := by
    exact_mod_cast hcancelQ
  have hclamp : (d.nonnegativeLower : ℝ) ≤ D := by
    change ((max 0 d.lower : ℚ) : ℝ) ≤ D
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hD0 hdLower
  exact hfirst.trans (hcancel.le.trans hclamp)

/-- The adaptive grouped checker first tries the cheaper head and escalates
to the measured hard-region head only when needed. -/
inductive LRCompactVLambdaGroupedHeadChoice where
  | n128
  | n192

namespace LRCompactVLambdaGroupedHeadChoice

def headN : LRCompactVLambdaGroupedHeadChoice → ℕ
  | .n128 => 128
  | .n192 => lrCompactVLambdaGroupedHeadN

end LRCompactVLambdaGroupedHeadChoice

structure LRCompactVLambdaGroupedLeafCertificate where
  b : LRCompactVBCertificate
  headChoice : LRCompactVLambdaGroupedHeadChoice

namespace LRCompactVLambdaGroupedLeafCertificate

def groupedLower
    (logTerms wTerms dTerms : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVLambdaGroupedLeafCertificate) : ℚ :=
  let b := certificate.b.evaluate logTerms box
  let d := lrCompactVDirectDEnclosure dTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let lambda := lrCompactVIndependentLambda b d
  lrCompactVLambdaGroupedFiniteLower
    certificate.headChoice.headN lambda box wOne

def check
    (logTerms wTerms dTerms : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVLambdaGroupedLeafCertificate) : Bool :=
  let b := certificate.b.evaluate logTerms box
  let d := lrCompactVDirectDEnclosure dTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let lambda := lrCompactVIndependentLambda b d
  decide (
    certificate.b.check box = true ∧
    LRCompactVDirectDValid.check box = true ∧
    0 < b.upper ∧
    0 ≤ lrCompactVLambdaGroupedFiniteLower
      certificate.headChoice.headN lambda box wOne)

theorem sound
    (logTerms wTerms dTerms : ℕ)
    {box : CertificateBox}
    {certificate : LRCompactVLambdaGroupedLeafCertificate}
    (hcheck : certificate.check
      logTerms wTerms dTerms box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hparts :
      certificate.b.check box = true ∧
      LRCompactVDirectDValid.check box = true ∧
      0 < (certificate.b.evaluate logTerms box).upper ∧
      0 ≤ certificate.groupedLower logTerms wTerms dTerms box := by
    simpa [check, groupedLower] using hcheck
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
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2
          hinterior.2.2.2
  have hsquare : t ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  let b := certificate.b.evaluate logTerms box
  let d := lrCompactVDirectDEnclosure dTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  let lambda := lrCompactVIndependentLambda b d
  have hb : b.Contains (lrFlowB point.s point.k t) := by
    dsimp [b, t]
    exact certificate.b.sound logTerms hpoint hinterior hparts.1
  have hwOne : wOne.Contains (lrWKernel point.s 1) := by
    dsimp [wOne]
    exact lrCompactVWOneEnclosure_sound
      logTerms wTerms hbox hpoint hinterior
  have hdLower : (d.lower : ℝ) ≤ lrFlowD point.s point.k t := by
    dsimp [d, t]
    exact lrCompactVDirectDEnclosure_lower_le_flowD
      dTerms hdvalid hpoint hinterior
  have hD0 : 0 ≤ lrFlowD point.s point.k t := by
    have hhead0 := lrCompactVDHead_nonneg
      ⟨hinterior.1.1.le, hinterior.1.2.le⟩
      (sq_nonneg (point.k * t)) 0
    exact hhead0.trans <|
      lrCompactVDHead_le_lrFlowD
        hinterior.1 hinterior.2.1 ht 0
  have hlambdaQ : (0 : ℚ) ≤ lambda := by
    dsimp [lambda, b, d]
    exact lrCompactVIndependentLambda_nonnegative hparts.2.2.1
  have hlambda : (0 : ℝ) ≤ lambda := by exact_mod_cast hlambdaQ
  have hfinite := lrCompactVLambdaGroupedFiniteLower_le
    (N := certificate.headChoice.headN)
    hlambdaQ hbox hpoint hinterior hwOne
  have hanalytic := lrCompactVLambdaGroupedFinite_le
    hinterior.1 hinterior.2.1 ht hlambda
    certificate.headChoice.headN
  have hbound :
      (lrCompactVLambdaGroupedFiniteLower
          certificate.headChoice.headN lambda box wOne : ℝ) ≤
        (lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k))) +
          (lambda : ℝ) * lrFlowC point.s point.k t := by
    exact hfinite.trans (by simpa [hsquare] using hanalytic)
  have hlowerReal :
      (0 : ℝ) ≤
        (certificate.groupedLower
          logTerms wTerms dTerms box : ℚ) := by
    exact_mod_cast hparts.2.2.2
  have hQlambda :
      0 ≤
        (lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k))) +
          (lambda : ℝ) * lrFlowC point.s point.k t := by
    dsimp [groupedLower, b, d, wOne, lambda] at hlowerReal
    exact hlowerReal.trans hbound
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
  have hlambdaB :
      (lambda : ℝ) * lrFlowB point.s point.k t ≤
        lrFlowD point.s point.k t := by
    dsimp [lambda]
    exact cast_lrCompactVIndependentLambda_mul_le
      hb.2 hparts.2.2.1 hdLower hD0
  have hC0 := lrFlowC_nonneg_of_compact_series
    hinterior.1 hinterior.2.1 ht
  have htotal :
      0 ≤
        lrFlowB point.s point.k t *
          (lrFlowPW point.s point.k t -
            4 * lrWKernel point.s 1 *
              (point.k * t ^ 2 / (1 + point.k))) +
        lrFlowD point.s point.k t *
          lrFlowC point.s point.k t := by
    calc
      0 ≤
          lrFlowB point.s point.k t *
              ((lrFlowPW point.s point.k t -
                4 * lrWKernel point.s 1 *
                  (point.k * t ^ 2 / (1 + point.k))) +
                (lambda : ℝ) * lrFlowC point.s point.k t) +
            (lrFlowD point.s point.k t -
                (lambda : ℝ) * lrFlowB point.s point.k t) *
              lrFlowC point.s point.k t :=
        add_nonneg
          (mul_nonneg hBPos.le hQlambda)
          (mul_nonneg (sub_nonneg.mpr hlambdaB) hC0)
      _ =
          lrFlowB point.s point.k t *
            (lrFlowPW point.s point.k t -
              4 * lrWKernel point.s 1 *
                (point.k * t ^ 2 / (1 + point.k))) +
          lrFlowD point.s point.k t *
            lrFlowC point.s point.k t := by ring
  have hvNe : point.k ≠ -1 := by linarith [hinterior.2.1.1]
  rw [lrCompactVReserveTarget,
    lrLowVReserve_eq_compact_grouped hvNe]
  exact htotal

end LRCompactVLambdaGroupedLeafCertificate

end CourtadeKumar
