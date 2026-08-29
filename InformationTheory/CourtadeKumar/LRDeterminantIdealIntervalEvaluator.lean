import InformationTheory.CourtadeKumar.LRDeterminantIdealCoreCertificate
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate
import InformationTheory.CourtadeKumar.LRSmallSBridgeChi

/-!
# Verified interval evaluator for the determinant ideal-core leaves

This module supplies the nonlinear evaluator missing from
`LRDeterminantIdealCoreCertificate`.  In particular it handles both removable
singularities that occur on boxes touching `chi = 0`:

* `chi * log chi / (1 + chi)` is enclosed by its endpoint and the exact value
  `0` at the origin;
* `h(t) = (1+t) log(1+t) / t` is enclosed using its monotonicity and the exact
  continuous value `h(0)=1`.

All proposed logarithm range reductions are checked by the existing Boolean
checker.  The evaluator itself uses only the proved rational interval
operations, and its final soundness theorem targets all three quantities used
by an accepted leaf: the endpoint ideal core, its `L` derivative, and `C₁`.
-/

open Set Filter

namespace CourtadeKumar

/-! ## A zero-aware enclosure for `h(t)` -/

lemma hasDerivAt_lrDeterminantIdealH
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt lrDeterminantIdealH
      ((t - Real.log (1 + t)) / t ^ 2) t := by
  have hone : HasDerivAt (fun z : ℝ ↦ 1 + z) 1 t :=
    (hasDerivAt_id t).const_add 1
  have honePos : 0 < 1 + t := by linarith
  have hlog := hone.log honePos.ne'
  have hnum := hone.mul hlog
  have hquot := hnum.div (hasDerivAt_id t) ht.ne'
  have hg : HasDerivAt
      (fun z : ℝ ↦ (1 + z) * Real.log (1 + z) / z)
      ((t - Real.log (1 + t)) / t ^ 2) t := by
    convert hquot using 1
    simp only [Pi.mul_apply, id_eq]
    field_simp [ht.ne', honePos.ne']
    ring_nf
  apply hg.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with z hz
  simp [lrDeterminantIdealH, hz.ne']

lemma lrDeterminantIdealH_deriv_nonneg
    {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv lrDeterminantIdealH t := by
  rw [(hasDerivAt_lrDeterminantIdealH ht).deriv]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
  exact div_nonneg (sub_nonneg.mpr (by simpa using hlog)) (sq_nonneg t)

lemma lrDeterminantIdealH_one_le
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ lrDeterminantIdealH t := by
  rcases ht.eq_or_lt with rfl | htPos
  · simp [lrDeterminantIdealH]
  · have honePos : 0 < 1 + t := by linarith
    have hlog := Real.one_sub_inv_le_log_of_pos honePos
    have hscaled := mul_le_mul_of_nonneg_left hlog honePos.le
    have hid :
        (1 + t) * (1 - (1 + t)⁻¹) = t := by
      field_simp [honePos.ne']
      ring
    unfold lrDeterminantIdealH
    rw [if_neg htPos.ne', le_div_iff₀ htPos]
    calc
      1 * t = t := one_mul t
      _ = (1 + t) * (1 - (1 + t)⁻¹) := hid.symm
      _ ≤ (1 + t) * Real.log (1 + t) := hscaled

lemma lrDeterminantIdealH_mono_nonnegative
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    lrDeterminantIdealH a ≤ lrDeterminantIdealH b := by
  rcases ha.eq_or_lt with rfl | haPos
  · simpa [lrDeterminantIdealH] using
      lrDeterminantIdealH_one_le (ha.trans hab)
  · have hmono : MonotoneOn lrDeterminantIdealH (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      · intro x hx
        exact (hasDerivAt_lrDeterminantIdealH
          (haPos.trans_le hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hasDerivAt_lrDeterminantIdealH
          (haPos.trans hx.1)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact lrDeterminantIdealH_deriv_nonneg (haPos.trans hx.1)
    exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- A single logarithm proposal suffices for both the positive-input and the
zero-touching implementations of `h`. -/
structure LRDeterminantIdealHCertificate where
  logOnePlus : RationalEnclosure.LogIntervalCertificate

namespace LRDeterminantIdealHCertificate

def onePlusI (input : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) input

def endpointOnePlusI (input : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.point (1 + input.upper)

def endpointRaw (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRDeterminantIdealHCertificate) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.mul (endpointOnePlusI input)
      (certificate.logOnePlus.enclosure terms))
    (RationalEnclosure.point input.upper)

/-- The exact interval expression.  A box starting at zero uses monotonicity;
strictly positive boxes use ordinary interval division. -/
def enclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRDeterminantIdealHCertificate) : RationalEnclosure :=
  if input.lower = 0 then
    if input.upper = 0 then RationalEnclosure.point 1
    else ⟨1, (endpointRaw terms input certificate).upper⟩
  else
    RationalEnclosure.div
      (RationalEnclosure.mul (onePlusI input)
        (certificate.logOnePlus.enclosure terms)) input

/-- Every side condition, including positivity of a divisor, is executable. -/
def check (input : RationalEnclosure)
    (certificate : LRDeterminantIdealHCertificate) : Bool :=
  decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper) &&
    if input.lower = 0 then
      if input.upper = 0 then true
      else decide ((0 : ℚ) < input.upper) &&
        certificate.logOnePlus.check (endpointOnePlusI input)
    else decide ((0 : ℚ) < input.lower) &&
      certificate.logOnePlus.check (onePlusI input)

theorem sound
    (terms : ℕ) {input : RationalEnclosure} {t : ℝ}
    {certificate : LRDeterminantIdealHCertificate}
    (hcheck : certificate.check input = true)
    (ht : input.Contains t) :
    (certificate.enclosure terms input).Contains
      (lrDeterminantIdealH t) := by
  have hraw :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper) = true ∧
      (if input.lower = 0 then
        if input.upper = 0 then true
        else decide ((0 : ℚ) < input.upper) &&
          certificate.logOnePlus.check (endpointOnePlusI input)
      else decide ((0 : ℚ) < input.lower) &&
        certificate.logOnePlus.check (onePlusI input)) = true := by
    simpa [check] using hcheck
  have hdomain : (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper := by
    simpa using hraw.1
  by_cases hlo : input.lower = 0
  · by_cases hup : input.upper = 0
    · have htZero : t = 0 := by
        have htNonneg : 0 ≤ t := by
          have : (0 : ℝ) ≤ (input.lower : ℝ) := by
            exact_mod_cast hdomain.1
          exact this.trans ht.1
        have htUpper : t ≤ 0 := by simpa [hup] using ht.2
        linarith
      subst t
      simp [enclosure, hlo, hup, lrDeterminantIdealH,
        RationalEnclosure.point, RationalEnclosure.Contains]
    · have hparts : (0 : ℚ) < input.upper ∧
          certificate.logOnePlus.check (endpointOnePlusI input) = true := by
        simpa [hlo, hup] using hraw.2
      have huPos : (0 : ℝ) < (input.upper : ℝ) := by
        exact_mod_cast hparts.1
      have honeEndpoint : (endpointOnePlusI input).Contains
          (1 + (input.upper : ℝ)) := by
        simpa [endpointOnePlusI] using
          RationalEnclosure.contains_point (1 + input.upper)
      have hlog := certificate.logOnePlus.sound terms hparts.2 honeEndpoint
      have hnum := RationalEnclosure.contains_mul honeEndpoint hlog
      have hden : (RationalEnclosure.point input.upper).Contains
          (input.upper : ℝ) := RationalEnclosure.contains_point input.upper
      have hquot := RationalEnclosure.contains_div
        (by simpa [RationalEnclosure.point] using hparts.1) hnum hden
      have hendpoint : (endpointRaw terms input certificate).Contains
          (lrDeterminantIdealH (input.upper : ℝ)) := by
        unfold endpointRaw lrDeterminantIdealH
        rw [if_neg huPos.ne']
        simpa using hquot
      have htNonneg : 0 ≤ t := by
        have hloReal : (0 : ℝ) ≤ (input.lower : ℝ) := by
          exact_mod_cast hdomain.1
        exact hloReal.trans ht.1
      have hmono := lrDeterminantIdealH_mono_nonnegative htNonneg ht.2
      have hone := lrDeterminantIdealH_one_le htNonneg
      have hbounds :
          (1 : ℝ) ≤ lrDeterminantIdealH t ∧
          lrDeterminantIdealH t ≤
            ((endpointRaw terms input certificate).upper : ℝ) :=
        ⟨hone, hmono.trans hendpoint.2⟩
      simpa [enclosure, hlo, hup, RationalEnclosure.Contains] using hbounds
  · have hparts : (0 : ℚ) < input.lower ∧
        certificate.logOnePlus.check (onePlusI input) = true := by
      simpa [hlo] using hraw.2
    have hone := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point 1) ht
    have hlog := certificate.logOnePlus.sound terms hparts.2 hone
    have hnum := RationalEnclosure.contains_mul hone hlog
    have hquot := RationalEnclosure.contains_div hparts.1 hnum ht
    have htPos : 0 < t := by
      have hloReal : (0 : ℝ) < (input.lower : ℝ) := by
        exact_mod_cast hparts.1
      exact hloReal.trans_le ht.1
    unfold enclosure lrDeterminantIdealH
    rw [if_neg hlo, if_neg htPos.ne']
    simpa [onePlusI] using hquot

def auto (logFuel : ℕ) (input : RationalEnclosure) :
    LRDeterminantIdealHCertificate :=
  { logOnePlus := RationalEnclosure.autoLogIntervalCertificate logFuel
      (if input.lower = 0 then endpointOnePlusI input else onePlusI input) }

end LRDeterminantIdealHCertificate

/-! ## A zero-aware enclosure for `chi log chi / (1+chi)` -/

structure LRDeterminantIdealQChiCertificate where
  logChi : RationalEnclosure.LogIntervalCertificate

namespace LRDeterminantIdealQChiCertificate

def endpointRaw (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRDeterminantIdealQChiCertificate) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.mul (RationalEnclosure.point input.upper)
      (certificate.logChi.enclosure terms))
    (RationalEnclosure.point (1 + input.upper))

def enclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRDeterminantIdealQChiCertificate) : RationalEnclosure :=
  if input.lower = 0 then
    if input.upper = 0 then RationalEnclosure.point 0
    else ⟨(endpointRaw terms input certificate).lower, 0⟩
  else
    RationalEnclosure.div
      (RationalEnclosure.mul input (certificate.logChi.enclosure terms))
      (RationalEnclosure.add (RationalEnclosure.point 1) input)

def check (input : RationalEnclosure)
    (certificate : LRDeterminantIdealQChiCertificate) : Bool :=
  decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper ≤ 1) &&
    if input.lower = 0 then
      if input.upper = 0 then true
      else decide (input.upper ≤ (1 / 4 : ℚ)) &&
        certificate.logChi.check (RationalEnclosure.point input.upper)
    else decide ((0 : ℚ) < input.lower) &&
      certificate.logChi.check input

theorem sound
    (terms : ℕ) {input : RationalEnclosure} {chi : ℝ}
    {certificate : LRDeterminantIdealQChiCertificate}
    (hcheck : certificate.check input = true)
    (hchi : input.Contains chi) :
    (certificate.enclosure terms input).Contains
      (lrSmallSBridgeQChi chi) := by
  have hraw :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
        input.upper ≤ 1) = true ∧
      (if input.lower = 0 then
        if input.upper = 0 then true
        else decide (input.upper ≤ (1 / 4 : ℚ)) &&
          certificate.logChi.check (RationalEnclosure.point input.upper)
      else decide ((0 : ℚ) < input.lower) &&
        certificate.logChi.check input) = true := by
    simpa [check] using hcheck
  have hdomain : (0 : ℚ) ≤ input.lower ∧
      input.lower ≤ input.upper ∧ input.upper ≤ 1 := by
    simpa using hraw.1
  by_cases hlo : input.lower = 0
  · have hchiNonneg : 0 ≤ chi := by
      have hloReal : (0 : ℝ) ≤ (input.lower : ℝ) := by
        exact_mod_cast hdomain.1
      exact hloReal.trans hchi.1
    by_cases hup : input.upper = 0
    · have hchiZero : chi = 0 := by
        have : chi ≤ 0 := by simpa [hup] using hchi.2
        linarith
      subst chi
      simp [enclosure, hlo, hup, lrSmallSBridgeQChi,
        RationalEnclosure.point, RationalEnclosure.Contains]
    · have hparts : input.upper ≤ (1 / 4 : ℚ) ∧
          certificate.logChi.check
            (RationalEnclosure.point input.upper) = true := by
        simpa [hlo, hup] using hraw.2
      have huPosRat : (0 : ℚ) < input.upper :=
        lt_of_le_of_ne (hdomain.1.trans hdomain.2.1) (Ne.symm hup)
      have huPos : (0 : ℝ) < (input.upper : ℝ) := by
        exact_mod_cast huPosRat
      have huPoint : (RationalEnclosure.point input.upper).Contains
          (input.upper : ℝ) := RationalEnclosure.contains_point input.upper
      have hlog := certificate.logChi.sound terms hparts.2 huPoint
      have hnum := RationalEnclosure.contains_mul huPoint hlog
      have hden : (RationalEnclosure.point (1 + input.upper)).Contains
          (1 + (input.upper : ℝ)) := by
        simpa using RationalEnclosure.contains_point (1 + input.upper)
      have hdenPos : (0 : ℚ) <
          (RationalEnclosure.point (1 + input.upper)).lower := by
        simpa [RationalEnclosure.point] using (show 0 < 1 + input.upper by linarith)
      have hquot := RationalEnclosure.contains_div hdenPos hnum hden
      have hendpoint : (endpointRaw terms input certificate).Contains
          (lrSmallSBridgeQChi (input.upper : ℝ)) := by
        simpa [endpointRaw, lrSmallSBridgeQChi] using hquot
      have huMem : (input.upper : ℝ) ∈ Icc (0 : ℝ) (1 / 4) := by
        constructor
        · exact huPos.le
        · have hcast : ((input.upper : ℚ) : ℝ) ≤
              ((((1 / 4 : ℚ) : ℚ)) : ℝ) := by
            exact_mod_cast hparts.1
          norm_num at hcast ⊢
          exact hcast
      have hchiMem : chi ∈ Icc (0 : ℝ) (1 / 4) :=
        ⟨hchiNonneg, hchi.2.trans huMem.2⟩
      have horder := lrSmallSBridgeQChi_antitoneOn_quarter
        hchiMem huMem hchi.2
      have hnonpos := lrSmallSBridgeQChi_nonpos
        ⟨hchiNonneg, hchiMem.2.trans (by norm_num)⟩
      have hbounds :
          ((endpointRaw terms input certificate).lower : ℝ) ≤
              lrSmallSBridgeQChi chi ∧ lrSmallSBridgeQChi chi ≤ 0 :=
        ⟨hendpoint.1.trans horder, hnonpos⟩
      simpa [enclosure, hlo, hup, RationalEnclosure.Contains] using hbounds
  · have hparts : (0 : ℚ) < input.lower ∧
        certificate.logChi.check input = true := by
      simpa [hlo] using hraw.2
    have hlog := certificate.logChi.sound terms hparts.2 hchi
    have hnum := RationalEnclosure.contains_mul hchi hlog
    have hone := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point 1) hchi
    have hdenPos : (0 : ℚ) <
        (RationalEnclosure.add
          (RationalEnclosure.point 1) input).lower := by
      dsimp [RationalEnclosure.add, RationalEnclosure.point]
      linarith
    have hquot := RationalEnclosure.contains_div hdenPos hnum hone
    simpa [enclosure, hlo, lrSmallSBridgeQChi] using hquot

def auto (logFuel : ℕ) (input : RationalEnclosure) :
    LRDeterminantIdealQChiCertificate :=
  { logChi := RationalEnclosure.autoLogIntervalCertificate logFuel
      (if input.lower = 0 then RationalEnclosure.point input.upper else input) }

end LRDeterminantIdealQChiCertificate

/-! ## The simultaneous three-target evaluator -/

structure LRDeterminantIdealEvaluatorCertificate where
  logTwo : RationalEnclosure.LogIntervalCertificate
  logFourThird : RationalEnclosure.LogIntervalCertificate
  logK : RationalEnclosure.LogIntervalCertificate
  logOnePlusK : RationalEnclosure.LogIntervalCertificate
  logOnePlusKChi : RationalEnclosure.LogIntervalCertificate
  logDArg : RationalEnclosure.LogIntervalCertificate
  hK : LRDeterminantIdealHCertificate
  hKChi : LRDeterminantIdealHCertificate
  qChi : LRDeterminantIdealQChiCertificate

namespace LRDeterminantIdealEvaluatorCertificate

def kI (box : CertificateBox) : RationalEnclosure := box.kInterval
def chiI (box : CertificateBox) : RationalEnclosure := box.chiInterval

def kChiI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative (kI box) (chiI box)

def onePlusChiI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) (chiI box)

def onePlusKI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) (kI box)

def onePlusKChiI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) (kChiI box)

def twoKI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative (RationalEnclosure.point 2) (kI box)

def dArgI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1)
    (RationalEnclosure.invPositive (twoKI box))

def fourKPlusThreeI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.mulNonnegative
      (RationalEnclosure.point 4) (kI box))
    (RationalEnclosure.point 3)

def logTwoI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.logTwo.enclosure terms

def logFourThirdI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.logFourThird.enclosure terms

def logKI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.logK.enclosure terms

def logOnePlusKI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.logOnePlusK.enclosure terms

def logOnePlusKChiI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.logOnePlusKChi.enclosure terms

def logDArgI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.logDArg.enclosure terms

def hKI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.hK.enclosure terms (kI box)

def hKChiI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.hKChi.enclosure terms (kChiI box)

def qChiI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure := certificate.qChi.enclosure terms (chiI box)

def l0I (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.scale 14 (logTwoI terms certificate)

def cI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.sub (RationalEnclosure.point 1)
      (RationalEnclosure.scale 2 (logTwoI terms certificate)))
    (RationalEnclosure.scale 16 (logFourThirdI terms certificate))

def aI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.add
      (RationalEnclosure.mul (chiI box)
        (logOnePlusKChiI terms certificate))
      (logOnePlusKI terms certificate))
    (onePlusChiI box)

def ahI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.add
      (RationalEnclosure.mul (chiI box) (hKChiI terms box certificate))
      (hKI terms box certificate))
    (onePlusChiI box)

def d0I (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.scale (1 / 2) (logDArgI terms certificate))
    (RationalEnclosure.invPositive (fourKPlusThreeI box))

def b0I (terms : ℕ) (_box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.scale (1 / 2) (l0I terms certificate))
      (logTwoI terms certificate))
    (RationalEnclosure.scale (1 / 2) (logOnePlusKI terms certificate))

def pI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.add (l0I terms certificate)
        (RationalEnclosure.scale 2 (logTwoI terms certificate)))
      (RationalEnclosure.point 1))
    (aI terms box certificate)

def gI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.add
        (RationalEnclosure.sub (l0I terms certificate)
          (logKI terms certificate))
        (RationalEnclosure.scale 2 (logTwoI terms certificate)))
      (RationalEnclosure.point 1))
    (qChiI terms box certificate)

def tI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.add (l0I terms certificate)
        (RationalEnclosure.scale 2 (logTwoI terms certificate)))
      (RationalEnclosure.point 1))
    (ahI terms box certificate)

def l0PlusCI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.add (l0I terms certificate) (cI terms certificate)

def coreI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.add
      (RationalEnclosure.mul (d0I terms box certificate)
        (pI terms box certificate))
      (RationalEnclosure.mul (b0I terms box certificate)
        (RationalEnclosure.sub (pI terms box certificate)
          (gI terms box certificate))))
    (RationalEnclosure.div
      (RationalEnclosure.mul
        (RationalEnclosure.sub (b0I terms box certificate)
          (d0I terms box certificate))
        (tI terms box certificate))
      (RationalEnclosure.mulNonnegative (RationalEnclosure.point 3)
        (l0PlusCI terms certificate)))

def bConstI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub (logTwoI terms certificate)
    (RationalEnclosure.scale (1 / 2) (logOnePlusKI terms certificate))

def sI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add (logKI terms certificate)
      (qChiI terms box certificate))
    (aI terms box certificate)

def t0I (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.scale 2 (logTwoI terms certificate))
      (RationalEnclosure.point 1))
    (ahI terms box certificate)

def lambdaI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.add
      (RationalEnclosure.scale 2 (d0I terms box certificate))
      (sI terms box certificate))
    (RationalEnclosure.point (1 / 3))

def c1I (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.scale (1 / 3)
    (RationalEnclosure.mul
      (RationalEnclosure.sub (t0I terms box certificate)
        (cI terms certificate))
      (RationalEnclosure.sub
        (RationalEnclosure.sub (bConstI terms certificate)
          (d0I terms box certificate))
        (RationalEnclosure.scale (1 / 2) (cI terms certificate))))

def derivativeI (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.scale (1 / 2) (lambdaI terms box certificate))
    (RationalEnclosure.div (c1I terms box certificate)
      (RationalEnclosure.mulNonnegative
        (l0PlusCI terms certificate) (l0PlusCI terms certificate)))

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    LRDeterminantIdealLeafResult where
  core := coreI terms box certificate
  derivative := derivativeI terms box certificate
  c1 := c1I terms box certificate

def payloadCheck (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) : Bool :=
  decide ((0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
      box.chiHi ≤ 1) &&
    decide ((0 : ℚ) < (onePlusChiI box).lower ∧
      (0 : ℚ) < (twoKI box).lower ∧
      (0 : ℚ) < (fourKPlusThreeI box).lower) &&
    certificate.logTwo.check (RationalEnclosure.point 2) &&
    certificate.logFourThird.check (RationalEnclosure.point (4 / 3)) &&
    certificate.logK.check (kI box) &&
    certificate.logOnePlusK.check (onePlusKI box) &&
    certificate.logOnePlusKChi.check (onePlusKChiI box) &&
    certificate.logDArg.check (dArgI box) &&
    certificate.hK.check (kI box) &&
    certificate.hKChi.check (kChiI box) &&
    certificate.qChi.check (chiI box) &&
    decide ((0 : ℚ) < (l0PlusCI terms certificate).lower)

structure Valid (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) : Prop where
  domain : (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
    box.chiHi ≤ 1
  denominators : (0 : ℚ) < (onePlusChiI box).lower ∧
    (0 : ℚ) < (twoKI box).lower ∧
    (0 : ℚ) < (fourKPlusThreeI box).lower
  logTwo : certificate.logTwo.check (RationalEnclosure.point 2) = true
  logFourThird : certificate.logFourThird.check
    (RationalEnclosure.point (4 / 3)) = true
  logK : certificate.logK.check (kI box) = true
  logOnePlusK : certificate.logOnePlusK.check (onePlusKI box) = true
  logOnePlusKChi : certificate.logOnePlusKChi.check
    (onePlusKChiI box) = true
  logDArg : certificate.logDArg.check (dArgI box) = true
  hK : certificate.hK.check (kI box) = true
  hKChi : certificate.hKChi.check (kChiI box) = true
  qChi : certificate.qChi.check (chiI box) = true
  l0PlusC : (0 : ℚ) < (l0PlusCI terms certificate).lower

theorem valid_of_payloadCheck
    {box : CertificateBox}
    {certificate : LRDeterminantIdealEvaluatorCertificate}
    (hcheck : certificate.payloadCheck terms box = true) :
    Valid terms box certificate := by
  have h :
      ((0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1) ∧
      ((0 : ℚ) < (onePlusChiI box).lower ∧
        (0 : ℚ) < (twoKI box).lower ∧
        (0 : ℚ) < (fourKPlusThreeI box).lower) ∧
      certificate.logTwo.check (RationalEnclosure.point 2) = true ∧
      certificate.logFourThird.check
        (RationalEnclosure.point (4 / 3)) = true ∧
      certificate.logK.check (kI box) = true ∧
      certificate.logOnePlusK.check (onePlusKI box) = true ∧
      certificate.logOnePlusKChi.check (onePlusKChiI box) = true ∧
      certificate.logDArg.check (dArgI box) = true ∧
      certificate.hK.check (kI box) = true ∧
      certificate.hKChi.check (kChiI box) = true ∧
      certificate.qChi.check (chiI box) = true ∧
      (0 : ℚ) < (l0PlusCI terms certificate).lower := by
    simpa [payloadCheck, and_assoc] using hcheck
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 1600000 in
theorem evaluate_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRDeterminantIdealEvaluatorCertificate}
    (hpoint : box.Contains point) (hvalid : Valid terms box certificate) :
    (certificate.evaluate terms box).core.Contains
        (lrDeterminantIdealCore lrDeterminantIdealDeepL0
          point.k point.chi) ∧
      (certificate.evaluate terms box).derivative.Contains
        (lrDeterminantIdealLDerivative lrDeterminantIdealDeepL0
          point.k point.chi) ∧
      (certificate.evaluate terms box).c1.Contains
        (lrDeterminantIdealC1 point.k point.chi) := by
  have hk : (kI box).Contains point.k :=
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchi : (chiI box).Contains point.chi :=
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hkLowerNonneg : (0 : ℚ) ≤ (kI box).lower := by
    simpa [kI, CertificateBox.kInterval] using hvalid.domain.1.le
  have hchiLowerNonneg : (0 : ℚ) ≤ (chiI box).lower := by
    simpa [chiI, CertificateBox.chiInterval] using hvalid.domain.2.2.1
  have hkchi := RationalEnclosure.contains_mulNonnegative
    hkLowerNonneg hchiLowerNonneg hk hchi
  have honeChi := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hchi
  have honeK := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hk
  have honeKChi := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hkchi
  have htwoK := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 2).lower)
    hkLowerNonneg (RationalEnclosure.contains_point 2) hk
  have hinvTwoK := RationalEnclosure.contains_invPositive
    hvalid.denominators.2.1 htwoK
  have hdArg := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hinvTwoK
  have hfourK := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 4).lower)
    hkLowerNonneg (RationalEnclosure.contains_point 4) hk
  have hfourKThree := RationalEnclosure.contains_add hfourK
    (RationalEnclosure.contains_point 3)
  have hlogTwo := certificate.logTwo.sound terms hvalid.logTwo
    (RationalEnclosure.contains_point 2)
  have hlogFourThird := certificate.logFourThird.sound terms
    hvalid.logFourThird (RationalEnclosure.contains_point (4 / 3))
  have hlogK := certificate.logK.sound terms hvalid.logK hk
  have hlogOneK := certificate.logOnePlusK.sound terms
    hvalid.logOnePlusK honeK
  have hlogOneKChi := certificate.logOnePlusKChi.sound terms
    hvalid.logOnePlusKChi honeKChi
  have hlogDArg := certificate.logDArg.sound terms hvalid.logDArg hdArg
  have hhK := certificate.hK.sound terms hvalid.hK hk
  have hhKChi := certificate.hKChi.sound terms hvalid.hKChi hkchi
  have hqChi := certificate.qChi.sound terms hvalid.qChi hchi
  have hL0 := RationalEnclosure.contains_scale (14 : ℚ) hlogTwo
  have hC := RationalEnclosure.contains_add
    (RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1)
      (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
    (RationalEnclosure.contains_scale (16 : ℚ) hlogFourThird)
  have hA := RationalEnclosure.contains_div hvalid.denominators.1
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hchi hlogOneKChi) hlogOneK)
    honeChi
  have hAH := RationalEnclosure.contains_div hvalid.denominators.1
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hchi hhKChi) hhK)
    honeChi
  have hD := RationalEnclosure.contains_add
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hlogDArg)
    (RationalEnclosure.contains_invPositive
      hvalid.denominators.2.2 hfourKThree)
  have hB := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (1 / 2 : ℚ) hL0) hlogTwo)
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hlogOneK)
  have hP := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_add hL0
        (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
      (RationalEnclosure.contains_point 1)) hA
  have hG := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_add
        (RationalEnclosure.contains_sub hL0 hlogK)
        (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
      (RationalEnclosure.contains_point 1)) hqChi
  have hT := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_add hL0
        (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
      (RationalEnclosure.contains_point 1)) hAH
  have hLC := RationalEnclosure.contains_add hL0 hC
  have hthreeLC := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 3).lower)
    hvalid.l0PlusC.le (RationalEnclosure.contains_point 3) hLC
  have hthreeLCLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative (RationalEnclosure.point 3)
        (l0PlusCI terms certificate)).lower := by
    dsimp [RationalEnclosure.mulNonnegative, RationalEnclosure.point]
    exact mul_pos (by norm_num) hvalid.l0PlusC
  have hcoreRaw := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hD hP)
      (RationalEnclosure.contains_mul hB
        (RationalEnclosure.contains_sub hP hG)))
    (RationalEnclosure.contains_div hthreeLCLower
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_sub hB hD) hT) hthreeLC)
  have hbConst := RationalEnclosure.contains_sub hlogTwo
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hlogOneK)
  have hS := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hlogK hqChi) hA
  have hT0 := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo)
      (RationalEnclosure.contains_point 1)) hAH
  have hLambda := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (2 : ℚ) hD) hS)
    (RationalEnclosure.contains_point (1 / 3))
  have hC1Raw := RationalEnclosure.contains_scale (1 / 3 : ℚ)
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_sub hT0 hC)
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_sub hbConst hD)
        (RationalEnclosure.contains_scale (1 / 2 : ℚ) hC)))
  have hLCSquare := RationalEnclosure.contains_mulNonnegative
    hvalid.l0PlusC.le hvalid.l0PlusC.le hLC hLC
  have hLCSquareLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative
        (l0PlusCI terms certificate) (l0PlusCI terms certificate)).lower := by
    dsimp [RationalEnclosure.mulNonnegative]
    exact mul_pos hvalid.l0PlusC hvalid.l0PlusC
  have hDerivativeRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hLambda)
    (RationalEnclosure.contains_div hLCSquareLower hC1Raw hLCSquare)
  have hcore : (coreI terms box certificate).Contains
      (lrDeterminantIdealCore lrDeterminantIdealDeepL0
        point.k point.chi) := by
    convert hcoreRaw using 1
    unfold lrDeterminantIdealCore lrDeterminantIdealD0
      lrDeterminantIdealB0 lrDeterminantIdealP lrDeterminantIdealG
      lrDeterminantIdealT lrDeterminantIdealA lrDeterminantIdealAH
      lrDeterminantIdealC lrDeterminantIdealDeepL0
    ring_nf
  have hc1 : (c1I terms box certificate).Contains
      (lrDeterminantIdealC1 point.k point.chi) := by
    convert hC1Raw using 1
    unfold lrDeterminantIdealC1 lrDeterminantIdealT0
      lrDeterminantIdealC lrDeterminantIdealBConst
      lrDeterminantIdealD0 lrDeterminantIdealAH
    ring_nf
  have hderivative : (derivativeI terms box certificate).Contains
      (lrDeterminantIdealLDerivative lrDeterminantIdealDeepL0
        point.k point.chi) := by
    convert hDerivativeRaw using 1
    unfold lrDeterminantIdealLDerivative lrDeterminantIdealLambda
      lrDeterminantIdealS lrDeterminantIdealC1 lrDeterminantIdealT0
      lrDeterminantIdealC lrDeterminantIdealBConst
      lrDeterminantIdealD0 lrDeterminantIdealA lrDeterminantIdealAH
      lrDeterminantIdealDeepL0
    ring_nf
  exact ⟨hcore, hderivative, hc1⟩

def accepts (terms : ℕ) (margin : ℚ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) : Bool :=
  certificate.payloadCheck terms box &&
    (certificate.evaluate terms box).check margin

theorem accepts_sound
    (terms : ℕ) (margin : ℚ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRDeterminantIdealEvaluatorCertificate}
    (hpoint : box.Contains point)
    (haccept : certificate.accepts terms margin box = true) :
    LRDeterminantIdealEndpointProperties lrDeterminantIdealDeepL0
      (margin : ℝ) point := by
  have hparts : certificate.payloadCheck terms box = true ∧
      (certificate.evaluate terms box).check margin = true := by
    simpa [accepts] using haccept
  have hsound := evaluate_sound terms hpoint
    (valid_of_payloadCheck hparts.1)
  exact LRDeterminantIdealLeafResult.sound hparts.2
    hsound.1 hsound.2.1 hsound.2.2

def auto (logFuel : ℕ) (box : CertificateBox) :
    LRDeterminantIdealEvaluatorCertificate :=
  let k := kI box
  let chi := chiI box
  let kchi := kChiI box
  { logTwo := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.point 2)
    logFourThird := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.point (4 / 3))
    logK := RationalEnclosure.autoLogIntervalCertificate logFuel k
    logOnePlusK := RationalEnclosure.autoLogIntervalCertificate logFuel
      (onePlusKI box)
    logOnePlusKChi := RationalEnclosure.autoLogIntervalCertificate logFuel
      (onePlusKChiI box)
    logDArg := RationalEnclosure.autoLogIntervalCertificate logFuel
      (dArgI box)
    hK := LRDeterminantIdealHCertificate.auto logFuel k
    hKChi := LRDeterminantIdealHCertificate.auto logFuel kchi
    qChi := LRDeterminantIdealQChiCertificate.auto logFuel chi }

def autoAccepts (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  let certificate := auto logFuel box
  certificate.accepts terms margin box

theorem autoAccepts_sound
    (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) (_unit : Unit)
    (haccept : autoAccepts terms logFuel margin box () = true) :
    ∀ point, box.Contains point →
      LRDeterminantIdealEndpointProperties lrDeterminantIdealDeepL0
        (margin : ℝ) point := by
  intro point hpoint
  exact accepts_sound terms margin hpoint
    (by simpa [autoAccepts] using haccept)

/-- End-to-end soundness for a generated ideal-core tree.  Invalid proposed
range reductions simply make the Boolean traversal fail. -/
theorem subdivision_sound
    {Relevant : CertificatePoint → Prop} {DiscardData : Type}
    (terms logFuel : ℕ) (margin : ℚ)
    {discardBox : CertificateBox → DiscardData → Bool}
    (discardSound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {tree : SubdivisionCertificate Unit DiscardData}
    (hcheck : tree.check (autoAccepts terms logFuel margin)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point →
      LRDeterminantIdealEndpointProperties lrDeterminantIdealDeepL0
        (margin : ℝ) point := by
  exact subdivisionCertificate_sound
    (Relevant := Relevant)
    (Property := LRDeterminantIdealEndpointProperties
      lrDeterminantIdealDeepL0 (margin : ℝ))
    (acceptBox := autoAccepts terms logFuel margin)
    (discardBox := discardBox)
    (fun leaf data h ↦ autoAccepts_sound terms logFuel margin leaf data h)
    discardSound hcheck

/-- The generated endpoint tree immediately propagates to every larger
logarithmic scale through the exact DA2 identity. -/
theorem subdivision_propagated
    {Relevant : CertificatePoint → Prop} {DiscardData : Type}
    (terms logFuel : ℕ) (margin : ℚ) {L : ℝ}
    (hL : lrDeterminantIdealDeepL0 ≤ L)
    {discardBox : CertificateBox → DiscardData → Bool}
    (discardSound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {tree : SubdivisionCertificate Unit DiscardData}
    (hcheck : tree.check (autoAccepts terms logFuel margin)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point →
      (margin : ℝ) < lrDeterminantIdealCore L point.k point.chi := by
  intro point hpoint hrelevant
  have hendpoint := subdivision_sound terms logFuel margin
    discardSound hcheck point hpoint hrelevant
  exact lrDeterminantIdealCore_gt_of_endpointProperties
    lrDeterminantIdealDeepL0_add_C_pos hL hendpoint

end LRDeterminantIdealEvaluatorCertificate

end CourtadeKumar
