import InformationTheory.CourtadeKumar.IntervalCertificateAssembly
import InformationTheory.CourtadeKumar.LRSmallSBridgeChi

/-!
# Kernel-checked certificate interface for the bounded determinant ideal core

This module isolates the exact interface needed to replay the
bounded-`k` part of the audited deep determinant certificate.  A leaf checks
three rational enclosures simultaneously:

* the ideal core at the endpoint `L₀`;
* its exact separated-form `L` derivative;
* the coefficient `C₁` controlling propagation away from `L₀`.

The checker is Boolean and kernel executable.  Its soundness theorem is
combined below with the exact separation identity (DA2), an algebraic
propagation theorem, and the two rational restoration ledgers (DA3)--(DA4).

This is certificate infrastructure: a concrete interval evaluator and tree,
and the analytic ideal-to-true restoration inequalities, remain explicit
downstream obligations.
-/

open Set

namespace CourtadeKumar

/-! ## The exact logarithmic ideal core -/

/-- The continuous endpoint convention for
`h(1+t) = (1+t) log(1+t) / t`. -/
noncomputable def lrDeterminantIdealH (t : ℝ) : ℝ :=
  if t = 0 then 1 else (1 + t) * Real.log (1 + t) / t

/-- The constant `C = 1 - 2 log 2 + 16 log(4/3)` in (DA2). -/
noncomputable def lrDeterminantIdealC : ℝ :=
  1 - 2 * Real.log 2 + 16 * Real.log (4 / 3)

noncomputable def lrDeterminantIdealA (k chi : ℝ) : ℝ :=
  (chi * Real.log (1 + k * chi) + Real.log (1 + k)) / (1 + chi)

noncomputable def lrDeterminantIdealAH (k chi : ℝ) : ℝ :=
  (chi * lrDeterminantIdealH (k * chi) + lrDeterminantIdealH k) /
    (1 + chi)

noncomputable def lrDeterminantIdealD0 (k : ℝ) : ℝ :=
  Real.log (1 + 1 / (2 * k)) / 2 + 1 / (4 * k + 3)

noncomputable def lrDeterminantIdealB0 (L k : ℝ) : ℝ :=
  L / 2 + Real.log 2 - Real.log (1 + k) / 2

noncomputable def lrDeterminantIdealP (L k chi : ℝ) : ℝ :=
  L + 2 * Real.log 2 + 1 - lrDeterminantIdealA k chi

noncomputable def lrDeterminantIdealG (L k chi : ℝ) : ℝ :=
  L - Real.log k + 2 * Real.log 2 + 1 -
    lrSmallSBridgeQChi chi

noncomputable def lrDeterminantIdealT (L k chi : ℝ) : ℝ :=
  L + 2 * Real.log 2 + 1 - lrDeterminantIdealAH k chi

/-- The ideal normalized determinant `E₀` before finite-`s`, channel, and
entropy-remainder restoration. -/
noncomputable def lrDeterminantIdealCore (L k chi : ℝ) : ℝ :=
  let D := lrDeterminantIdealD0 k
  let B := lrDeterminantIdealB0 L k
  let p := lrDeterminantIdealP L k chi
  let g := lrDeterminantIdealG L k chi
  let t := lrDeterminantIdealT L k chi
  D * p + B * (p - g) +
    (B - D) * t / (3 * (L + lrDeterminantIdealC))

/-- The `L`-independent coefficient `b` in `B₀=L/2+b`. -/
noncomputable def lrDeterminantIdealBConst (k : ℝ) : ℝ :=
  Real.log 2 - Real.log (1 + k) / 2

noncomputable def lrDeterminantIdealS (k chi : ℝ) : ℝ :=
  Real.log k + lrSmallSBridgeQChi chi - lrDeterminantIdealA k chi

noncomputable def lrDeterminantIdealT0 (k chi : ℝ) : ℝ :=
  2 * Real.log 2 + 1 - lrDeterminantIdealAH k chi

noncomputable def lrDeterminantIdealLambda (k chi : ℝ) : ℝ :=
  2 * lrDeterminantIdealD0 k + lrDeterminantIdealS k chi + 1 / 3

noncomputable def lrDeterminantIdealRInf (k chi : ℝ) : ℝ :=
  let D := lrDeterminantIdealD0 k
  let b := lrDeterminantIdealBConst k
  let P := 2 * Real.log 2 + 1 - lrDeterminantIdealA k chi
  let S := lrDeterminantIdealS k chi
  let T0 := lrDeterminantIdealT0 k chi
  D * P + b * S + (T0 - lrDeterminantIdealC) / 6 + (b - D) / 3

noncomputable def lrDeterminantIdealC1 (k chi : ℝ) : ℝ :=
  (lrDeterminantIdealT0 k chi - lrDeterminantIdealC) *
    (lrDeterminantIdealBConst k - lrDeterminantIdealD0 k -
      lrDeterminantIdealC / 2) / 3

/-- The exact derivative appearing in (DA2). -/
noncomputable def lrDeterminantIdealLDerivative (L k chi : ℝ) : ℝ :=
  lrDeterminantIdealLambda k chi / 2 -
    lrDeterminantIdealC1 k chi / (L + lrDeterminantIdealC) ^ 2

/-- Exact separation identity (DA2), independent of any numerical replay. -/
theorem lrDeterminantIdealCore_eq_separated
    {L k chi : ℝ} (hden : L + lrDeterminantIdealC ≠ 0) :
    lrDeterminantIdealCore L k chi =
      L * lrDeterminantIdealLambda k chi / 2 +
        lrDeterminantIdealRInf k chi +
        lrDeterminantIdealC1 k chi /
          (L + lrDeterminantIdealC) := by
  unfold lrDeterminantIdealCore lrDeterminantIdealLambda
    lrDeterminantIdealRInf lrDeterminantIdealC1
    lrDeterminantIdealB0 lrDeterminantIdealBConst
    lrDeterminantIdealP lrDeterminantIdealG lrDeterminantIdealT
    lrDeterminantIdealS lrDeterminantIdealT0
  field_simp [hden]
  ring

/-! ## Exact propagation from one checked logarithmic endpoint -/

/-- Pure algebra behind the monotone propagation in (DA2).  In particular,
no numerical differentiation or untrusted computation is used here. -/
theorem separatedIdealCore_strictMono_from_endpoint
    {L0 L Lambda RInf C C1 margin : ℝ}
    (hbase : 0 < L0 + C) (hL : L0 ≤ L) (hC1 : 0 ≤ C1)
    (hendpoint : margin < L0 * Lambda / 2 + RInf + C1 / (L0 + C))
    (hderivative : 0 < Lambda / 2 - C1 / (L0 + C) ^ 2) :
    margin < L * Lambda / 2 + RInf + C1 / (L + C) := by
  have htop : 0 < L + C := by linarith
  have hprod : (L0 + C) ^ 2 ≤ (L0 + C) * (L + C) := by
    nlinarith
  have hquot : C1 / ((L0 + C) * (L + C)) ≤
      C1 / (L0 + C) ^ 2 := by
    exact div_le_div_of_nonneg_left hC1 (sq_pos_of_pos hbase) hprod
  have hfactor : 0 < Lambda / 2 -
      C1 / ((L0 + C) * (L + C)) := by
    linarith
  have hdelta : 0 ≤ (L - L0) *
      (Lambda / 2 - C1 / ((L0 + C) * (L + C))) :=
    mul_nonneg (sub_nonneg.mpr hL) hfactor.le
  have hid :
      L * Lambda / 2 + RInf + C1 / (L + C) =
        (L0 * Lambda / 2 + RInf + C1 / (L0 + C)) +
          (L - L0) *
            (Lambda / 2 - C1 / ((L0 + C) * (L + C))) := by
    field_simp [hbase.ne', htop.ne']
    ring
  rw [hid]
  linarith

/-- The endpoint triple used by every accepted bounded-`k` ideal-core leaf. -/
def LRDeterminantIdealEndpointProperties
    (L0 margin : ℝ) (point : CertificatePoint) : Prop :=
  margin < lrDeterminantIdealCore L0 point.k point.chi ∧
    0 < lrDeterminantIdealLDerivative L0 point.k point.chi ∧
    0 ≤ lrDeterminantIdealC1 point.k point.chi

theorem lrDeterminantIdealCore_gt_of_endpointProperties
    {L0 L margin : ℝ} {point : CertificatePoint}
    (hbase : 0 < L0 + lrDeterminantIdealC)
    (hL : L0 ≤ L)
    (hendpoint : LRDeterminantIdealEndpointProperties L0 margin point) :
    margin < lrDeterminantIdealCore L point.k point.chi := by
  have htop : 0 < L + lrDeterminantIdealC := by linarith
  rcases hendpoint with ⟨hcore, hderivative, hc1⟩
  rw [lrDeterminantIdealCore_eq_separated hbase.ne'] at hcore
  rw [lrDeterminantIdealCore_eq_separated htop.ne']
  apply separatedIdealCore_strictMono_from_endpoint
      hbase hL hc1 hcore
  simpa [lrDeterminantIdealLDerivative] using hderivative

/-- The fixed logarithmic endpoint used by both bounded deep replays. -/
noncomputable def lrDeterminantIdealDeepL0 : ℝ := 14 * Real.log 2

theorem lrDeterminantIdealDeepL0_add_C_pos :
    0 < lrDeterminantIdealDeepL0 + lrDeterminantIdealC := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogFourThird : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  unfold lrDeterminantIdealDeepL0 lrDeterminantIdealC
  nlinarith

/-! ## A simultaneous, kernel-executable accepted-leaf checker -/

/-- Rational output of one bounded determinant ideal-core leaf. -/
structure LRDeterminantIdealLeafResult where
  core : RationalEnclosure
  derivative : RationalEnclosure
  c1 : RationalEnclosure

namespace LRDeterminantIdealLeafResult

/-- The leaf is accepted only when all three propagated targets have the
required rational signs. -/
def check (margin : ℚ) (result : LRDeterminantIdealLeafResult) : Bool :=
  decide (margin < result.core.lower ∧
    0 < result.derivative.lower ∧ 0 ≤ result.c1.lower)

theorem sound
    {L0 : ℝ} {margin : ℚ} {point : CertificatePoint}
    {result : LRDeterminantIdealLeafResult}
    (hcheck : result.check margin = true)
    (hcore : result.core.Contains
      (lrDeterminantIdealCore L0 point.k point.chi))
    (hderivative : result.derivative.Contains
      (lrDeterminantIdealLDerivative L0 point.k point.chi))
    (hc1 : result.c1.Contains
      (lrDeterminantIdealC1 point.k point.chi)) :
    LRDeterminantIdealEndpointProperties L0 (margin : ℝ) point := by
  have hparts : margin < result.core.lower ∧
      0 < result.derivative.lower ∧ 0 ≤ result.c1.lower := by
    simpa [check] using hcheck
  have hcoreLower : (margin : ℝ) < (result.core.lower : ℝ) := by
    exact_mod_cast hparts.1
  have hderivativeLower : (0 : ℝ) < (result.derivative.lower : ℝ) := by
    exact_mod_cast hparts.2.1
  have hc1Lower : (0 : ℝ) ≤ (result.c1.lower : ℝ) := by
    exact_mod_cast hparts.2.2
  constructor
  · exact hcoreLower.trans_le hcore.1
  constructor
  · exact hderivativeLower.trans_le hderivative.1
  · exact hc1Lower.trans hc1.1

end LRDeterminantIdealLeafResult

/-- Soundness contract for the target-specific ideal-core interval
evaluator.  The evaluator itself can be generated automatically, but this
contract forces the kernel proof to connect all three output intervals to
the exact real formulas above. -/
structure LRDeterminantIdealLeafEvaluatorSound
    {AcceptData : Type}
    (L0 : ℝ)
    (evaluate : CertificateBox → AcceptData →
      LRDeterminantIdealLeafResult) : Prop where
  core : ∀ box data point, box.Contains point →
    (evaluate box data).core.Contains
      (lrDeterminantIdealCore L0 point.k point.chi)
  derivative : ∀ box data point, box.Contains point →
    (evaluate box data).derivative.Contains
      (lrDeterminantIdealLDerivative L0 point.k point.chi)
  c1 : ∀ box data point, box.Contains point →
    (evaluate box data).c1.Contains
      (lrDeterminantIdealC1 point.k point.chi)

def lrDeterminantIdealLeafAccepts
    {AcceptData : Type}
    (margin : ℚ)
    (evaluate : CertificateBox → AcceptData →
      LRDeterminantIdealLeafResult)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  (evaluate box data).check margin

/-- End-to-end subdivision soundness for the simultaneous ideal-core
endpoint replay.  Discarded boxes are permitted only through a separately
proved relevance checker. -/
theorem lrDeterminantIdealSubdivision_sound
    {Relevant : CertificatePoint → Prop}
    {AcceptData DiscardData : Type}
    {L0 : ℝ} {margin : ℚ}
    {evaluate : CertificateBox → AcceptData →
      LRDeterminantIdealLeafResult}
    {discardBox : CertificateBox → DiscardData → Bool}
    (evaluateSound : LRDeterminantIdealLeafEvaluatorSound L0 evaluate)
    (discardSound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {tree : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : tree.check
      (lrDeterminantIdealLeafAccepts margin evaluate)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point →
      LRDeterminantIdealEndpointProperties L0 (margin : ℝ) point := by
  apply subdivisionCertificate_sound
      (Relevant := Relevant)
      (Property := LRDeterminantIdealEndpointProperties L0 (margin : ℝ))
      (acceptBox := lrDeterminantIdealLeafAccepts margin evaluate)
      (discardBox := discardBox)
      (box := box) (certificate := tree) ?_ discardSound hcheck
  intro leaf data hleaf point hpoint
  exact LRDeterminantIdealLeafResult.sound hleaf
    (evaluateSound.core leaf data point hpoint)
    (evaluateSound.derivative leaf data point hpoint)
    (evaluateSound.c1 leaf data point hpoint)

/-- A successful endpoint subdivision replay automatically proves the ideal
core margin at every larger logarithmic scale. -/
theorem lrDeterminantIdealSubdivision_propagated
    {Relevant : CertificatePoint → Prop}
    {AcceptData DiscardData : Type}
    {L : ℝ} {margin : ℚ}
    {evaluate : CertificateBox → AcceptData →
      LRDeterminantIdealLeafResult}
    {discardBox : CertificateBox → DiscardData → Bool}
    (hL : lrDeterminantIdealDeepL0 ≤ L)
    (evaluateSound : LRDeterminantIdealLeafEvaluatorSound
      lrDeterminantIdealDeepL0 evaluate)
    (discardSound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {tree : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : tree.check
      (lrDeterminantIdealLeafAccepts margin evaluate)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point →
      (margin : ℝ) < lrDeterminantIdealCore L point.k point.chi := by
  intro point hpoint hRelevant
  have hendpoint := lrDeterminantIdealSubdivision_sound
    evaluateSound discardSound hcheck point hpoint hRelevant
  exact lrDeterminantIdealCore_gt_of_endpointProperties
    lrDeterminantIdealDeepL0_add_C_pos hL hendpoint

/-! ## Exact restoration ledgers -/

/-- Complete audited loss budget (DA3), valid on the bounded band
`k ≤ 16`. -/
def lrDeterminantLowBandRestorationBudget : ℚ :=
  27017301 / 2684354560 +
    51 / 50 * (1 / 2 ^ 10) * (49 / 5 + 1 / 2 ^ 14) +
    51 / 100 * (1 / 2 ^ 14) * (49 / 5 + 4 / 5) +
    1 / 10240 + 3 / 5120 + 91 / 40960 + 1 / 1000000

theorem lrDeterminantLowBandRestorationBudget_exact :
    lrDeterminantLowBandRestorationBudget =
      193464268233 / 8388608000000 := by
  norm_num [lrDeterminantLowBandRestorationBudget]

theorem lrDeterminantLowBandRestorationBudget_lt :
    lrDeterminantLowBandRestorationBudget < 1 / 40 := by
  rw [lrDeterminantLowBandRestorationBudget_exact]
  norm_num

/-- Sharpened audited loss budget (DA4), valid on `16 ≤ k ≤ 128`. -/
def lrDeterminantHighBandRestorationBudget : ℚ :=
  8656817 / 440401920 +
    (1 / 2 ^ 7) / 80 +
    51 / 100 * (1 / 2 ^ 14) * (49 / 5 + 4 / 5) +
    (1 / 2 ^ 7) / 10 + 3 / 5 * (1 / 2 ^ 7) +
    91 / 40960 + 1 / 1000000

theorem lrDeterminantHighBandRestorationBudget_exact :
    lrDeterminantHighBandRestorationBudget =
      38226433381 / 1376256000000 := by
  norm_num [lrDeterminantHighBandRestorationBudget]

theorem lrDeterminantHighBandRestorationBudget_lt :
    lrDeterminantHighBandRestorationBudget < 3 / 100 := by
  rw [lrDeterminantHighBandRestorationBudget_exact]
  norm_num

/-- Transfer the checked `3/5` ideal margin through the complete low-band
restoration ledger.  The remaining analytic restoration proof need only
establish the single displayed loss inequality. -/
theorem lrDeterminantRestored_gt_twenty_three_fortieths
    {ideal actual : ℝ}
    (hideal : 3 / 5 < ideal)
    (hloss : ideal - actual ≤
      (lrDeterminantLowBandRestorationBudget : ℝ)) :
    23 / 40 < actual := by
  have hbudget : (lrDeterminantLowBandRestorationBudget : ℝ) < 1 / 40 := by
    norm_num [lrDeterminantLowBandRestorationBudget]
  linarith

/-- Transfer the checked `1/2` ideal margin through the sharpened high-band
restoration ledger. -/
theorem lrDeterminantRestored_gt_forty_seven_hundredths
    {ideal actual : ℝ}
    (hideal : 1 / 2 < ideal)
    (hloss : ideal - actual ≤
      (lrDeterminantHighBandRestorationBudget : ℝ)) :
    47 / 100 < actual := by
  have hbudget : (lrDeterminantHighBandRestorationBudget : ℝ) < 3 / 100 := by
    norm_num [lrDeterminantHighBandRestorationBudget]
  linarith

end CourtadeKumar
