import InformationTheory.CourtadeKumar.LRDeterminantIdealMeanValueEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantIdealSharedPrimitiveAD
import InformationTheory.CourtadeKumar.LRDeterminantIdealSharedPrimitiveADSoundness
import InformationTheory.CourtadeKumar.LRDeterminantIdealNaturalOracle

/-!
# Centered mean-value oracles for the two ideal replays

This scratch module is the final executable adapter between the shared
positive-`chi` interval-AD graph and the compact natural/mean replay trees.
Each mean leaf carries two independently checked payloads:

* a payload evaluated on the singleton rational center, supplying values;
* a payload evaluated on the whole box, supplying derivative enclosures.

The `chi = 0` face remains on the independent zero-aware natural evaluator.
Every proposal is reconstructed deterministically and then checked by the
ordinary rational/logarithm checkers before any soundness theorem is used.
-/

namespace CourtadeKumar
namespace LRIdealCenteredMeanOracle

open LRLowKIdealMeanValue
open LRLowKIdealSharedPrimitiveAD
open LRLowKIdealSharedPrimitiveADSoundness

abbrev SharedPayload := LRLowKIdealSharedPrimitiveAD.Payload

/-! ## Singleton-center boxes and paired payloads -/

/-- The exact rational singleton at the midpoint of a certificate box. -/
def centerBox (box : CertificateBox) : CertificateBox :=
  let s := RationalEnclosure.center box.sInterval
  let k := RationalEnclosure.center box.kInterval
  let chi := RationalEnclosure.center box.chiInterval
  { sLo := s, sHi := s, kLo := k, kHi := k,
    chiLo := chi, chiHi := chi }

theorem centerBox_contains_midpoint (box : CertificateBox) :
    (centerBox box).Contains box.midpoint := by
  simp [centerBox, CertificateBox.midpoint, CertificateBox.Contains]

/-- Separate checked proposals for center values and whole-box partials. -/
structure CenteredPayload where
  center : SharedPayload
  full : SharedPayload

namespace CenteredPayload

/-- Deterministic proposal generation.  Neither proposal is trusted: the
combined Boolean check below reruns all of its primitive checks. -/
def auto (logFuel : ℕ) (box : CertificateBox) : CenteredPayload where
  center := LRLowKIdealSharedPrimitiveAD.Payload.auto logFuel (centerBox box)
  full := LRLowKIdealSharedPrimitiveAD.Payload.auto logFuel box

end CenteredPayload

/-- Mean leaves are strictly positive-`chi` leaves.  In addition to the
explicit face check, both the singleton-center and whole-box shared graphs
must pass their complete payload checks. -/
def payloadCheck (terms : ℕ) (config : Config) (box : CertificateBox)
    (payload : CenteredPayload) : Bool :=
  decide ((0 : ℚ) < box.chiLo) &&
    (fullPayloadCheck terms config (centerBox box) payload.center &&
      fullPayloadCheck terms config box payload.full)

structure CenteredPayload.Valid (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : CenteredPayload) : Prop where
  positiveChi : (0 : ℚ) < box.chiLo
  center : FullValid terms config (centerBox box) payload.center
  full : FullValid terms config box payload.full

theorem CenteredPayload.valid_of_payloadCheck
    {terms : ℕ} {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hcheck : payloadCheck terms config box payload = true) :
    payload.Valid terms config box := by
  have hparts :
      (0 : ℚ) < box.chiLo ∧
        fullPayloadCheck terms config (centerBox box) payload.center = true ∧
        fullPayloadCheck terms config box payload.full = true := by
    simpa [payloadCheck, Bool.and_eq_true] using hcheck
  exact ⟨hparts.1, fullValid_of_check hparts.2.1,
    fullValid_of_check hparts.2.2⟩

/-! ## Center values combined with whole-box derivatives -/

def toADTriple (result : TargetADTriple) : ADTriple where
  first := result.first
  second := result.second
  third := result.third

/-- The precise correlated mean-value payload: values come from the center
graph, while all three partial intervals come from the full graph. -/
def evaluate (terms : ℕ) (config : Config) (box : CertificateBox)
    (payload : CenteredPayload) : MidpointTriple :=
  MidpointTriple.ofAD
    (toADTriple
      (evaluateTargets terms config (centerBox box) payload.center))
    (toADTriple
      (evaluateTargets terms config box payload.full))

/-- The target triple represented by a shared graph configuration. -/
noncomputable def sharedTargets (config : Config) : TargetTriple where
  first := targetFirst config
  second := targetSecond config
  third := targetThird config

theorem firstValue_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hvalid : payload.Valid terms config box) :
    (evaluate terms config box payload).first.value.Contains
      ((sharedTargets config).first box.midpoint) := by
  have hcenter := evaluateTargets_sound terms hvalid.center
    (centerBox_contains_midpoint box)
  simpa [evaluate, toADTriple, MidpointTriple.ofAD, sharedTargets] using
    hcenter.1.1

theorem secondValue_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hvalid : payload.Valid terms config box) :
    (evaluate terms config box payload).second.value.Contains
      ((sharedTargets config).second box.midpoint) := by
  have hcenter := evaluateTargets_sound terms hvalid.center
    (centerBox_contains_midpoint box)
  simpa [evaluate, toADTriple, MidpointTriple.ofAD, sharedTargets] using
    hcenter.2.1.1

theorem thirdValue_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hvalid : payload.Valid terms config box) :
    (evaluate terms config box payload).third.value.Contains
      ((sharedTargets config).third box.midpoint) := by
  have hcenter := evaluateTargets_sound terms hvalid.center
    (centerBox_contains_midpoint box)
  simpa [evaluate, toADTriple, MidpointTriple.ofAD, sharedTargets] using
    hcenter.2.2.1

/-- Changing only the midpoint value enclosure does not change a verified
family of derivative enclosures. -/
def derivativeEnclosures_replaceValue
    {target : CertificatePoint → ℝ} {box : CertificateBox}
    {certificate : MidpointCertificate}
    (data : BoxDerivativeEnclosures target box certificate)
    (value : RationalEnclosure) :
    BoxDerivativeEnclosures target box { certificate with value := value } where
  partialS := data.partialS
  partialK := data.partialK
  partialChi := data.partialChi
  derivS := data.derivS
  derivK := data.derivK
  derivChi := data.derivChi
  boundS := data.boundS
  boundK := data.boundK
  boundChi := data.boundChi

noncomputable def firstDerivatives
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hvalid : payload.Valid terms config box) :
    BoxDerivativeEnclosures (sharedTargets config).first box
      (evaluate terms config box payload).first := by
  have hbase := first_boxDerivativeEnclosures terms hvalid.full
  have hcentered := derivativeEnclosures_replaceValue hbase
    (evaluateTargets terms config (centerBox box) payload.center).first.value
  simpa [evaluate, toADTriple, MidpointTriple.ofAD, sharedTargets,
    firstMidpointCertificate] using hcentered

noncomputable def secondDerivatives
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hvalid : payload.Valid terms config box) :
    BoxDerivativeEnclosures (sharedTargets config).second box
      (evaluate terms config box payload).second := by
  have hbase := second_boxDerivativeEnclosures terms hvalid.full
  have hcentered := derivativeEnclosures_replaceValue hbase
    (evaluateTargets terms config (centerBox box) payload.center).second.value
  simpa [evaluate, toADTriple, MidpointTriple.ofAD, sharedTargets,
    secondMidpointCertificate] using hcentered

noncomputable def thirdDerivatives
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : CenteredPayload}
    (hvalid : payload.Valid terms config box) :
    BoxDerivativeEnclosures (sharedTargets config).third box
      (evaluate terms config box payload).third := by
  have hbase := third_boxDerivativeEnclosures terms hvalid.full
  have hcentered := derivativeEnclosures_replaceValue hbase
    (evaluateTargets terms config (centerBox box) payload.center).third.value
  simpa [evaluate, toADTriple, MidpointTriple.ofAD, sharedTargets,
    thirdMidpointCertificate] using hcentered

/-! ## Generic and replay-specific mean oracles -/

noncomputable def meanOracle (terms : ℕ) (config : Config) :
    MeanOracle (sharedTargets config) where
  Payload := CenteredPayload
  payloadCheck := payloadCheck terms config
  evaluate := evaluate terms config
  firstValue_sound := by
    intro box payload hcheck
    exact firstValue_sound terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  firstDerivatives := by
    intro box payload hcheck
    exact firstDerivatives terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  secondValue_sound := by
    intro box payload hcheck
    exact secondValue_sound terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  secondDerivatives := by
    intro box payload hcheck
    exact secondDerivatives terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  thirdValue_sound := by
    intro box payload hcheck
    exact thirdValue_sound terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  thirdDerivatives := by
    intro box payload hcheck
    exact thirdDerivatives terms
      (CenteredPayload.valid_of_payloadCheck hcheck)

/-- Reindex the shared centered evaluator along extensional equality of its
three targets.  Its payload type is stated explicitly, so the deterministic
constructor remains definitionally visible to the final `AutoOracle`. -/
noncomputable def meanOracleAs
    (terms : ℕ) (config : Config) (target : TargetTriple)
    (h : sharedTargets config = target) : MeanOracle target where
  Payload := CenteredPayload
  payloadCheck := payloadCheck terms config
  evaluate := evaluate terms config
  firstValue_sound := by
    intro box payload hcheck
    rw [← h]
    exact firstValue_sound terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  firstDerivatives := by
    intro box payload hcheck
    rw [← h]
    exact firstDerivatives terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  secondValue_sound := by
    intro box payload hcheck
    rw [← h]
    exact secondValue_sound terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  secondDerivatives := by
    intro box payload hcheck
    rw [← h]
    exact secondDerivatives terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  thirdValue_sound := by
    intro box payload hcheck
    rw [← h]
    exact thirdValue_sound terms
      (CenteredPayload.valid_of_payloadCheck hcheck)
  thirdDerivatives := by
    intro box payload hcheck
    rw [← h]
    exact thirdDerivatives terms
      (CenteredPayload.valid_of_payloadCheck hcheck)

theorem targetTriple_ext
    {left right : TargetTriple}
    (hfirst : left.first = right.first)
    (hsecond : left.second = right.second)
    (hthird : left.third = right.third) : left = right := by
  cases left
  cases right
  simp_all

theorem sharedTargets_lowKMiddle :
    sharedTargets lowKMiddleConfig = middleTargets := by
  apply targetTriple_ext
  · funext point
    norm_num [sharedTargets, targetFirst, lowKMiddleConfig, Config.l0,
      middleTargets, lrLowKIdealL0]
  · funext point
    norm_num [sharedTargets, targetSecond, lowKMiddleConfig, Config.l0,
      middleTargets, lrLowKIdealL0]
  · funext point
    norm_num [sharedTargets, targetThird, lowKMiddleConfig, Config.l0,
      middleTargets, lrLowKIdealL0]

theorem sharedTargets_lowKUpper :
    sharedTargets lowKUpperConfig = upperTargets := by
  apply targetTriple_ext
  · funext point
    norm_num [sharedTargets, targetFirst, lowKUpperConfig, Config.l0,
      upperTargets, lrLowKIdealL0]
  · funext point
    norm_num [sharedTargets, targetSecond, lowKUpperConfig, Config.l0,
      upperTargets, lrLowKIdealL0]
  · funext point
    norm_num [sharedTargets, targetThird, lowKUpperConfig, Config.l0,
      upperTargets, lrLowKIdealL0]

theorem sharedTargets_restricted :
    sharedTargets restrictedEndpointConfig = restrictedTargets := by
  apply targetTriple_ext
  · funext point
    norm_num [sharedTargets, targetFirst, restrictedEndpointConfig,
      Config.l0, restrictedTargets, lrDeterminantIdealDeepL0]
  · funext point
    norm_num [sharedTargets, targetSecond, restrictedEndpointConfig,
      Config.l0, restrictedTargets, lrDeterminantIdealDeepL0]
  · funext point
    norm_num [sharedTargets, targetThird, restrictedEndpointConfig,
      Config.l0, restrictedTargets, lrDeterminantIdealDeepL0]

noncomputable def middleMeanOracle (terms : ℕ) :
    MeanOracle middleTargets :=
  meanOracleAs terms lowKMiddleConfig middleTargets
    sharedTargets_lowKMiddle

noncomputable def upperMeanOracle (terms : ℕ) :
    MeanOracle upperTargets :=
  meanOracleAs terms lowKUpperConfig upperTargets
    sharedTargets_lowKUpper

noncomputable def restrictedMeanOracle (terms : ℕ) :
    MeanOracle restrictedTargets :=
  meanOracleAs terms restrictedEndpointConfig restrictedTargets
    sharedTargets_restricted

/-! ## Final deterministic natural/mean replay oracles -/

noncomputable def middleAutoOracle (terms logFuel : ℕ) :
    AutoOracle middleTargets where
  natural := LRIdealNaturalOracle.middleNaturalOracle terms
  mean := middleMeanOracle terms
  naturalPayload := LRIdealNaturalOracle.autoPayload logFuel
  meanPayload := CenteredPayload.auto logFuel

noncomputable def upperAutoOracle (terms logFuel : ℕ) :
    AutoOracle upperTargets where
  natural := LRIdealNaturalOracle.upperNaturalOracle terms
  mean := upperMeanOracle terms
  naturalPayload := LRIdealNaturalOracle.autoPayload logFuel
  meanPayload := CenteredPayload.auto logFuel

noncomputable def restrictedAutoOracle (terms logFuel : ℕ) :
    AutoOracle restrictedTargets where
  natural := LRIdealNaturalOracle.restrictedNaturalOracle terms
  mean := restrictedMeanOracle terms
  naturalPayload := LRIdealNaturalOracle.autoPayload logFuel
  meanPayload := CenteredPayload.auto logFuel

end LRIdealCenteredMeanOracle
end CourtadeKumar
