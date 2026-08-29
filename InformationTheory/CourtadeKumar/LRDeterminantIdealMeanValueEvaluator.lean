import InformationTheory.CourtadeKumar.IntervalADElementary
import InformationTheory.CourtadeKumar.IntervalDerivativeCertificate
import InformationTheory.CourtadeKumar.LRDeterminantIdealIntervalEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantLowKAnalytic
import InformationTheory.CourtadeKumar.LRDeterminantLowKThin
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreAssembly

/-!
# Mean-value interface for the low-`k` ideal replay

This scratch module starts the kernel-side reconstruction of
`verify_lr_direct_small_s_k1_ideal_core.py`.  It has three deliberately
small responsibilities.

* It identifies the legacy low-`k` ideal formulas with the newer ideal-core
  formulas used by the verified interval evaluator.
* It records the two exact triples checked by the historical replay at
  `L₀ = 7 log 2`: the global-`L` middle triple and the endpoint/derivative
  upper triple.
* It gives natural and midpoint leaf interfaces whose executable outputs are
  rational intervals.  The midpoint interface is expressed through the
  already verified `IntervalAD` and `MidpointCertificate` infrastructure.

The concrete formula evaluator and its automatic logarithm payload are the
next layer.  No generated tree, proof-valued payload, or executable shortcut
is introduced here.
-/

namespace CourtadeKumar
namespace LRLowKIdealMeanValue

/-! ## Legacy/current formula bridge -/

/-- The two continuous conventions for the ideal entropy quotient agree
after the change of variables `z = 1 + t`. -/
theorem idealH_one_add_eq (t : ℝ) :
    lrLowKIdealH (1 + t) = lrDeterminantIdealH t := by
  simp [lrLowKIdealH, lrDeterminantIdealH]

theorem idealC_eq : lrLowKIdealC = lrDeterminantIdealC := by
  rfl

theorem idealA_eq (k chi : ℝ) :
    lrLowKIdealA k chi = lrDeterminantIdealA k chi := by
  rfl

theorem idealAH_eq (k chi : ℝ) :
    lrLowKIdealAH k chi = lrDeterminantIdealAH k chi := by
  simp only [lrLowKIdealAH, lrDeterminantIdealAH, idealH_one_add_eq]

theorem idealQChi_eq (chi : ℝ) :
    lrLowKIdealQChi chi = lrSmallSBridgeQChi chi := by
  rfl

theorem idealD_eq (k : ℝ) :
    lrLowKIdealD k = lrDeterminantIdealD0 k := by
  rfl

theorem idealBOffset_eq (k : ℝ) :
    lrLowKIdealBOffset k = lrDeterminantIdealBConst k := by
  rfl

theorem idealB_eq (L k : ℝ) :
    lrDeterminantIdealB0 L k = L / 2 + lrLowKIdealBOffset k := by
  unfold lrDeterminantIdealB0 lrLowKIdealBOffset
  ring

theorem idealP_eq (L k chi : ℝ) :
    lrDeterminantIdealP L k chi = L + lrLowKIdealP k chi := by
  unfold lrDeterminantIdealP lrLowKIdealP
  rw [idealA_eq]
  ring

theorem idealP_sub_G_eq (L k chi : ℝ) :
    lrDeterminantIdealP L k chi - lrDeterminantIdealG L k chi =
      lrLowKIdealS k chi := by
  unfold lrDeterminantIdealP lrDeterminantIdealG lrLowKIdealS
  rw [idealA_eq, idealQChi_eq]
  ring

theorem idealT_eq (L k chi : ℝ) :
    lrDeterminantIdealT L k chi = L + lrLowKIdealT k chi := by
  unfold lrDeterminantIdealT lrLowKIdealT
  rw [idealAH_eq]
  ring

/-- The legacy DA1 ideal core and the current ideal-core target are exactly
the same real function, for every logarithmic scale. -/
theorem idealCore_eq (L k chi : ℝ) :
    lrLowKIdealCore L k chi = lrDeterminantIdealCore L k chi := by
  unfold lrLowKIdealCore lrDeterminantIdealCore
  dsimp only
  rw [idealD_eq, idealP_sub_G_eq, idealP_eq, idealB_eq, idealBOffset_eq,
    idealT_eq, idealC_eq]

theorem idealS_eq (k chi : ℝ) :
    lrLowKIdealS k chi = lrDeterminantIdealS k chi := by
  unfold lrLowKIdealS lrDeterminantIdealS
  rw [idealQChi_eq, idealA_eq]

theorem idealT0_eq (k chi : ℝ) :
    lrLowKIdealT k chi = lrDeterminantIdealT0 k chi := by
  unfold lrLowKIdealT lrDeterminantIdealT0
  rw [idealAH_eq]

theorem idealLambda_eq (k chi : ℝ) :
    lrLowKIdealLambda k chi = lrDeterminantIdealLambda k chi := by
  unfold lrLowKIdealLambda lrDeterminantIdealLambda
  rw [idealD_eq, idealS_eq]

theorem idealC1_eq (k chi : ℝ) :
    lrLowKIdealC1 k chi = lrDeterminantIdealC1 k chi := by
  unfold lrLowKIdealC1 lrDeterminantIdealC1
  rw [idealT0_eq, idealC_eq, idealBOffset_eq, idealD_eq]

theorem idealDerivative_eq (L k chi : ℝ) :
    lrDeterminantIdealLDerivative L k chi =
      lrLowKIdealLambda k chi / 2 -
        lrLowKIdealC1 k chi / (L + lrLowKIdealC) ^ 2 := by
  unfold lrDeterminantIdealLDerivative
  rw [idealLambda_eq, idealC1_eq, idealC_eq]

/-! ## Exact target triples from the historical evaluator -/

/-- Three real targets which must all be strictly positive at a leaf. -/
structure TargetTriple where
  first : CertificatePoint → ℝ
  second : CertificatePoint → ℝ
  third : CertificatePoint → ℝ

def TargetTriple.PositiveAt (targets : TargetTriple)
    (point : CertificatePoint) : Prop :=
  0 < targets.first point ∧
    0 < targets.second point ∧
    0 < targets.third point

/-- On `[1/32,5/32]`, the replay removes the whole positive reciprocal
tail at `L₀`.  The second target is the separated linear slope
`Lambda/2`, not the endpoint derivative. -/
noncomputable def middleTargets : TargetTriple where
  first := fun point ↦
    (lrDeterminantIdealCore lrLowKIdealL0 point.k point.chi -
      lrDeterminantIdealC1 point.k point.chi /
        (lrLowKIdealL0 + lrDeterminantIdealC)) - 19 / 50
  second := fun point ↦
    lrDeterminantIdealLambda point.k point.chi / 2
  third := fun point ↦
    lrDeterminantIdealC1 point.k point.chi

/-- On `[5/32,1]`, the replay checks the endpoint value, its exact
`L` derivative, and `C₁`. -/
noncomputable def upperTargets : TargetTriple where
  first := fun point ↦
    lrDeterminantIdealCore lrLowKIdealL0 point.k point.chi - 19 / 50
  second := fun point ↦
    lrDeterminantIdealLDerivative lrLowKIdealL0 point.k point.chi
  third := fun point ↦
    lrDeterminantIdealC1 point.k point.chi

/-- The same correlated evaluator also serves the restricted deep ideal
replay at `L₀ = 14 log 2`. -/
noncomputable def restrictedTargets : TargetTriple where
  first := fun point ↦
    lrDeterminantIdealCore lrDeterminantIdealDeepL0 point.k point.chi - 3 / 5
  second := fun point ↦
    lrDeterminantIdealLDerivative lrDeterminantIdealDeepL0 point.k point.chi
  third := fun point ↦
    lrDeterminantIdealC1 point.k point.chi

theorem middleFirst_eq_legacy (point : CertificatePoint) :
    middleTargets.first point =
      (lrLowKIdealCore lrLowKIdealL0 point.k point.chi -
        lrLowKIdealC1 point.k point.chi /
          (lrLowKIdealL0 + lrLowKIdealC)) - 19 / 50 := by
  simp only [middleTargets]
  rw [idealCore_eq, idealC1_eq, idealC_eq]

theorem middleSecond_eq_legacy (point : CertificatePoint) :
    middleTargets.second point =
      lrLowKIdealLambda point.k point.chi / 2 := by
  simp only [middleTargets]
  rw [idealLambda_eq]

theorem middleThird_eq_legacy (point : CertificatePoint) :
    middleTargets.third point = lrLowKIdealC1 point.k point.chi := by
  simp only [middleTargets]
  rw [idealC1_eq]

theorem upperFirst_eq_legacy (point : CertificatePoint) :
    upperTargets.first point =
      lrLowKIdealCore lrLowKIdealL0 point.k point.chi - 19 / 50 := by
  simp only [upperTargets]
  rw [idealCore_eq]

theorem upperSecond_eq_legacy (point : CertificatePoint) :
    upperTargets.second point =
      lrLowKIdealLambda point.k point.chi / 2 -
        lrLowKIdealC1 point.k point.chi /
          (lrLowKIdealL0 + lrLowKIdealC) ^ 2 := by
  simp only [upperTargets]
  exact idealDerivative_eq lrLowKIdealL0 point.k point.chi

theorem upperThird_eq_legacy (point : CertificatePoint) :
    upperTargets.third point = lrLowKIdealC1 point.k point.chi := by
  simp only [upperTargets]
  rw [idealC1_eq]

/-- Exact equivalence with the `middle` field of
`LRLowKIdealReplayCertificate`. -/
theorem middle_positive_iff_legacy (point : CertificatePoint) :
    middleTargets.PositiveAt point ↔
      19 / 50 <
          lrLowKIdealCore lrLowKIdealL0 point.k point.chi -
            lrLowKIdealC1 point.k point.chi /
              (lrLowKIdealL0 + lrLowKIdealC) ∧
        0 < lrLowKIdealLambda point.k point.chi / 2 ∧
        0 < lrLowKIdealC1 point.k point.chi := by
  rw [TargetTriple.PositiveAt, middleFirst_eq_legacy,
    middleSecond_eq_legacy, middleThird_eq_legacy]
  simp only [sub_pos]

/-- Exact equivalence with the `upper` field of
`LRLowKIdealReplayCertificate`. -/
theorem upper_positive_iff_legacy (point : CertificatePoint) :
    upperTargets.PositiveAt point ↔
      19 / 50 < lrLowKIdealCore lrLowKIdealL0 point.k point.chi ∧
        0 < lrLowKIdealLambda point.k point.chi / 2 -
          lrLowKIdealC1 point.k point.chi /
            (lrLowKIdealL0 + lrLowKIdealC) ^ 2 ∧
        0 < lrLowKIdealC1 point.k point.chi := by
  rw [TargetTriple.PositiveAt, upperFirst_eq_legacy,
    upperSecond_eq_legacy, upperThird_eq_legacy]
  simp only [sub_pos]

theorem restricted_positive_endpointProperties
    {point : CertificatePoint}
    (hpositive : restrictedTargets.PositiveAt point) :
    LRDeterminantIdealEndpointProperties lrDeterminantIdealDeepL0
      (3 / 5) point := by
  rcases hpositive with ⟨hcore, hderivative, hc1⟩
  have hc1Pos : 0 < lrDeterminantIdealC1 point.k point.chi := by
    simpa [restrictedTargets] using hc1
  exact ⟨by simpa [restrictedTargets, sub_pos] using hcore,
    by simpa [restrictedTargets] using hderivative, hc1Pos.le⟩

/-! ## Exact-rational natural leaves -/

/-- Rational enclosures of all three targets. -/
structure IntervalTriple where
  first : RationalEnclosure
  second : RationalEnclosure
  third : RationalEnclosure

namespace IntervalTriple

def check (result : IntervalTriple) : Bool :=
  decide ((0 : ℚ) < result.first.lower ∧
    (0 : ℚ) < result.second.lower ∧
    (0 : ℚ) < result.third.lower)

theorem positiveAt_of_check
    {targets : TargetTriple} {point : CertificatePoint}
    {result : IntervalTriple}
    (hcheck : result.check = true)
    (hfirst : result.first.Contains (targets.first point))
    (hsecond : result.second.Contains (targets.second point))
    (hthird : result.third.Contains (targets.third point)) :
    targets.PositiveAt point := by
  have hparts : (0 : ℚ) < result.first.lower ∧
      (0 : ℚ) < result.second.lower ∧
      (0 : ℚ) < result.third.lower := by
    simpa [check] using hcheck
  constructor
  · have hrat : (0 : ℝ) < (result.first.lower : ℝ) := by
      exact_mod_cast hparts.1
    exact hrat.trans_le hfirst.1
  constructor
  · have hrat : (0 : ℝ) < (result.second.lower : ℝ) := by
      exact_mod_cast hparts.2.1
    exact hrat.trans_le hsecond.1
  · have hrat : (0 : ℝ) < (result.third.lower : ℝ) := by
      exact_mod_cast hparts.2.2
    exact hrat.trans_le hthird.1

end IntervalTriple

/-- The value projections of a simultaneous verified-AD evaluation. -/
structure ADTriple where
  first : IntervalAD
  second : IntervalAD
  third : IntervalAD

def ADTriple.values (result : ADTriple) : IntervalTriple where
  first := result.first.value
  second := result.second.value
  third := result.third.value

/-- Abstract contract for the direct whole-box evaluator.  A concrete
implementation will reconstruct its payload deterministically and prove
this contract using `IntervalAD.contains_*` and the checked log nodes. -/
structure NaturalOracle (targets : TargetTriple) where
  Payload : Type
  payloadCheck : CertificateBox → Payload → Bool
  evaluate : CertificateBox → Payload → IntervalTriple
  sound : ∀ box payload, payloadCheck box payload = true →
    ∀ point, box.Contains point →
      (evaluate box payload).first.Contains (targets.first point) ∧
      (evaluate box payload).second.Contains (targets.second point) ∧
      (evaluate box payload).third.Contains (targets.third point)

def naturalAccepts {targets : TargetTriple}
    (oracle : NaturalOracle targets) (box : CertificateBox)
    (payload : oracle.Payload) : Bool :=
  oracle.payloadCheck box payload && (oracle.evaluate box payload).check

theorem positiveAt_of_naturalAccepts
    {targets : TargetTriple} (oracle : NaturalOracle targets)
    {box : CertificateBox} {payload : oracle.Payload}
    (haccept : naturalAccepts oracle box payload = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    targets.PositiveAt point := by
  have hparts : oracle.payloadCheck box payload = true ∧
      (oracle.evaluate box payload).check = true := by
    simpa [naturalAccepts] using haccept
  rcases oracle.sound box payload hparts.1 point hpoint with
    ⟨hfirst, hsecond, hthird⟩
  exact IntervalTriple.positiveAt_of_check hparts.2
    hfirst hsecond hthird

/-! ## Verified midpoint leaves -/

/-- A midpoint certificate for each of the three simultaneous targets. -/
structure MidpointTriple where
  first : MidpointCertificate
  second : MidpointCertificate
  third : MidpointCertificate

/-- Combine value intervals computed at the exact box midpoint with
derivative intervals computed on the whole box.  This is precisely the
mean-value construction used by the historical Python replay. -/
def MidpointTriple.ofAD (center full : ADTriple) : MidpointTriple where
  first :=
    { value := center.first.value
      derivS := full.first.derivS
      derivK := full.first.derivK
      derivChi := full.first.derivChi }
  second :=
    { value := center.second.value
      derivS := full.second.derivS
      derivK := full.second.derivK
      derivChi := full.second.derivChi }
  third :=
    { value := center.third.value
      derivS := full.third.derivS
      derivK := full.third.derivK
      derivChi := full.third.derivChi }

def MidpointTriple.check (box : CertificateBox)
    (result : MidpointTriple) : Bool :=
  result.first.check box &&
    (result.second.check box && result.third.check box)

/-- Abstract contract for a correlated midpoint evaluator.  The six
semantic clauses are exactly what `MidpointCertificate.sound` consumes;
the concrete evaluator will discharge them from verified interval AD. -/
structure MeanOracle (targets : TargetTriple) where
  Payload : Type
  payloadCheck : CertificateBox → Payload → Bool
  evaluate : CertificateBox → Payload → MidpointTriple
  firstValue_sound : ∀ box payload, payloadCheck box payload = true →
    (evaluate box payload).first.value.Contains
      (targets.first box.midpoint)
  firstDerivatives : ∀ box payload, payloadCheck box payload = true →
    BoxDerivativeEnclosures targets.first box
      (evaluate box payload).first
  secondValue_sound : ∀ box payload, payloadCheck box payload = true →
    (evaluate box payload).second.value.Contains
      (targets.second box.midpoint)
  secondDerivatives : ∀ box payload, payloadCheck box payload = true →
    BoxDerivativeEnclosures targets.second box
      (evaluate box payload).second
  thirdValue_sound : ∀ box payload, payloadCheck box payload = true →
    (evaluate box payload).third.value.Contains
      (targets.third box.midpoint)
  thirdDerivatives : ∀ box payload, payloadCheck box payload = true →
    BoxDerivativeEnclosures targets.third box
      (evaluate box payload).third

def meanAccepts {targets : TargetTriple}
    (oracle : MeanOracle targets) (box : CertificateBox)
    (payload : oracle.Payload) : Bool :=
  oracle.payloadCheck box payload &&
    (oracle.evaluate box payload).check box

theorem positiveAt_of_meanAccepts
    {targets : TargetTriple} (oracle : MeanOracle targets)
    {box : CertificateBox} {payload : oracle.Payload}
    (haccept : meanAccepts oracle box payload = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    targets.PositiveAt point := by
  have hparts : oracle.payloadCheck box payload = true ∧
      (oracle.evaluate box payload).check box = true := by
    simpa [meanAccepts] using haccept
  have hchecks :
      (oracle.evaluate box payload).first.check box = true ∧
      (oracle.evaluate box payload).second.check box = true ∧
      (oracle.evaluate box payload).third.check box = true := by
    simpa [MidpointTriple.check, Bool.and_eq_true] using hparts.2
  have hfirstValue := oracle.firstValue_sound box payload hparts.1
  have hfirstDeriv := oracle.firstDerivatives box payload hparts.1
  have hsecondValue := oracle.secondValue_sound box payload hparts.1
  have hsecondDeriv := oracle.secondDerivatives box payload hparts.1
  have hthirdValue := oracle.thirdValue_sound box payload hparts.1
  have hthirdDeriv := oracle.thirdDerivatives box payload hparts.1
  constructor
  · exact MidpointCertificate.sound_of_derivativeEnclosures
      hfirstValue hfirstDeriv hchecks.1 hpoint
  constructor
  · exact MidpointCertificate.sound_of_derivativeEnclosures
      hsecondValue hsecondDeriv hchecks.2.1 hpoint
  · exact MidpointCertificate.sound_of_derivativeEnclosures
      hthirdValue hthirdDeriv hchecks.2.2 hpoint

/-! These aliases keep the two replay modes distinct at the type level. -/

abbrev MiddleNaturalOracle := NaturalOracle middleTargets
abbrev MiddleMeanOracle := MeanOracle middleTargets
abbrev UpperNaturalOracle := NaturalOracle upperTargets
abbrev UpperMeanOracle := MeanOracle upperTargets
abbrev RestrictedNaturalOracle := NaturalOracle restrictedTargets
abbrev RestrictedMeanOracle := MeanOracle restrictedTargets

/-! ## Compact natural/mean trees -/

/-- A concrete replay oracle consists of the two verified semantic rules and
deterministic payload constructors.  The payload constructors are untrusted:
their Boolean checks are rerun at every leaf. -/
structure AutoOracle (targets : TargetTriple) where
  natural : NaturalOracle targets
  mean : MeanOracle targets
  naturalPayload : (box : CertificateBox) → natural.Payload
  meanPayload : (box : CertificateBox) → mean.Payload

inductive AcceptTag where
  | natural
  | mean
  deriving DecidableEq, Repr

def acceptCheck {targets : TargetTriple}
    (oracle : AutoOracle targets) (box : CertificateBox) :
    AcceptTag → Bool
  | .natural =>
      naturalAccepts oracle.natural box (oracle.naturalPayload box)
  | .mean =>
      meanAccepts oracle.mean box (oracle.meanPayload box)

theorem positiveAt_of_acceptCheck
    {targets : TargetTriple} (oracle : AutoOracle targets)
    {box : CertificateBox} {tag : AcceptTag}
    (hcheck : acceptCheck oracle box tag = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    targets.PositiveAt point := by
  cases tag with
  | natural =>
      exact positiveAt_of_naturalAccepts oracle.natural
        (by simpa [acceptCheck] using hcheck) hpoint
  | mean =>
      exact positiveAt_of_meanAccepts oracle.mean
        (by simpa [acceptCheck] using hcheck) hpoint

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

/-- Compact preorder topology.  An accepted leaf stores only which of the
two independently verified rules should be recomputed on its current box. -/
inductive Tree where
  | accept (tag : AcceptTag)
  | split (axis : CertificateAxis) (lower upper : Tree)
  deriving Repr

namespace Tree

def check {targets : TargetTriple} (oracle : AutoOracle targets) :
    Tree → CertificateBox → Bool
  | .accept tag, box => acceptCheck oracle box tag
  | .split axis lower upper, box =>
      let cut := axisCut box axis
      check oracle lower (box.lower axis cut) &&
        check oracle upper (box.upper axis cut)

def nodeCount : Tree → ℕ
  | .accept _ => 1
  | .split _ lower upper => 1 + nodeCount lower + nodeCount upper

def leafCount : Tree → ℕ
  | .accept _ => 1
  | .split _ lower upper => leafCount lower + leafCount upper

def naturalLeafCount : Tree → ℕ
  | .accept .natural => 1
  | .accept .mean => 0
  | .split _ lower upper =>
      naturalLeafCount lower + naturalLeafCount upper

def meanLeafCount : Tree → ℕ
  | .accept .natural => 0
  | .accept .mean => 1
  | .split _ lower upper => meanLeafCount lower + meanLeafCount upper

def maxDepth : Tree → ℕ
  | .accept _ => 0
  | .split _ lower upper => 1 + max (maxDepth lower) (maxDepth upper)

def axisToken : CertificateAxis → Char
  | .s => 's'
  | .k => 'k'
  | .chi => 'h'

def tokens : Tree → List Char
  | .accept .natural => ['N']
  | .accept .mean => ['M']
  | .split axis lower upper =>
      axisToken axis :: (tokens lower ++ tokens upper)

def packed (tree : Tree) : String := String.ofList tree.tokens

end Tree

theorem positiveAt_of_treeCheck
    {targets : TargetTriple} (oracle : AutoOracle targets)
    {box : CertificateBox} {tree : Tree}
    (hcheck : tree.check oracle box = true) :
    ∀ point, box.Contains point → targets.PositiveAt point := by
  induction tree generalizing box with
  | accept tag =>
      intro point hpoint
      exact positiveAt_of_acceptCheck oracle
        (by simpa [Tree.check] using hcheck) hpoint
  | split axis lower upper lower_ih upper_ih =>
      have hparts :
          lower.check oracle (box.lower axis (axisCut box axis)) = true ∧
            upper.check oracle (box.upper axis (axisCut box axis)) = true := by
        simpa [Tree.check, Bool.and_eq_true] using hcheck
      intro point hpoint
      rcases box.contains_lower_or_upper hpoint axis (axisCut box axis) with
        hlower | hupper
      · exact lower_ih hparts.1 point hlower
      · exact upper_ih hparts.2 point hupper

structure CheckedTree {targets : TargetTriple}
    (oracle : AutoOracle targets) (root : CertificateBox) where
  certificate : Tree
  checked : certificate.check oracle root = true

/-! ## Exact low-`k` assembly -/

def middleRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 1 / 32, kHi := 5 / 32
    chiLo := 0, chiHi := 1 }

def upperRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 5 / 32, kHi := 1
    chiLo := 0, chiHi := 1 }

def restrictedRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 1, kHi := 4
    chiLo := 0, chiHi := 1 }

/-- The two exact historical restricted roots.  They are kept separate
because their outer join is at `k = 2`, whereas the arithmetic midpoint of
`[1,4]` is `5/2`. -/
def restrictedLowerRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 1, kHi := 2
    chiLo := 0, chiHi := 1 }

def restrictedUpperRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 2, kHi := 4
    chiLo := 0, chiHi := 1 }

/-- Two checked compact trees discharge exactly the two compact fields left
after the analytic thin-`k` theorem. -/
def lowKIdealReplayCertificate_of_checkedTrees
    (middleOracle : AutoOracle middleTargets)
    (upperOracle : AutoOracle upperTargets)
    (middleTree : CheckedTree middleOracle middleRoot)
    (upperTree : CheckedTree upperOracle upperRoot) :
    LRLowKIdealReplayCertificate := by
  apply lrLowKIdealReplayCertificate_of_middle_upper
  · intro k chi hk hchi
    let point : CertificatePoint := { s := 0, k := k, chi := chi }
    have hpoint : middleRoot.Contains point := by
      rcases hk with ⟨hkLower, hkUpper⟩
      rcases hchi with ⟨hchiLower, hchiUpper⟩
      simpa [middleRoot, point, CertificateBox.Contains] using
        (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
            1 / 32 ≤ k ∧ k ≤ 5 / 32 ∧
            0 ≤ chi ∧ chi ≤ 1 from
          ⟨by norm_num, by norm_num, hkLower, hkUpper,
            hchiLower, hchiUpper⟩)
    have hpositive := positiveAt_of_treeCheck middleOracle
      middleTree.checked point hpoint
    simpa [point] using (middle_positive_iff_legacy point).mp hpositive
  · intro k chi hk hchi
    let point : CertificatePoint := { s := 0, k := k, chi := chi }
    have hpoint : upperRoot.Contains point := by
      rcases hk with ⟨hkLower, hkUpper⟩
      rcases hchi with ⟨hchiLower, hchiUpper⟩
      simpa [upperRoot, point, CertificateBox.Contains] using
        (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
            5 / 32 ≤ k ∧ k ≤ 1 ∧
            0 ≤ chi ∧ chi ≤ 1 from
          ⟨by norm_num, by norm_num, hkLower, hkUpper,
            hchiLower, hchiUpper⟩)
    have hpositive := positiveAt_of_treeCheck upperOracle
      upperTree.checked point hpoint
    simpa [point] using (upper_positive_iff_legacy point).mp hpositive

/-- The same tree interface closes the second ideal replay needed by the
restricted determinant assembly, now on `1 ≤ k ≤ 4` at `14 log 2`. -/
def idealOneToFour_of_checkedTree
    (oracle : AutoOracle restrictedTargets)
    (tree : CheckedTree oracle restrictedRoot) :
    LRDeterminantIdealOneToFourTheorem := by
  intro L hL k chi hk hchi
  let point : CertificatePoint := { s := 0, k := k, chi := chi }
  have hpoint : restrictedRoot.Contains point := by
    rcases hk with ⟨hkLower, hkUpper⟩
    rcases hchi with ⟨hchiLower, hchiUpper⟩
    simpa [restrictedRoot, point, CertificateBox.Contains] using
      (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
          1 ≤ k ∧ k ≤ 4 ∧ 0 ≤ chi ∧ chi ≤ 1 from
        ⟨by norm_num, by norm_num, hkLower, hkUpper,
          hchiLower, hchiUpper⟩)
  have hpositive := positiveAt_of_treeCheck oracle
    tree.checked point hpoint
  have hendpoint := restricted_positive_endpointProperties hpositive
  simpa [point] using lrDeterminantIdealCore_gt_of_endpointProperties
    lrDeterminantIdealDeepL0_add_C_pos hL hendpoint

/-- Exact adapter for the historical restricted forest.  The split at
`k = 2` is represented by two separately rooted checked trees, so it is not
confused with the generic arithmetic-midpoint `k` token. -/
def idealOneToFour_of_twoCheckedTrees
    (oracle : AutoOracle restrictedTargets)
    (lowerTree : CheckedTree oracle restrictedLowerRoot)
    (upperTree : CheckedTree oracle restrictedUpperRoot) :
    LRDeterminantIdealOneToFourTheorem := by
  intro L hL k chi hk hchi
  let point : CertificatePoint := { s := 0, k := k, chi := chi }
  have finish
      (hpositive : restrictedTargets.PositiveAt point) :
      (3 / 5 : ℝ) < lrDeterminantIdealCore L k chi := by
    have hendpoint := restricted_positive_endpointProperties hpositive
    simpa [point] using lrDeterminantIdealCore_gt_of_endpointProperties
      lrDeterminantIdealDeepL0_add_C_pos hL hendpoint
  by_cases hkTwo : k ≤ 2
  · have hpoint : restrictedLowerRoot.Contains point := by
      rcases hk with ⟨hkLower, _hkUpper⟩
      rcases hchi with ⟨hchiLower, hchiUpper⟩
      simpa [restrictedLowerRoot, point, CertificateBox.Contains] using
        (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
            1 ≤ k ∧ k ≤ 2 ∧ 0 ≤ chi ∧ chi ≤ 1 from
          ⟨by norm_num, by norm_num, hkLower, hkTwo,
            hchiLower, hchiUpper⟩)
    exact finish (positiveAt_of_treeCheck oracle
      lowerTree.checked point hpoint)
  · have hkTwoLower : 2 ≤ k := le_of_lt (lt_of_not_ge hkTwo)
    have hpoint : restrictedUpperRoot.Contains point := by
      rcases hk with ⟨_hkLower, hkUpper⟩
      rcases hchi with ⟨hchiLower, hchiUpper⟩
      simpa [restrictedUpperRoot, point, CertificateBox.Contains] using
        (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
            2 ≤ k ∧ k ≤ 4 ∧ 0 ≤ chi ∧ chi ≤ 1 from
          ⟨by norm_num, by norm_num, hkTwoLower, hkUpper,
            hchiLower, hchiUpper⟩)
    exact finish (positiveAt_of_treeCheck oracle
      upperTree.checked point hpoint)

end LRLowKIdealMeanValue
end CourtadeKumar
