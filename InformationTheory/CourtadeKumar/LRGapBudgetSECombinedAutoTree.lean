import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedTail

/-!
# Automatic finite tree for the bounded gap-budget derivative

The generator is untrusted convenience code.  Every returned leaf is
rechecked by one of the three verified evaluators or by a one-sided physical
discard, and `buildTree_check_of_eq` proves structurally that a successful
return value passes the aggregate Boolean checker.
-/

namespace CourtadeKumar
namespace LRGapBudgetSECombinedAutoTree

abbrev Tree := LRGapBudgetSEDerivativeTree

def autoAccept (terms sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    Option LRGapBudgetSEDerivativeAcceptData :=
  if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .regular then
    some .regular
  else if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .endpoint then
    some .endpoint
  else if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .endpointRetainedQ then
    some .endpointRetainedQ
  else none

theorem autoAccept_check_of_eq
    (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (data : LRGapBudgetSEDerivativeAcceptData)
    (haccept : autoAccept terms sqrtFuel logFuel box = some data) :
    data.check terms sqrtFuel logFuel box = true := by
  by_cases hregular :
      LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
        .regular = true
  · simp [autoAccept, hregular] at haccept
    cases haccept
    exact hregular
  have hregularFalse := Bool.eq_false_of_not_eq_true hregular
  by_cases hendpoint :
      LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
        .endpoint = true
  · simp [autoAccept, hregularFalse, hendpoint] at haccept
    cases haccept
    exact hendpoint
  have hendpointFalse := Bool.eq_false_of_not_eq_true hendpoint
  by_cases hretained :
      LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
        .endpointRetainedQ = true
  · simp [autoAccept, hregularFalse, hendpointFalse, hretained] at haccept
    cases haccept
    exact hretained
  · have hretainedFalse := Bool.eq_false_of_not_eq_true hretained
    simp [autoAccept, hregularFalse, hendpointFalse, hretainedFalse] at haccept

def autoDiscard (box : CertificateBox) :
    Option LRGapBudgetSEDiscardData :=
  if lrGapBudgetSEDiscardCheck box .eBelowFourS then
    some .eBelowFourS
  else if lrGapBudgetSEDiscardCheck box .eAtLeastOne then
    some .eAtLeastOne
  else if lrGapBudgetSEDiscardCheck box .xBelowHighShape then
    some .xBelowHighShape
  else if lrGapBudgetSEDiscardCheck box .vBelowThird then
    some .vBelowThird
  else none

theorem autoDiscard_check_of_eq (box : CertificateBox)
    (data : LRGapBudgetSEDiscardData)
    (hdiscard : autoDiscard box = some data) :
    lrGapBudgetSEDiscardCheck box data = true := by
  by_cases hfour : lrGapBudgetSEDiscardCheck box .eBelowFourS = true
  · simp [autoDiscard, hfour] at hdiscard
    cases hdiscard
    exact hfour
  have hfourFalse := Bool.eq_false_of_not_eq_true hfour
  by_cases hone : lrGapBudgetSEDiscardCheck box .eAtLeastOne = true
  · simp [autoDiscard, hfourFalse, hone] at hdiscard
    cases hdiscard
    exact hone
  have honeFalse := Bool.eq_false_of_not_eq_true hone
  by_cases hx : lrGapBudgetSEDiscardCheck box .xBelowHighShape = true
  · simp [autoDiscard, hfourFalse, honeFalse, hx] at hdiscard
    cases hdiscard
    exact hx
  have hxFalse := Bool.eq_false_of_not_eq_true hx
  by_cases hv : lrGapBudgetSEDiscardCheck box .vBelowThird = true
  · simp [autoDiscard, hfourFalse, honeFalse, hxFalse, hv] at hdiscard
    cases hdiscard
    exact hv
  · have hvFalse := Bool.eq_false_of_not_eq_true hv
    simp [autoDiscard, hfourFalse, honeFalse, hxFalse, hvFalse] at hdiscard

/-- Normalized widths put the short `s` coordinate on the same scale as
`e` and `chi`.  A failed box touching `s=0` is first peeled by decimal cuts,
so only one rapidly shrinking child continues to touch the endpoint. -/
def chooseAxis (box : CertificateBox) : CertificateAxis :=
  let sWidth := 10 * (box.sHi - box.sLo)
  let eWidth := box.kHi - box.kLo
  let chiWidth := box.chiHi - box.chiLo
  if box.sLo = 0 ∧ 1 / 100000 < box.sHi then .s
  else if sWidth ≥ eWidth ∧ sWidth ≥ chiWidth ∧
      box.sLo < box.sHi then .s
  else if eWidth ≥ chiWidth ∧ box.kLo < box.kHi then .k
  else .chi

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s =>
      if box.sLo = 0 ∧ 1 / 100000 < box.sHi then
        box.sLo + (box.sHi - box.sLo) / 10
      else RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

def buildTree (terms sqrtFuel logFuel : ℕ) :
    ℕ → CertificateBox → Option Tree
  | 0, box =>
      match autoAccept terms sqrtFuel logFuel box with
      | some data => some (.accept data)
      | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none => none
  | fuel + 1, box =>
      match autoAccept terms sqrtFuel logFuel box with
      | some data => some (.accept data)
      | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              match buildTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) with
              | none => none
              | some lower =>
                  match buildTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) with
                  | none => none
                  | some upper => some (.split axis cut lower upper)

def treeNodes : Tree → ℕ
  | .accept _ => 1
  | .discard _ => 1
  | .split _ _ lower upper => 1 + treeNodes lower + treeNodes upper

theorem buildTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox)
    (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check
      (LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck box = true := by
  induction fuel generalizing box tree with
  | zero =>
      change (match autoAccept terms sqrtFuel logFuel box with
        | some data => some (.accept data)
        | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none => none) = some tree at hbuild
      generalize haccept : autoAccept terms sqrtFuel logFuel box = acceptOption
      cases acceptOption with
      | some data =>
          simp only [haccept, Option.some.injEq] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            autoAccept_check_of_eq terms sqrtFuel logFuel box data haccept
      | none =>
          generalize hdiscard : autoDiscard box = discardOption
          cases discardOption with
          | none =>
              simp only [haccept, hdiscard] at hbuild
              contradiction
          | some data =>
              simp only [haccept, hdiscard, Option.some.injEq] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                autoDiscard_check_of_eq box data hdiscard
  | succ fuel ih =>
      change (match autoAccept terms sqrtFuel logFuel box with
        | some data => some (.accept data)
        | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              match buildTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) with
              | none => none
              | some lower =>
                  match buildTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) with
                  | none => none
                  | some upper => some (.split axis cut lower upper)) =
        some tree at hbuild
      generalize haccept : autoAccept terms sqrtFuel logFuel box = acceptOption
      cases acceptOption with
      | some data =>
          simp only [haccept, Option.some.injEq] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            autoAccept_check_of_eq terms sqrtFuel logFuel box data haccept
      | none =>
          generalize hdiscard : autoDiscard box = discardOption
          cases discardOption with
          | some data =>
              simp only [haccept, hdiscard, Option.some.injEq] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                autoDiscard_check_of_eq box data hdiscard
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              generalize hlower : buildTree terms sqrtFuel logFuel fuel
                (box.lower axis cut) = lowerOption
              cases lowerOption with
              | none =>
                  simp only [haccept, hdiscard, axis, cut, hlower] at hbuild
                  contradiction
              | some lower =>
                  generalize hupper : buildTree terms sqrtFuel logFuel fuel
                    (box.upper axis cut) = upperOption
                  cases upperOption with
                  | none =>
                      simp only [haccept, hdiscard, axis, cut, hlower,
                        hupper] at hbuild
                      contradiction
                  | some upper =>
                      simp only [haccept, hdiscard, axis, cut, hlower,
                        hupper, Option.some.injEq] at hbuild
                      subst tree
                      simp only [SubdivisionCertificate.check,
                        Bool.and_eq_true]
                      exact ⟨ih _ _ hlower, ih _ _ hupper⟩

/-! The closed-endpoint generator deliberately omits the regular evaluator.
This gives a uniform tree whose leaves remain valid on boxes touching
`s = 0`, and makes exact replay by generator equality especially compact. -/

def endpointAutoAccept (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) :
    Option LRGapBudgetSEDerivativeAcceptData :=
  if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .endpoint then
    some .endpoint
  else if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .endpointRetainedQ then
    some .endpointRetainedQ
  else none

theorem endpointAutoAccept_check_of_eq
    (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (data : LRGapBudgetSEDerivativeAcceptData)
    (haccept : endpointAutoAccept terms sqrtFuel logFuel box = some data) :
    data.check terms sqrtFuel logFuel box = true := by
  by_cases hendpoint :
      LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
        .endpoint = true
  · simp [endpointAutoAccept, hendpoint] at haccept
    cases haccept
    exact hendpoint
  have hendpointFalse := Bool.eq_false_of_not_eq_true hendpoint
  by_cases hretained :
      LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
        .endpointRetainedQ = true
  · simp [endpointAutoAccept, hendpointFalse, hretained] at haccept
    cases haccept
    exact hretained
  · have hretainedFalse := Bool.eq_false_of_not_eq_true hretained
    simp [endpointAutoAccept, hendpointFalse, hretainedFalse] at haccept

def buildEndpointTree (terms sqrtFuel logFuel : ℕ) :
    ℕ → CertificateBox → Option Tree
  | 0, box =>
      match endpointAutoAccept terms sqrtFuel logFuel box with
      | some data => some (.accept data)
      | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none => none
  | fuel + 1, box =>
      match endpointAutoAccept terms sqrtFuel logFuel box with
      | some data => some (.accept data)
      | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              match buildEndpointTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) with
              | none => none
              | some lower =>
                  match buildEndpointTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) with
                  | none => none
                  | some upper => some (.split axis cut lower upper)

theorem buildEndpointTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox)
    (tree : Tree)
    (hbuild : buildEndpointTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check
      (LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck box = true := by
  induction fuel generalizing box tree with
  | zero =>
      change (match endpointAutoAccept terms sqrtFuel logFuel box with
        | some data => some (.accept data)
        | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none => none) = some tree at hbuild
      generalize haccept : endpointAutoAccept terms sqrtFuel logFuel box =
        acceptOption
      cases acceptOption with
      | some data =>
          simp only [haccept, Option.some.injEq] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            endpointAutoAccept_check_of_eq terms sqrtFuel logFuel box data
              haccept
      | none =>
          generalize hdiscard : autoDiscard box = discardOption
          cases discardOption with
          | none =>
              simp only [haccept, hdiscard] at hbuild
              contradiction
          | some data =>
              simp only [haccept, hdiscard, Option.some.injEq] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                autoDiscard_check_of_eq box data hdiscard
  | succ fuel ih =>
      change (match endpointAutoAccept terms sqrtFuel logFuel box with
        | some data => some (.accept data)
        | none =>
          match autoDiscard box with
          | some data => some (.discard data)
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              match buildEndpointTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) with
              | none => none
              | some lower =>
                  match buildEndpointTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) with
                  | none => none
                  | some upper => some (.split axis cut lower upper)) =
        some tree at hbuild
      generalize haccept : endpointAutoAccept terms sqrtFuel logFuel box =
        acceptOption
      cases acceptOption with
      | some data =>
          simp only [haccept, Option.some.injEq] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            endpointAutoAccept_check_of_eq terms sqrtFuel logFuel box data
              haccept
      | none =>
          generalize hdiscard : autoDiscard box = discardOption
          cases discardOption with
          | some data =>
              simp only [haccept, hdiscard, Option.some.injEq] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                autoDiscard_check_of_eq box data hdiscard
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              generalize hlower : buildEndpointTree terms sqrtFuel logFuel fuel
                (box.lower axis cut) = lowerOption
              cases lowerOption with
              | none =>
                  simp only [haccept, hdiscard, axis, cut, hlower] at hbuild
                  contradiction
              | some lower =>
                  generalize hupper :
                    buildEndpointTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) = upperOption
                  cases upperOption with
                  | none =>
                      simp only [haccept, hdiscard, axis, cut, hlower,
                        hupper] at hbuild
                      contradiction
                  | some upper =>
                      simp only [haccept, hdiscard, axis, cut, hlower,
                        hupper, Option.some.injEq] at hbuild
                      subst tree
                      simp only [SubdivisionCertificate.check,
                        Bool.and_eq_true]
                      exact ⟨ih _ _ hlower, ih _ _ hupper⟩

theorem derivative_nonnegative_of_buildTree_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox)
    (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  exact lrGapBudgetSECombinedDerivativeSubdivision_sound
    terms sqrtFuel logFuel
    (buildTree_check_of_eq terms sqrtFuel logFuel fuel box tree hbuild)

end LRGapBudgetSECombinedAutoTree
end CourtadeKumar
