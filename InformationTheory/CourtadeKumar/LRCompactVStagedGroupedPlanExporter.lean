import InformationTheory.CourtadeKumar.LRCompactVStagedGroupedGeneratedCertificate

/-!
# Streaming plan exporter for staged compact-`V` certificates

This module is generation infrastructure, not part of the trusted proof.
It mirrors the staged generator while streaming a tab-separated plan instead
of materializing a subdivision tree.  Every emitted arithmetic terminal is
later replayed by an ordinary kernel checker in its own Lean module.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVStagedGroupedPlanExporter

private def renderLine (fields : List String) : String :=
  String.intercalate "\t" fields

private def stdoutLine (fields : List String) : IO Unit :=
  IO.println (renderLine fields)

private def rat (q : ℚ) : String := toString q

private def axis : CertificateAxis → String
  | .s => "s"
  | .k => "k"
  | .chi => "chi"

private def head : LRCompactVLambdaGroupedHeadChoice → String
  | .n128 => "n128"
  | .n192 => "n192"

private def boxFields (box : CertificateBox) : List String :=
  [rat box.sLo, rat box.sHi, rat box.kLo, rat box.kHi,
    rat box.chiLo, rat box.chiHi]

private def logRangeFields
    (certificate : RationalEnclosure.LogRangeCertificate) : List String :=
  [toString certificate.exponent, rat certificate.mantissa]

private def logIntervalFields
    (certificate : RationalEnclosure.LogIntervalCertificate) : List String :=
  logRangeFields certificate.lower ++ logRangeFields certificate.upper

private def bFields (certificate : LRCompactVBCertificate) : List String :=
  logIntervalFields certificate.logOnePlusV ++
    logIntervalFields certificate.logOneSubRY

private def emitAccept
    (emitLine : List String → IO Unit)
    (index : ℕ) (path : String) (box : CertificateBox)
    (certificate : LRCompactVStagedGroupedLeafCertificate) : IO ℕ := do
  let mkPrefix (kind headChoice : String) :=
    ["A", toString index, path, kind, headChoice] ++ boxFields box
  match certificate with
  | .sameY data =>
      emitLine (mkPrefix "sameY" (head data.headChoice) ++
        logRangeFields data.logOnePlusVHi)
  | .grouped data =>
      emitLine (mkPrefix "independent" (head data.headChoice) ++ bFields data.b)
  | .direct data =>
      emitLine (mkPrefix "direct" "none" ++ bFields data.b)
  pure (index + 1)

private def emitDiscard
    (emitLine : List String → IO Unit)
    (index : ℕ) (path : String) (box : CertificateBox)
    (certificate : LRCompactVDiscardCertificate) : IO ℕ := do
  emitLine (["X", toString index, path, "discard", "none"] ++
    boxFields box ++ bFields certificate.b ++
    logIntervalFields certificate.logOneSubY)
  pure (index + 1)

private def emitFrontier
    (emitLine : List String → IO Unit)
    (index : ℕ) (path : String) (box : CertificateBox) : IO ℕ := do
  emitLine (["F", toString index, path, "frontier", "none"] ++ boxFields box)
  pure (index + 1)

/-- Stream the exact staged decisions in depth-first order.  Generation is
untrusted: a bad decision can only produce a failed terminal replay or a
structural plan that does not compile. -/
private def exportGeneratedWith
    (emitLine : List String → IO Unit)
    (logTerms pZeroTerms wTerms dTerms directN logFuel : ℕ) :
    ℕ → ℕ → String → CertificateBox → IO ℕ
  | 0, index, path, box => do
      let direct := LRCompactVHybridDirectDLeafCertificate.auto logFuel box
      let directOK := direct.check
        logTerms pZeroTerms wTerms dTerms directN box
      match LRCompactVStagedGroupedLeafCertificate.selectAdaptiveReplay
          logTerms wTerms dTerms directOK box direct with
      | some leaf => emitAccept emitLine index path box leaf
      | none => emitFrontier emitLine index path box
  | fuel + 1, index, path, box => do
      let discard := LRCompactVDiscardCertificate.hybridDirectDAuto logFuel box
      if discard.check logTerms box then
        emitDiscard emitLine index path box discard
      else
        let direct : LRCompactVHybridDirectDLeafCertificate :=
          { b := discard.b }
        let directOK := direct.check
          logTerms pZeroTerms wTerms dTerms directN box
        match LRCompactVStagedGroupedLeafCertificate.selectAdaptiveReplay
            logTerms wTerms dTerms directOK box direct with
        | some leaf => emitAccept emitLine index path box leaf
        | none =>
            let splitAxis := lrCompactVHybridDirectDLookaheadSplitAxis
              logTerms pZeroTerms wTerms dTerms directN logFuel box
            let cut := lrCompactVHybridDirectDSplitCut box splitAxis
            emitLine ["N", path, axis splitAxis, rat cut]
            let next ← exportGeneratedWith emitLine
              logTerms pZeroTerms wTerms dTerms directN logFuel
              fuel index (path ++ "L") (box.lower splitAxis cut)
            exportGeneratedWith emitLine
              logTerms pZeroTerms wTerms dTerms directN logFuel
              fuel next (path ++ "R") (box.upper splitAxis cut)

/-- Stream a plan to standard output. -/
def exportGenerated
    (logTerms pZeroTerms wTerms dTerms directN logFuel : ℕ)
    (fuel index : ℕ) (path : String) (box : CertificateBox) : IO ℕ :=
  exportGeneratedWith stdoutLine
    logTerms pZeroTerms wTerms dTerms directN logFuel
    fuel index path box

private def exportPlanWith
    (emitLine : List String → IO Unit)
    (logTerms pZeroTerms wTerms dTerms directN logFuel fuel : ℕ)
    (root : CertificateBox) : IO Unit := do
  emitLine (["H", "compact-v-staged-plan-v1", toString logTerms,
    toString pZeroTerms, toString wTerms, toString dTerms,
    toString directN, toString logFuel, toString fuel] ++ boxFields root)
  let count ← exportGeneratedWith emitLine
    logTerms pZeroTerms wTerms dTerms directN logFuel fuel 0 "r" root
  emitLine ["E", toString count]

/-- Emit a self-describing plan with a header and final terminal count. -/
def exportPlan
    (logTerms pZeroTerms wTerms dTerms directN logFuel fuel : ℕ)
    (root : CertificateBox) : IO Unit := do
  exportPlanWith stdoutLine
    logTerms pZeroTerms wTerms dTerms directN logFuel fuel root

/-- Stream a plan directly to a file, keeping generation memory independent
of the number of terminals. -/
def exportPlanToFile
    (logTerms pZeroTerms wTerms dTerms directN logFuel fuel : ℕ)
    (root : CertificateBox) (output : System.FilePath) : IO Unit :=
  IO.FS.withFile output .write fun handle => do
    exportPlanWith
      (fun fields => handle.putStrLn (renderLine fields))
      logTerms pZeroTerms wTerms dTerms directN logFuel fuel root
    handle.flush

end LRCompactVStagedGroupedPlanExporter
end CourtadeKumar
