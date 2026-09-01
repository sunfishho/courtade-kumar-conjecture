import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteD9CheckedTree

/-!
# Deterministic plan emitter for the restricted fixed-16 finite-D9 row

This executable is untrusted generation infrastructure.  It searches for a
payload-free finite-D9 subdivision and writes a canonical tab-separated plan.
The companion Python renderer validates every printed box against the exact
root-relative path before emitting independently kernel-checked terminal
chunks and an arithmetic-free structural assembly.

The cheap exact wedge test is deliberately attempted before any interval-AD
work.  A box satisfying `kHi <= sLo` contains no point with `s < k`, which is
exactly the extra relevance hypothesis carried by the restricted checked-tree
interface.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRFiniteDeterminantRestrictedFixed16SegmentedPlan

inductive SearchTree where
  | accept
  | discardIrrelevant
  | discardWedge
  | split (axis : CertificateAxis) (cut : ℚ)
      (lower upper : SearchTree)

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

/- Derivatives guide only the untrusted subdivision choice.  Every terminal
is independently rechecked against its reconstructed external box. -/
def heuristicAD (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : IntervalAD :=
  match LRFiniteDeterminantD9PayloadFree.autoData
      terms sqrtFuel logFuel box with
  | .regular certificate => certificate.evaluateAD terms box
  | .zeroFace certificate => certificate.regularShell.evaluateAD terms box

def chooseAxis (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : CertificateAxis :=
  let value := heuristicAD terms sqrtFuel logFuel box
  let ss := value.derivS.maxAbs * RationalEnclosure.radius box.sInterval
  let sk := value.derivK.maxAbs * RationalEnclosure.radius box.kInterval
  let sc := value.derivChi.maxAbs * RationalEnclosure.radius box.chiInterval
  if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
  else if sk ≥ sc ∧ box.kLo < box.kHi then .k
  else .chi

/- The ordering is a runtime optimization only.  It does not contribute any
proof authority: the generated terminal modules replay the corresponding
Boolean predicate in Lean's ordinary kernel. -/
def buildTree (terms sqrtFuel logFuel : Nat) :
    Nat → CertificateBox → Option SearchTree
  | 0, box =>
      if LRFiniteDeterminantRestrictedD9PayloadFree.geometricDiscardCheck box
      then some .discardWedge
      else if LRFiniteDeterminantD9PayloadFree.accepts
          terms sqrtFuel logFuel box () then
        some .accept
      else if LRFiniteDeterminantD9PayloadFree.discardCheck
          terms sqrtFuel logFuel box () then
        some .discardIrrelevant
      else none
  | fuel + 1, box =>
      if LRFiniteDeterminantRestrictedD9PayloadFree.geometricDiscardCheck box
      then some .discardWedge
      else if LRFiniteDeterminantD9PayloadFree.accepts
          terms sqrtFuel logFuel box () then
        some .accept
      else if LRFiniteDeterminantD9PayloadFree.discardCheck
          terms sqrtFuel logFuel box () then
        some .discardIrrelevant
      else
        let axis := chooseAxis terms sqrtFuel logFuel box
        let cut := axisCut box axis
        match buildTree terms sqrtFuel logFuel fuel (box.lower axis cut) with
        | none => none
        | some lower =>
            match buildTree terms sqrtFuel logFuel fuel
                (box.upper axis cut) with
            | none => none
            | some upper => some (.split axis cut lower upper)

private def renderLine (fields : List String) : String :=
  String.intercalate "\t" fields

private def rat (q : ℚ) : String := toString q

private def axisName : CertificateAxis → String
  | .s => "s"
  | .k => "k"
  | .chi => "chi"

private def boxFields (box : CertificateBox) : List String :=
  [rat box.sLo, rat box.sHi, rat box.kLo, rat box.kHi,
    rat box.chiLo, rat box.chiHi]

private def terminalLine (tag : String) (index : Nat) (path : String)
    (kind : String) (box : CertificateBox) : List String :=
  [tag, toString index, path, kind] ++ boxFields box

/- Emit lower-first preorder.  Terminal indices therefore give a stable
chunking order while paths retain the complete structural authority. -/
private def emitTree
    (emitLine : List String → IO Unit) :
    Nat → String → CertificateBox → SearchTree → IO Nat
  | index, path, box, .accept => do
      emitLine (terminalLine "A" index path "accept" box)
      pure (index + 1)
  | index, path, box, .discardIrrelevant => do
      emitLine (terminalLine "X" index path "irrelevant" box)
      pure (index + 1)
  | index, path, box, .discardWedge => do
      emitLine (terminalLine "W" index path "wedge" box)
      pure (index + 1)
  | index, path, box, .split axis cut lower upper => do
      emitLine ["N", path, axisName axis, rat cut]
      let next ← emitTree emitLine index (path ++ "L")
        (box.lower axis cut) lower
      emitTree emitLine next (path ++ "R") (box.upper axis cut) upper

private def exportPlanToFile
    (terms sqrtFuel logFuel depth : Nat)
    (root : CertificateBox) (tree : SearchTree)
    (output : System.FilePath) : IO Nat := do
  let staged := System.FilePath.mk (output.toString ++ ".building")
  let count ← IO.FS.withFile staged .write fun handle => do
    let emitLine (fields : List String) :=
      handle.putStrLn (renderLine fields)
    emitLine (["H", "fixed16-restricted-d9-plan-v1", toString terms,
      toString sqrtFuel, toString logFuel, toString depth] ++ boxFields root)
    let count ← emitTree emitLine 0 "r" root tree
    emitLine ["E", toString count]
    handle.flush
    pure count
  IO.FS.rename staged output
  pure count

private def countKinds : SearchTree → Nat × Nat × Nat
  | .accept => (1, 0, 0)
  | .discardIrrelevant => (0, 1, 0)
  | .discardWedge => (0, 0, 1)
  | .split _ _ lower upper =>
      let l := countKinds lower
      let u := countKinds upper
      (l.1 + u.1, l.2.1 + u.2.1, l.2.2 + u.2.2)

def defaultTerms : Nat := 8
def defaultSqrtFuel : Nat := 12
def defaultLogFuel : Nat := 8
def defaultDepth : Nat := 8
def defaultOutput : System.FilePath :=
  ".lake/scratch/LRDeterminantFixed16KLeFour.plan.tsv"

def run (args : List String) : IO Unit := do
  let depth := match args with
    | value :: _ => value.toNat?.getD defaultDepth
    | [] => defaultDepth
  let output := match args with
    | _ :: value :: _ => System.FilePath.mk value
    | _ => defaultOutput
  match buildTree defaultTerms defaultSqrtFuel defaultLogFuel depth
      lrDeterminantFixed16KLeFourRoot with
  | none =>
      IO.println ("UNRESOLVED fixed16-kLeFour depth=" ++ toString depth)
  | some tree =>
      let count ← exportPlanToFile defaultTerms defaultSqrtFuel
        defaultLogFuel depth lrDeterminantFixed16KLeFourRoot tree output
      let kinds := countKinds tree
      IO.println ("SUCCESS fixed16-kLeFour depth=" ++ toString depth ++
        " terminals=" ++ toString count ++
        " accepts=" ++ toString kinds.1 ++
        " irrelevantDiscards=" ++ toString kinds.2.1 ++
        " wedgeDiscards=" ++ toString kinds.2.2 ++
        " output=" ++ output.toString)

end LRFiniteDeterminantRestrictedFixed16SegmentedPlan
end CourtadeKumar

def main (args : List String) : IO Unit :=
  CourtadeKumar.LRFiniteDeterminantRestrictedFixed16SegmentedPlan.run args
