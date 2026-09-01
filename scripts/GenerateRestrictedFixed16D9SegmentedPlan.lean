import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteD9HybridCheckedTree

/-!
# Optimized deterministic plan emitter for restricted fixed-16 finite-D9

This executable is untrusted generation infrastructure. It emits canonical
tab-separated plans whose terminals are later replayed by ordinary Lean
kernel checking. Its search policy:

* discards the exact `k <= s` wedge before interval-AD work;
* forces the fixed-16 root into six `k` slabs cut at
  `1/8, 1/4, 1/2, 1, 2`;
* chooses the largest exact normalized coordinate width and bisects it at its
  exact midpoint; and
* passes computed child probes into recursion, avoiding duplicate evaluation.

The centered accepted-leaf hook evaluates the singleton-center value and the
whole-box derivatives once, and exposes the exact midpoint lower bound as the
split score.  The final generated terminal is still checked independently
against its external path box.

The `slab` and `all-slabs` commands emit independent checkpoint plans.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRFiniteDeterminantRestrictedFixed16SegmentedPlan

inductive AcceptFlavor where
  | centered
  | fallback
  deriving DecidableEq, Repr

inductive SearchTree where
  | accept (flavor : AcceptFlavor)
  | discardIrrelevant
  | discardWedge
  | split (axis : CertificateAxis) (cut : ℚ)
      (lower upper : SearchTree)

inductive TerminalKind where
  | accept (flavor : AcceptFlavor)
  | discardIrrelevant
  | discardWedge

structure CenteredCandidate where
  payloadValid : Bool
  accepts : Bool
  lowerBound : ℚ

namespace CenteredHook

/- This untrusted search summary supplies no proof authority: every emitted
centered terminal later passes the exact hybrid checker in its own kernel
receipt. -/
def candidate? (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : Option CenteredCandidate :=
  let certificate := LRFiniteDeterminantD9CenteredCertificate.auto
    sqrtFuel logFuel box
  let evaluation := certificate.evaluate terms box
  let payloadValid := certificate.payloadCheck box
  some
    { payloadValid := payloadValid
      accepts := payloadValid && evaluation.check box
      lowerBound := evaluation.lowerBound box }

end CenteredHook

structure LeafProbe where
  terminal? : Option TerminalKind
  score : ℚ

structure SplitCandidate where
  axis : CertificateAxis
  cut : ℚ
  lowerBox : CertificateBox
  upperBox : CertificateBox
  lowerProbe : LeafProbe
  upperProbe : LeafProbe
  score : ℚ

def successScore : ℚ := 10 ^ 30
def invalidScore : ℚ := -(10 ^ 30)

def validLowerScore (valid : Bool) (enclosure : RationalEnclosure) : ℚ :=
  if valid then enclosure.lower else invalidScore

def fallbackDiscardCheckWithData (terms : Nat) (box : CertificateBox)
    (data : LRFiniteDeterminantD9HybridAcceptData) : Bool :=
  match lrPhysicalDiscardFirst box with
  | some reason =>
      lrHighShapeVDiscardCheck terms box (.physical reason)
  | none =>
      lrHighShapeVDiscardCheck terms box (.jNonpositive
        (LRFiniteDeterminantD9PayloadFree.midpointBase data))

/- Evaluate fallback data once. A failed centered candidate does not suppress
the established direct/zero-face fallback. -/
def probeLeafAtPrecision (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : LeafProbe :=
  if LRFiniteDeterminantRestrictedD9PayloadFree.geometricDiscardCheck box then
    { terminal? := some .discardWedge, score := successScore }
  else
    let centered := CenteredHook.candidate? terms sqrtFuel logFuel box
    match centered with
    | some candidate =>
        if candidate.accepts then
          { terminal? := some (.accept .centered), score := successScore }
        else
          let fallbackData := LRFiniteDeterminantD9PayloadFree.autoData
            terms sqrtFuel logFuel box
          let fallbackValid :=
            LRFiniteDeterminantD9HybridAcceptData.payloadCheck box fallbackData
          let fallbackEnclosure :=
            LRFiniteDeterminantD9HybridAcceptData.enclose terms box fallbackData
          if fallbackValid && fallbackEnclosure.provesNonnegative then
            { terminal? := some (.accept .fallback), score := successScore }
          else if fallbackDiscardCheckWithData terms box fallbackData then
            { terminal? := some .discardIrrelevant, score := successScore }
          else
            { terminal? := none
              score := max
                (if candidate.payloadValid then candidate.lowerBound
                  else invalidScore)
                (validLowerScore fallbackValid fallbackEnclosure) }
    | none =>
        let fallbackData := LRFiniteDeterminantD9PayloadFree.autoData
          terms sqrtFuel logFuel box
        let fallbackValid :=
          LRFiniteDeterminantD9HybridAcceptData.payloadCheck box fallbackData
        let fallbackEnclosure :=
          LRFiniteDeterminantD9HybridAcceptData.enclose terms box fallbackData
        if fallbackValid && fallbackEnclosure.provesNonnegative then
          { terminal? := some (.accept .fallback), score := successScore }
        else if fallbackDiscardCheckWithData terms box fallbackData then
          { terminal? := some .discardIrrelevant, score := successScore }
        else
          { terminal? := none
            score := validLowerScore fallbackValid fallbackEnclosure }

def cheapSqrtFuel : Nat := 12
def cheapLogFuel : Nat := 8

/- Search first with inexpensive transcendental proposals.  When they already
accept a leaf, the emitted plan may safely retain that topology because its
header records the requested (possibly stronger) replay precision and the
generated Lean receipt independently recomputes that final predicate.  Only
an unresolved cheap probe pays for one requested higher-precision proposal.
This is an optimization of untrusted topology search, not proof authority. -/
def probeLeaf (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : LeafProbe :=
  let fastSqrtFuel := min cheapSqrtFuel sqrtFuel
  let fastLogFuel := min cheapLogFuel logFuel
  let fast := probeLeafAtPrecision terms fastSqrtFuel fastLogFuel box
  if fast.terminal?.isSome then fast
  else if fastSqrtFuel = sqrtFuel ∧ fastLogFuel = logFuel then fast
  else
    probeLeafAtPrecision terms sqrtFuel logFuel box

def axisBounds (box : CertificateBox) : CertificateAxis → ℚ × ℚ
  | .s => (box.sLo, box.sHi)
  | .k => (box.kLo, box.kHi)
  | .chi => (box.chiLo, box.chiHi)

def fractionalCut (box : CertificateBox) (axis : CertificateAxis)
    (numerator denominator : Nat) : ℚ :=
  let bounds := axisBounds box axis
  bounds.1 + (numerator : ℚ) * (bounds.2 - bounds.1) / denominator

def splitCandidate (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (axis : CertificateAxis) (cut : ℚ) :
    SplitCandidate :=
  let lowerBox := box.lower axis cut
  let upperBox := box.upper axis cut
  let lowerProbe := probeLeaf terms sqrtFuel logFuel lowerBox
  let upperProbe := probeLeaf terms sqrtFuel logFuel upperBox
  { axis := axis
    cut := cut
    lowerBox := lowerBox
    upperBox := upperBox
    lowerProbe := lowerProbe
    upperProbe := upperProbe
    score := min lowerProbe.score upperProbe.score }

/- Keep the left candidate on ties, making list order the deterministic tie
break. -/
def betterCandidate (left right : SplitCandidate) : SplitCandidate :=
  if left.score < right.score then right else left

def bestCandidate? : List SplitCandidate → Option SplitCandidate
  | [] => none
  | first :: rest => some (rest.foldl betterCandidate first)

/- Exact relative widths.  The fixed-16 roots have positive `sLo` and `kLo`;
`chi` already has unit scale.  Ties are resolved `s`, then `k`, then `chi`.
This balanced rule is the audited policy that closes the representative slab
within depth 20; asymmetric quarter cuts can create arbitrarily deep slivers. -/
def chooseAxis (box : CertificateBox) : CertificateAxis :=
  let ss := (box.sHi - box.sLo) / box.sLo
  let sk := (box.kHi - box.kLo) / box.kLo
  let sc := box.chiHi - box.chiLo
  if ss ≥ sk ∧ ss ≥ sc then .s
  else if sk ≥ sc then .k
  else .chi

def chooseSplit? (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (_probe : LeafProbe) : Option SplitCandidate :=
  let axis := chooseAxis box
  let bounds := axisBounds box axis
  if bounds.1 < bounds.2 then
    some (splitCandidate terms sqrtFuel logFuel box axis
      (fractionalCut box axis 1 2))
  else
    let fallbackAxis := chooseAxis box
    let fallbackBounds := axisBounds box fallbackAxis
    if fallbackBounds.1 < fallbackBounds.2 then
      some (splitCandidate terms sqrtFuel logFuel box fallbackAxis
        (fractionalCut box fallbackAxis 1 2))
    else none

def treeOfTerminal : TerminalKind → SearchTree
  | .accept flavor => .accept flavor
  | .discardIrrelevant => .discardIrrelevant
  | .discardWedge => .discardWedge

def buildTreeWithProbe (terms sqrtFuel logFuel : Nat) :
    Nat → CertificateBox → LeafProbe → Option SearchTree
  | 0, _box, probe => probe.terminal?.map treeOfTerminal
  | fuel + 1, box, probe =>
      match probe.terminal? with
      | some terminal => some (treeOfTerminal terminal)
      | none =>
          match chooseSplit? terms sqrtFuel logFuel box probe with
          | none => none
          | some split =>
              match buildTreeWithProbe terms sqrtFuel logFuel fuel
                  split.lowerBox split.lowerProbe with
              | none => none
              | some lower =>
                  match buildTreeWithProbe terms sqrtFuel logFuel fuel
                      split.upperBox split.upperProbe with
                  | none => none
                  | some upper =>
                      some (.split split.axis split.cut lower upper)

def buildTree (terms sqrtFuel logFuel fuel : Nat)
    (box : CertificateBox) : Option SearchTree :=
  buildTreeWithProbe terms sqrtFuel logFuel fuel box
    (probeLeaf terms sqrtFuel logFuel box)

structure UnresolvedLeaf where
  path : String
  box : CertificateBox
  probe : LeafProbe

def firstUnresolvedWithProbe (terms sqrtFuel logFuel : Nat) :
    Nat → String → CertificateBox → LeafProbe → Option UnresolvedLeaf
  | 0, path, box, probe =>
      if probe.terminal?.isSome then none else some { path, box, probe }
  | fuel + 1, path, box, probe =>
      match probe.terminal? with
      | some _ => none
      | none =>
          match chooseSplit? terms sqrtFuel logFuel box probe with
          | none => some { path, box, probe }
          | some split =>
              match firstUnresolvedWithProbe terms sqrtFuel logFuel fuel
                  (path ++ "L") split.lowerBox split.lowerProbe with
              | some unresolved => some unresolved
              | none => firstUnresolvedWithProbe terms sqrtFuel logFuel fuel
                  (path ++ "U") split.upperBox split.upperProbe

def firstUnresolved (terms sqrtFuel logFuel fuel : Nat)
    (box : CertificateBox) : Option UnresolvedLeaf :=
  firstUnresolvedWithProbe terms sqrtFuel logFuel fuel "r" box
    (probeLeaf terms sqrtFuel logFuel box)

private def reportUnresolved (terms sqrtFuel logFuel fuel : Nat)
    (box : CertificateBox) : IO Unit := do
  match firstUnresolved terms sqrtFuel logFuel fuel box with
  | none => IO.println "unresolved diagnostic unexpectedly found no frontier"
  | some unresolved =>
      let centered := (CenteredHook.candidate? terms sqrtFuel logFuel
        unresolved.box).getD
        { payloadValid := false, accepts := false, lowerBound := invalidScore }
      let fallbackData := LRFiniteDeterminantD9PayloadFree.autoData
        terms sqrtFuel logFuel unresolved.box
      let fallbackValid := LRFiniteDeterminantD9HybridAcceptData.payloadCheck
        unresolved.box fallbackData
      let fallbackEnclosure :=
        LRFiniteDeterminantD9HybridAcceptData.enclose terms unresolved.box
          fallbackData
      IO.println (String.intercalate "\t" (["FRONTIER", unresolved.path,
        toString unresolved.box.sLo, toString unresolved.box.sHi,
        toString unresolved.box.kLo, toString unresolved.box.kHi,
        toString unresolved.box.chiLo, toString unresolved.box.chiHi] ++
        [ toString (decide ((0 : ℚ) ≤ unresolved.probe.score))
        , toString centered.payloadValid
        , toString centered.accepts
        , toString (decide ((0 : ℚ) ≤ centered.lowerBound))
        , toString fallbackValid
        , toString (decide ((0 : ℚ) ≤ fallbackEnclosure.lower))
        , toString (decide ((0 : ℚ) ≤ fallbackEnclosure.upper))
        , toString fallbackEnclosure.provesNonnegative
        , toString (fallbackDiscardCheckWithData terms unresolved.box
            fallbackData) ]))

/- A separate bottom-up pruning pass would retest exactly the same parent
predicate already tested before every adaptive split, so it cannot remove an
adaptive node under a deterministic leaf checker. The five forced slab nodes
are intentionally exempt: retesting them would reintroduce the costly broad
boxes that the fixed skeleton is designed to avoid. -/

/-! ## Forced fixed-16 k slabs -/

def fixedSlabRoots : List CertificateBox :=
  let root := lrDeterminantFixed16KLeFourRoot
  [ root.lower .k (1 / 8)
  , (root.upper .k (1 / 8)).lower .k (1 / 4)
  , (root.upper .k (1 / 4)).lower .k (1 / 2)
  , (root.upper .k (1 / 2)).lower .k 1
  , (root.upper .k 1).lower .k 2
  , root.upper .k 2 ]

/- Sixteen deterministic checkpoint cells per slab: split `s` and `k` once
at their exact midpoints, then split `chi` into four equal intervals.  The
fixed skeleton is independent of certificate arithmetic, so completed cells
can be retained and merged without replaying sibling searches.  Cell indices
are lower-first in `(s,k,chi)` lexicographic order. -/
def fixedCellRoots (root : CertificateBox) : List CertificateBox :=
  let sCut := fractionalCut root .s 1 2
  let sRoots := [root.lower .s sCut, root.upper .s sCut]
  sRoots.flatMap fun sBox =>
    let kCut := fractionalCut sBox .k 1 2
    let kRoots := [sBox.lower .k kCut, sBox.upper .k kCut]
    kRoots.flatMap fun kBox =>
      let chiOne := fractionalCut kBox .chi 1 4
      let chiTwo := fractionalCut kBox .chi 1 2
      let chiThree := fractionalCut kBox .chi 3 4
      [ kBox.lower .chi chiOne
      , (kBox.upper .chi chiOne).lower .chi chiTwo
      , (kBox.upper .chi chiTwo).lower .chi chiThree
      , kBox.upper .chi chiThree ]

def fixedCheckpointRoots : Nat → CertificateBox → List CertificateBox
  | 0, root => [root]
  | level + 1, root =>
      (fixedCellRoots root).flatMap (fixedCheckpointRoots level)

def assembleSlabs : List SearchTree → Option SearchTree
  | [slab0, slab1, slab2, slab3, slab4, slab5] =>
      some <| .split .k 1
        (.split .k (1 / 4)
          (.split .k (1 / 8) slab0 slab1)
          (.split .k (1 / 2) slab2 slab3))
        (.split .k 2 slab4 slab5)
  | _ => none

def buildSlabs (terms sqrtFuel logFuel fuel : Nat) :
    List CertificateBox → Option (List SearchTree)
  | [] => some []
  | box :: boxes => do
      let tree ← buildTree terms sqrtFuel logFuel fuel box
      let trees ← buildSlabs terms sqrtFuel logFuel fuel boxes
      pure (tree :: trees)

def buildForcedTree (terms sqrtFuel logFuel fuel : Nat) : Option SearchTree :=
  match buildSlabs terms sqrtFuel logFuel fuel fixedSlabRoots with
  | none => none
  | some slabs => assembleSlabs slabs

/-! ## Canonical plan serialization -/

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

private def emitTree
    (emitLine : List String → IO Unit) :
    Nat → String → CertificateBox → SearchTree → IO Nat
  | index, path, box, .accept .fallback => do
      emitLine (terminalLine "A" index path "fallback" box)
      pure (index + 1)
  | index, path, box, .accept .centered => do
      emitLine (terminalLine "C" index path "centered" box)
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

private def atomicPlanWrite (output : System.FilePath)
    (writer : IO.FS.Handle → IO Nat) : IO Nat := do
  let staged := System.FilePath.mk (output.toString ++ ".building")
  let count ← IO.FS.withFile staged .write fun handle => do
    let count ← writer handle
    handle.flush
    pure count
  IO.FS.rename staged output
  pure count

private def exportFullPlanToFile
    (terms sqrtFuel logFuel adaptiveDepth : Nat)
    (tree : SearchTree) (output : System.FilePath) : IO Nat :=
  atomicPlanWrite output fun handle => do
    let emitLine (fields : List String) :=
      handle.putStrLn (renderLine fields)
    let totalDepth := adaptiveDepth + 3
    emitLine (["H", "fixed16-restricted-d9-plan-v2", toString terms,
      toString sqrtFuel, toString logFuel, toString totalDepth] ++
      boxFields lrDeterminantFixed16KLeFourRoot)
    let count ← emitTree emitLine 0 "r"
      lrDeterminantFixed16KLeFourRoot tree
    emitLine ["E", toString count]
    pure count

private def exportSlabPlanToFile
    (slabIndex terms sqrtFuel logFuel adaptiveDepth : Nat)
    (root : CertificateBox) (tree : SearchTree)
    (output : System.FilePath) : IO Nat :=
  atomicPlanWrite output fun handle => do
    let emitLine (fields : List String) :=
      handle.putStrLn (renderLine fields)
    emitLine (["H", "fixed16-restricted-d9-slab-plan-v1",
      toString slabIndex, toString terms, toString sqrtFuel,
      toString logFuel, toString adaptiveDepth] ++ boxFields root)
    let count ← emitTree emitLine 0 "r" root tree
    emitLine ["E", toString count]
    pure count

private def exportCellPlanToFile
    (slabIndex cellIndex terms sqrtFuel logFuel adaptiveDepth : Nat)
    (root : CertificateBox) (tree : SearchTree)
    (output : System.FilePath) : IO Nat :=
  atomicPlanWrite output fun handle => do
    let emitLine (fields : List String) :=
      handle.putStrLn (renderLine fields)
    emitLine (["H", "fixed16-restricted-d9-cell-plan-v1",
      toString slabIndex, toString cellIndex, toString terms,
      toString sqrtFuel, toString logFuel, toString adaptiveDepth] ++
      boxFields root)
    let count ← emitTree emitLine 0 "r" root tree
    emitLine ["E", toString count]
    pure count

private def exportCheckpointPlanToFile
    (slabIndex level checkpointIndex terms sqrtFuel logFuel
      adaptiveDepth : Nat)
    (root : CertificateBox) (tree : SearchTree)
    (output : System.FilePath) : IO Nat :=
  atomicPlanWrite output fun handle => do
    let emitLine (fields : List String) :=
      handle.putStrLn (renderLine fields)
    emitLine (["H", "fixed16-restricted-d9-checkpoint-plan-v1",
      toString slabIndex, toString level, toString checkpointIndex,
      toString terms, toString sqrtFuel, toString logFuel,
      toString adaptiveDepth] ++ boxFields root)
    let count ← emitTree emitLine 0 "r" root tree
    emitLine ["E", toString count]
    pure count

structure Counts where
  centered : Nat := 0
  fallback : Nat := 0
  irrelevant : Nat := 0
  wedge : Nat := 0

def Counts.add (left right : Counts) : Counts where
  centered := left.centered + right.centered
  fallback := left.fallback + right.fallback
  irrelevant := left.irrelevant + right.irrelevant
  wedge := left.wedge + right.wedge

def countKinds : SearchTree → Counts
  | .accept .centered => { centered := 1 }
  | .accept .fallback => { fallback := 1 }
  | .discardIrrelevant => { irrelevant := 1 }
  | .discardWedge => { wedge := 1 }
  | .split _ _ lower upper => (countKinds lower).add (countKinds upper)

def defaultTerms : Nat := 8
def defaultSqrtFuel : Nat := 12
def defaultLogFuel : Nat := 8
def defaultDepth : Nat := 18
def defaultOutput : System.FilePath :=
  ".lake/scratch/LRDeterminantFixed16KLeFour.plan.tsv"
def defaultCheckpointDirectory : System.FilePath :=
  ".lake/scratch/LRDeterminantFixed16KLeFourSlabs"

private def parseNat (label value : String) : IO Nat :=
  match value.toNat? with
  | some result => pure result
  | none => throw <| IO.userError (label ++ " must be a natural number")

private def report (label : String) (count : Nat) (tree : SearchTree)
    (output : System.FilePath) : IO Unit := do
  let kinds := countKinds tree
  IO.println ("SUCCESS " ++ label ++
    " terminals=" ++ toString count ++
    " centered=" ++ toString kinds.centered ++
    " fallback=" ++ toString kinds.fallback ++
    " irrelevantDiscards=" ++ toString kinds.irrelevant ++
    " wedgeDiscards=" ++ toString kinds.wedge ++
    " output=" ++ output.toString)

def runFull (depth : Nat) (output : System.FilePath) : IO Unit := do
  match buildForcedTree defaultTerms defaultSqrtFuel defaultLogFuel depth with
  | none =>
      IO.println ("UNRESOLVED fixed16-kLeFour adaptiveDepth=" ++
        toString depth)
  | some tree =>
      let count ← exportFullPlanToFile defaultTerms defaultSqrtFuel
        defaultLogFuel depth tree output
      report ("fixed16-kLeFour adaptiveDepth=" ++ toString depth)
        count tree output

def runSlabWith (slabIndex terms sqrtFuel logFuel depth : Nat)
    (output : System.FilePath) : IO Unit := do
  match fixedSlabRoots[slabIndex]? with
  | none => throw <| IO.userError "slab index must lie in 0..5"
  | some root =>
      match buildTree terms sqrtFuel logFuel depth root with
      | none =>
          IO.println ("UNRESOLVED fixed16-kLeFour slab=" ++
            toString slabIndex ++ " terms=" ++ toString terms ++
            " sqrtFuel=" ++ toString sqrtFuel ++
            " logFuel=" ++ toString logFuel ++
            " adaptiveDepth=" ++ toString depth)
          reportUnresolved terms sqrtFuel logFuel depth root
      | some tree =>
          let count ← exportSlabPlanToFile slabIndex terms
            sqrtFuel logFuel depth root tree output
          report ("fixed16-kLeFour slab=" ++ toString slabIndex ++
            " terms=" ++ toString terms ++
            " sqrtFuel=" ++ toString sqrtFuel ++
            " logFuel=" ++ toString logFuel ++
            " adaptiveDepth=" ++ toString depth) count tree output

def runSlab (slabIndex depth : Nat) (output : System.FilePath) : IO Unit :=
  runSlabWith slabIndex defaultTerms defaultSqrtFuel defaultLogFuel depth output

def runCellWith (slabIndex cellIndex terms sqrtFuel logFuel depth : Nat)
    (output : System.FilePath) : IO Unit := do
  match fixedSlabRoots[slabIndex]? with
  | none => throw <| IO.userError "slab index must lie in 0..5"
  | some slabRoot =>
      match (fixedCellRoots slabRoot)[cellIndex]? with
      | none => throw <| IO.userError "cell index must lie in 0..15"
      | some root =>
          match buildTree terms sqrtFuel logFuel depth root with
          | none =>
              IO.println ("UNRESOLVED fixed16-kLeFour slab=" ++
                toString slabIndex ++ " cell=" ++ toString cellIndex ++
                " terms=" ++ toString terms ++
                " sqrtFuel=" ++ toString sqrtFuel ++
                " logFuel=" ++ toString logFuel ++
                " adaptiveDepth=" ++ toString depth)
              reportUnresolved terms sqrtFuel logFuel depth root
          | some tree =>
              let count ← exportCellPlanToFile slabIndex cellIndex terms
                sqrtFuel logFuel depth root tree output
              report ("fixed16-kLeFour slab=" ++ toString slabIndex ++
                " cell=" ++ toString cellIndex ++
                " terms=" ++ toString terms ++
                " sqrtFuel=" ++ toString sqrtFuel ++
                " logFuel=" ++ toString logFuel ++
                " adaptiveDepth=" ++ toString depth) count tree output

def runCheckpointWith
    (slabIndex level checkpointIndex terms sqrtFuel logFuel depth : Nat)
    (output : System.FilePath) : IO Unit := do
  match fixedSlabRoots[slabIndex]? with
  | none => throw <| IO.userError "slab index must lie in 0..5"
  | some slabRoot =>
      match (fixedCheckpointRoots level slabRoot)[checkpointIndex]? with
      | none => throw <| IO.userError "checkpoint index is out of range"
      | some root =>
          match buildTree terms sqrtFuel logFuel depth root with
          | none =>
              IO.println ("UNRESOLVED fixed16-kLeFour slab=" ++
                toString slabIndex ++ " checkpointLevel=" ++
                toString level ++ " checkpoint=" ++
                toString checkpointIndex ++ " terms=" ++ toString terms ++
                " sqrtFuel=" ++ toString sqrtFuel ++
                " logFuel=" ++ toString logFuel ++
                " adaptiveDepth=" ++ toString depth)
              reportUnresolved terms sqrtFuel logFuel depth root
          | some tree =>
              let count ← exportCheckpointPlanToFile slabIndex level
                checkpointIndex terms sqrtFuel logFuel depth root tree output
              report ("fixed16-kLeFour slab=" ++ toString slabIndex ++
                " checkpointLevel=" ++ toString level ++ " checkpoint=" ++
                toString checkpointIndex ++ " terms=" ++ toString terms ++
                " sqrtFuel=" ++ toString sqrtFuel ++
                " logFuel=" ++ toString logFuel ++
                " adaptiveDepth=" ++ toString depth) count tree output

def runCheckpointRangeWith
    (slabIndex level start stop terms sqrtFuel logFuel depth : Nat)
    (directory : System.FilePath) : IO Unit := do
  if stop <= start then
    throw <| IO.userError "checkpoint range requires start < stop"
  IO.FS.createDirAll directory
  for offset in List.range (stop - start) do
    let checkpointIndex := start + offset
    let output := directory /
      ("Slab" ++ toString slabIndex ++ "Level" ++ toString level ++
        "Checkpoint" ++ toString checkpointIndex ++ ".tsv")
    runCheckpointWith slabIndex level checkpointIndex terms sqrtFuel logFuel
      depth output

def runAllSlabs (depth : Nat) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for slabIndex in [0, 1, 2, 3, 4, 5] do
    let output := directory / ("Slab" ++ toString slabIndex ++ ".tsv")
    runSlab slabIndex depth output

def usage : String :=
  "usage:\n" ++
  "  fixed16_plan full <adaptive-depth> <output.tsv>\n" ++
  "  fixed16_plan slab <0..5> <adaptive-depth> <output.tsv>\n" ++
  "  fixed16_plan slab-config <0..5> <terms> <sqrt-fuel> <log-fuel> " ++
    "<adaptive-depth> <output.tsv>\n" ++
  "  fixed16_plan cell-config <0..5> <0..15> <terms> <sqrt-fuel> " ++
    "<log-fuel> <adaptive-depth> <output.tsv>\n" ++
  "  fixed16_plan checkpoint-config <0..5> <level> <index> <terms> " ++
    "<sqrt-fuel> <log-fuel> <adaptive-depth> <output.tsv>\n" ++
  "  fixed16_plan checkpoint-range-config <0..5> <level> <start> <stop-exclusive> " ++
    "<terms> <sqrt-fuel> <log-fuel> <adaptive-depth> <output-directory>\n" ++
  "  fixed16_plan all-slabs <adaptive-depth> <output-directory>\n" ++
  "  fixed16_plan <adaptive-depth> <output.tsv>  (legacy full mode)"

def run (args : List String) : IO Unit := do
  match args with
  | "full" :: depth :: output :: [] =>
      runFull (← parseNat "adaptive depth" depth) (System.FilePath.mk output)
  | "slab" :: slab :: depth :: output :: [] =>
      runSlab (← parseNat "slab" slab)
        (← parseNat "adaptive depth" depth) (System.FilePath.mk output)
  | "slab-config" :: slab :: terms :: sqrtFuel :: logFuel :: depth ::
      output :: [] =>
      runSlabWith (← parseNat "slab" slab) (← parseNat "terms" terms)
        (← parseNat "sqrt fuel" sqrtFuel) (← parseNat "log fuel" logFuel)
        (← parseNat "adaptive depth" depth) (System.FilePath.mk output)
  | "cell-config" :: slab :: cell :: terms :: sqrtFuel :: logFuel ::
      depth :: output :: [] =>
      runCellWith (← parseNat "slab" slab) (← parseNat "cell" cell)
        (← parseNat "terms" terms) (← parseNat "sqrt fuel" sqrtFuel)
        (← parseNat "log fuel" logFuel) (← parseNat "adaptive depth" depth)
        (System.FilePath.mk output)
  | "checkpoint-config" :: slab :: level :: checkpoint :: terms ::
      sqrtFuel :: logFuel :: depth :: output :: [] =>
      runCheckpointWith (← parseNat "slab" slab)
        (← parseNat "checkpoint level" level)
        (← parseNat "checkpoint" checkpoint) (← parseNat "terms" terms)
        (← parseNat "sqrt fuel" sqrtFuel) (← parseNat "log fuel" logFuel)
        (← parseNat "adaptive depth" depth) (System.FilePath.mk output)
  | "checkpoint-range-config" :: slab :: level :: start :: stop :: terms ::
      sqrtFuel :: logFuel :: depth :: directory :: [] =>
      runCheckpointRangeWith (← parseNat "slab" slab)
        (← parseNat "checkpoint level" level)
        (← parseNat "checkpoint start" start)
        (← parseNat "checkpoint stop" stop) (← parseNat "terms" terms)
        (← parseNat "sqrt fuel" sqrtFuel) (← parseNat "log fuel" logFuel)
        (← parseNat "adaptive depth" depth)
        (System.FilePath.mk directory)
  | "all-slabs" :: depth :: directory :: [] =>
      runAllSlabs (← parseNat "adaptive depth" depth)
        (System.FilePath.mk directory)
  | depth :: output :: [] =>
      runFull (← parseNat "adaptive depth" depth)
        (System.FilePath.mk output)
  | [] => runFull defaultDepth defaultOutput
  | _ => throw <| IO.userError usage

end LRFiniteDeterminantRestrictedFixed16SegmentedPlan
end CourtadeKumar

def main (args : List String) : IO Unit :=
  CourtadeKumar.LRFiniteDeterminantRestrictedFixed16SegmentedPlan.run args
