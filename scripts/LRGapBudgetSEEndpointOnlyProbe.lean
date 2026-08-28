import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

open CourtadeKumar
open CourtadeKumar.LRGapBudgetSECombinedAutoTree

def endpointAccept (terms sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    Option LRGapBudgetSEDerivativeAcceptData :=
  if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .endpoint then some .endpoint
  else if LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel box
      .endpointRetainedQ then some .endpointRetainedQ
  else none

def buildEndpointTree (terms sqrtFuel logFuel : ℕ) :
    ℕ → CertificateBox → Option Tree
  | 0, box =>
      match endpointAccept terms sqrtFuel logFuel box with
      | some data => some (.accept data)
      | none => match autoDiscard box with
        | some data => some (.discard data)
        | none => none
  | fuel + 1, box =>
      match endpointAccept terms sqrtFuel logFuel box with
      | some data => some (.accept data)
      | none => match autoDiscard box with
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

def axisText : CertificateAxis → String
  | .s => ".s"
  | .k => ".k"
  | .chi => ".chi"

def acceptText : LRGapBudgetSEDerivativeAcceptData → String
  | .regular => ".regular"
  | .endpoint => ".endpoint"
  | .endpointRetainedQ => ".endpointRetainedQ"

def discardText : LRGapBudgetSEDiscardData → String
  | .eBelowFourS => ".eBelowFourS"
  | .eAtLeastOne => ".eAtLeastOne"
  | .xBelowHighShape => ".xBelowHighShape"
  | .vBelowThird => ".vBelowThird"

def treeText : Tree → String
  | .accept data => "(.accept " ++ acceptText data ++ ")"
  | .discard data => "(.discard " ++ discardText data ++ ")"
  | .split axis cut lower upper =>
      "(.split " ++ axisText axis ++ " (" ++ toString cut ++ ") " ++
        treeText lower ++ " " ++ treeText upper ++ ")"

def writeTree : IO Unit :=
  match buildEndpointTree 2 8 6 20 lrGapBudgetSETailRoot with
  | none => throw (IO.userError "endpoint-only generation failed")
  | some result => IO.FS.writeFile
      "InformationTheory/CourtadeKumar/LRGapBudgetSEGeneratedTailTreeData.lean"
      ("import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree\n\n" ++
        "namespace CourtadeKumar\n" ++
        "namespace LRGapBudgetSEGeneratedTailTreeData\n\n" ++
        "open LRGapBudgetSECombinedAutoTree\n\n" ++
        "def tree : Tree :=\n  " ++ treeText result ++ "\n\n" ++
        "end LRGapBudgetSEGeneratedTailTreeData\n" ++
        "end CourtadeKumar\n")

def treeStats : Tree → Nat × Nat × Nat
  | .accept _ => (1, 0, 1)
  | .discard _ => (1, 0, 0)
  | .split _ _ lower upper =>
      let l := treeStats lower
      let u := treeStats upper
      (1 + l.1 + u.1, 1 + l.2.1 + u.2.1, l.2.2 + u.2.2)

def report (terms sqrtFuel logFuel fuel : Nat) : IO Unit :=
  match buildEndpointTree terms sqrtFuel logFuel fuel lrGapBudgetSETailRoot with
  | none => IO.println s!"({terms},{sqrtFuel},{logFuel},{fuel}): failed"
  | some result =>
      let stats := treeStats result
      IO.println s!"({terms},{sqrtFuel},{logFuel},{fuel}): nodes={stats.1}, splits={stats.2.1}, accepts={stats.2.2}"

#eval report 0 8 6 22
#eval report 1 8 6 22
#eval report 2 8 6 20
#eval report 3 8 6 20
#eval report 4 8 6 20
