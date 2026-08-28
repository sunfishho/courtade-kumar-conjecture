import InformationTheory.CourtadeKumar.LRGapBudgetSEGeneratedTailTreeData

open CourtadeKumar
open CourtadeKumar.LRGapBudgetSECombinedAutoTree

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

def ratText (q : ℚ) : String := "(" ++ toString q ++ ")"

def treeText : Tree → String
  | .accept data => "(.accept " ++ acceptText data ++ ")"
  | .discard data => "(.discard " ++ discardText data ++ ")"
  | .split axis cut lower upper =>
      "(.split " ++ axisText axis ++ " " ++ ratText cut ++ " " ++
        treeText lower ++ " " ++ treeText upper ++ ")"

structure ChunkSpec where
  name : String
  box : String
  body : String
  fuel : Nat

structure ChunkResult where
  tree : String
  proof : String
  chunks : List ChunkSpec
  next : Nat

def lowerBoxText (box : String) (axis : CertificateAxis) (cut : ℚ) : String :=
  "(" ++ box ++ ").lower " ++ axisText axis ++ " " ++ ratText cut

def upperBoxText (box : String) (axis : CertificateAxis) (cut : ℚ) : String :=
  "(" ++ box ++ ").upper " ++ axisText axis ++ " " ++ ratText cut

def chunkify (threshold : ℕ) :
    ℕ → ℕ → String → Tree → ChunkResult
  | fuel, next, box, tree =>
      let chunkThreshold := if next < 15 then threshold else 50
      if treeNodes tree ≤ chunkThreshold then
        let name := "chunk" ++ toString next
        { tree := name
          proof := name ++ "_check"
          chunks := [{ name := name
                       box := box
                       body := treeText tree
                       fuel := fuel }]
          next := next + 1 }
      else
        match tree with
        | .split axis cut lower upper =>
            let lowerResult := chunkify threshold (fuel - 1) next
              (lowerBoxText box axis cut) lower
            let upperResult := chunkify threshold (fuel - 1) lowerResult.next
              (upperBoxText box axis cut) upper
            let skeleton := "(.split " ++ axisText axis ++ " " ++ ratText cut ++
              " " ++ lowerResult.tree ++ " " ++ upperResult.tree ++ ")"
            { tree := skeleton
              proof := "⟨" ++ lowerResult.proof ++ ", " ++
                upperResult.proof ++ "⟩"
              chunks := lowerResult.chunks ++ upperResult.chunks
              next := upperResult.next }
        | _ =>
            let name := "chunk" ++ toString next
            { tree := name
              proof := name ++ "_check"
              chunks := [{ name := name
                           box := box
                           body := treeText tree
                           fuel := fuel }]
              next := next + 1 }
termination_by fuel next box tree => treeNodes tree
decreasing_by
  all_goals simp [treeNodes]
  all_goals omega

def chunkDefinition (chunk : ChunkSpec) : String :=
  "def " ++ chunk.name ++ " : Tree :=\n  " ++ chunk.body ++ "\n\n"

def chunkTheorem (chunk : ChunkSpec) : String :=
  "set_option maxRecDepth 1000000 in\n" ++
  "set_option maxHeartbeats 0 in\n" ++
  "theorem " ++ chunk.name ++ "_generated_eq :\n" ++
  "    buildEndpointTree 2 8 6 " ++ toString chunk.fuel ++ "\n" ++
  "      (" ++ chunk.box ++ ") = some " ++ chunk.name ++ " := by\n" ++
  "  rfl'\n\n" ++
  "theorem " ++ chunk.name ++ "_check :\n" ++
  "    " ++ chunk.name ++ ".check\n" ++
  "      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)\n" ++
  "      lrGapBudgetSEDiscardCheck (" ++ chunk.box ++ ") = true :=\n" ++
  "  buildEndpointTree_check_of_eq 2 8 6 " ++ toString chunk.fuel ++
    " (" ++ chunk.box ++ ") " ++ chunk.name ++ " " ++
    chunk.name ++ "_generated_eq\n\n"

def checkedNames (chunks : List ChunkSpec) : String :=
  String.intercalate ", " (chunks.map fun chunk => chunk.name ++ "_check")

def batchText (chunks : List ChunkSpec) : String :=
  "import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree\n\n" ++
  "namespace CourtadeKumar\n" ++
  "namespace LRGapBudgetSEGeneratedTailReplay\n\n" ++
  "open LRGapBudgetSECombinedAutoTree\n\n" ++
  String.join (chunks.map chunkDefinition) ++
  String.join (chunks.map chunkTheorem) ++
  "end LRGapBudgetSEGeneratedTailReplay\n" ++
  "end CourtadeKumar\n"

def batchImport (index : ℕ) : String :=
  "import InformationTheory.CourtadeKumar." ++
    "LRGapBudgetSEGeneratedTailReplayBatch" ++ toString index ++ "\n"

def assemblyText (batchCount : ℕ) (result : ChunkResult) : String :=
  String.join ((List.range batchCount).map batchImport) ++ "\n" ++
  "namespace CourtadeKumar\n" ++
  "namespace LRGapBudgetSEGeneratedTailReplay\n\n" ++
  "open LRGapBudgetSECombinedAutoTree\n\n" ++
  "def tree : Tree :=\n  " ++ result.tree ++ "\n\n" ++
  "set_option maxRecDepth 1000000 in\n" ++
  "theorem check_eq_true :\n" ++
  "    tree.check\n" ++
  "      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)\n" ++
  "      lrGapBudgetSEDiscardCheck lrGapBudgetSETailRoot = true := by\n" ++
  "  simp only [tree, SubdivisionCertificate.check, Bool.and_eq_true]\n" ++
  "  exact " ++ result.proof ++ "\n\n" ++
  "end LRGapBudgetSEGeneratedTailReplay\n" ++
  "end CourtadeKumar\n"

def writeReplay : IO Unit := do
  let result := chunkify 80 20 0 "lrGapBudgetSETailRoot"
    LRGapBudgetSEGeneratedTailTreeData.tree
  let chunks := result.chunks
  let batchSize := 1
  let batchCount := (chunks.length + batchSize - 1) / batchSize
  for index in List.range batchCount do
    let batch := (chunks.drop (index * batchSize)).take batchSize
    IO.FS.writeFile
      ("InformationTheory/CourtadeKumar/" ++
        "LRGapBudgetSEGeneratedTailReplayBatch" ++ toString index ++ ".lean")
      (batchText batch)
  IO.FS.writeFile
    "InformationTheory/CourtadeKumar/LRGapBudgetSEGeneratedTailReplay.lean"
    (assemblyText batchCount result)

#eval writeReplay
