/-!
# Authenticated final-refined ideal topology data

Exact inert NMkh streams after the ten authenticated M refinements and
the two final authenticated N refinements.  Lean packed replay remains
the sole proof authority.
-/

namespace CourtadeKumar.LRIdealFinalRefinedTopologyData

structure SourceRecord where
  name : String
  path : String
  sha256 : String

structure ComponentMetadata where
  nodes : Nat
  leaves : Nat
  naturalLeaves : Nat
  meanLeaves : Nat
  splitK : Nat
  splitChi : Nat
  maxDepth : Nat
  bytes : Nat
  priorMeanReplacements : Nat
  finalNaturalReplacements : Nat
  sha256 : String

def finalManifestFileSha256 : String := "0f5bf40e56912184b5db20c47dbb020188b007d95c4ae76cc4b148a3a245758d"
def finalManifestCoreSha256 : String := "c7aad3429083c454bfb031ae073adbeb3b2c1edc2ea999a25ad2cefa84887490"
def finalExporterSha256 : String := "a25ec797e5d79b7a419885aae5d8409e7a10a442c2caa870f1bd38ee8203c592"
def proofAuthority : String := "Lean packed Boolean replay; this exporter is untrusted"

def provenanceSources : List SourceRecord := [
  { name := "exactRationalArithmeticMirror", path := "lean-formalization/.lake/scratch/AgentIdealCoreExactReplayProbe.py", sha256 := "b92837d59b0ffea9a483d8b0bac3a12bde4e3c2c7ac770029cfacc83366d6ae9" },
  { name := "exactTopologyParser", path := "lean-formalization/.lake/scratch/AgentChunkExplicitIdealCoreTree.py", sha256 := "436b2db9a5df71247bd69266caff39e2a5516439e4b7e7522113980ed9b343d1" },
  { name := "historicalTopologyData", path := "lean-formalization/.lake/scratch/AgentIdealHistoricalTopologyData.lean", sha256 := "3a0963f14d029e392d08bdae2bf5cb4a4b8b64b3dbdbb5ccfa03df3d8d0cbcbb" },
  { name := "historicalTopologyValidator", path := "lean-formalization/.lake/scratch/AgentIdealHistoricalReplayChunkGenerator.py", sha256 := "1f77f94289e9920288dab1a4980a13a5576344611273f9f61efec40bfb4458cc" },
  { name := "leanIntervalEvaluator", path := "lean-formalization/InformationTheory/CourtadeKumar/LRDeterminantIdealIntervalEvaluator.lean", sha256 := "e8a616803ad4903a67a43d741b54301aaf3fa8af50e1ebb8478aa32cfc2f5d5d" },
  { name := "leanNaturalEvaluator", path := "lean-formalization/.lake/scratch/AgentIdealNaturalOracle.lean", sha256 := "ea4481bb609cc755d96832a2a640dace6549e63af69e37d0f87b39ccd7539bdc" },
  { name := "naturalEvaluatorExactMirror", path := "lean-formalization/.lake/scratch/AgentIdealNaturalZeroFaceAudit.py", sha256 := "2a98a46e461b13e37c5e284d2a63424a9c1f28314e3653c4e2f87e247efa9d20" },
  { name := "upstreamManifest", path := "lean-formalization/.lake/scratch/GeneratedIdealCenteredRefined.manifest.json", sha256 := "a7afb2e951046e6b8c0704ea37be6ae05a5e77614122eee0527949987eca4de7" },
  { name := "upstreamProvenanceValidator", path := "lean-formalization/.lake/scratch/AgentIdealCenteredRefinedReplayChunkGenerator.py", sha256 := "3fbebaece4ddd8dd4dde54fa15fad45dce5b01cc60615dbcf7d17e593c985338" },
  { name := "upstreamRefinementExporter", path := "lean-formalization/.lake/scratch/AgentIdealCenteredRefinedTopologyExporter.py", sha256 := "9d13ea9920d44106baf33155c2511f8bdfc4e296e107b12cfa7d92a7aec8300b" }
]

def l7MiddlePacked : String :=
  "hhhhhhkkkkNNkNNkkNNNkkNNkNNkkkMMkMMkMMkkkkMMMkMMkMMkkkkMMkMMkMMkkMMkMMkkkkkhMMhMMkhMMhMMkhMMhMMkkhMMMhMkMMkkhMkMMhkMMkMMkhhMMkMMhhMkMMkhMMhMkMMkkkkkhMMhMMhkMMMkhMMhMMkhkMMkMMhkMMMkkhkMMMhkMhMMhMMhkhkMMkMMhkhMMhkMMMkMhMMkhMMhMMkkkkhhMMMhMMhkMMMhkMMkMMkhkMMMhhkMMMM"

def l7MiddleMetadata : ComponentMetadata := {
  nodes := 263
  leaves := 132
  naturalLeaves := 11
  meanLeaves := 121
  splitK := 82
  splitChi := 49
  maxDepth := 10
  bytes := 263
  priorMeanReplacements := 1
  finalNaturalReplacements := 1
  sha256 := "93fe355f570beed88cb378ffc62961c10c8c664539897e85506dc132d0da31db"
}

def l7UpperFiveThirtySecondsToQuarterPacked : String :=
  "hhhhhhkkNNkNNkMMkMMkkMMkMMkkhkhMMMkhMkMMhMMhhMMkhMMMkhMkMMhMMkkhkhkhMMMhMMhkMMMhkMMMhhkMMkMMhMMhkhkMMMhMMkMMkhhkMMMMhhMMM"

def l7UpperFiveThirtySecondsToQuarterMetadata : ComponentMetadata := {
  nodes := 121
  leaves := 61
  naturalLeaves := 4
  meanLeaves := 57
  splitK := 29
  splitChi := 31
  maxDepth := 9
  bytes := 121
  priorMeanReplacements := 2
  finalNaturalReplacements := 0
  sha256 := "20a0e41824558b167b36cc425ba9886f5a7574edf09ba79ff5945bb0e73de459"
}

def l7UpperQuarterToHalfPacked : String :=
  "hhhhhhkkkNNkNNkNNkkMMMkkMMMkkMMkMMkkkhMMhMMhkMMkMMkhkMMkMMhhMMkMMkkhkhMMhMMkMMhkMMMhkhMMhMMkMMkhkhMMhMMkMMhhkMMMM"

def l7UpperQuarterToHalfMetadata : ComponentMetadata := {
  nodes := 113
  leaves := 57
  naturalLeaves := 6
  meanLeaves := 51
  splitK := 32
  splitChi := 24
  maxDepth := 9
  bytes := 113
  priorMeanReplacements := 0
  finalNaturalReplacements := 0
  sha256 := "f21f34514f4b620af5a9978728b1a71956e7b0ee3394b759eee1f94071d1e637"
}

def l7UpperHalfToOnePacked : String :=
  "hhhhhhkkkNNkNNkkNNkNNkkMMMkkMMkMMkkkMMhMkMMkhMkMMhMkMMkkkhhMMkMMhhMMkMMhkhMMhMMkkMMhMMkhkhMMhMkMMkhkMMkMMhkMMkMMhhkMhMMkkMMhMkMMkhkMMkMMhkhMMhMMkhMMhMMkkhkhkMMMhkMMMkMMhhkkMMhMMkMMhkMMMhkhkhMMhkMMMkMMhkhkMMMhkMMMkMhMMkhkMMMhkMMMkhkhkMMMhMMkMMhhkMMkMMhMM"

def l7UpperHalfToOneMetadata : ComponentMetadata := {
  nodes := 253
  leaves := 127
  naturalLeaves := 8
  meanLeaves := 119
  splitK := 71
  splitChi := 55
  maxDepth := 10
  bytes := 253
  priorMeanReplacements := 3
  finalNaturalReplacements := 0
  sha256 := "bba9e26b9698d2719e4e97072019a91e9bb6b37939ac1efc42ac95b5323f66c4"
}

def l14LowerPacked : String :=
  "hhhhhhkkkkNNkNNkNNkkNNkNNkkMMMkkMMkMMkkhkMMkMMhMkMMkhMMhMMkkhkhMkMMhMMkkhMMMkMMhkhMMhMMkhMMMkhkhMMMkMMhhMMkMMkhkkhkMMMhhMMMhkMMkMMkhkMMMhMMhkhkMMMhMMkhMMhMMkhkhkMMMhMMkhMMMhhkMMkMMhMM"

def l14LowerMetadata : ComponentMetadata := {
  nodes := 183
  leaves := 92
  naturalLeaves := 10
  meanLeaves := 82
  splitK := 50
  splitChi := 41
  maxDepth := 10
  bytes := 183
  priorMeanReplacements := 1
  finalNaturalReplacements := 1
  sha256 := "163faf2314aa04923756f5940bbc4fc2d2417206d65748783aa4c02ca02ade9c"
}

def l14UpperPacked : String :=
  "hhhhhhkkkkNNkNNkkNNkNNkkkNNkNNkkNNkNNkkMMMkkMMkMMkkkhMMhMMhMMkhMMhMMkkhkhMMMkMMhkMMkMMhkkMMkMMkkMMMkhkhkMMkMMhkMMMkhkMMMhMMhkhMMhMMkhMMhMMkhkhkMMMhMMkhMMhMMhhkMMkMMhkMMM"

def l14UpperMetadata : ComponentMetadata := {
  nodes := 169
  leaves := 85
  naturalLeaves := 16
  meanLeaves := 69
  splitK := 51
  splitChi := 33
  maxDepth := 10
  bytes := 169
  priorMeanReplacements := 3
  finalNaturalReplacements := 0
  sha256 := "d08b3d6331f4191683be6663aec4eac8f80bd311d53fbab7a04d05cba8aa8d73"
}

def aggregateNodes : Nat := 1102
def aggregateLeaves : Nat := 554
def aggregatePriorMeanReplacements : Nat := 10
def aggregateFinalNaturalReplacements : Nat := 2

end CourtadeKumar.LRIdealFinalRefinedTopologyData
