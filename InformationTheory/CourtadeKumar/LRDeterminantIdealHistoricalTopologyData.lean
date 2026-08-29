/-!
# Historical mean-value ideal topology data

Exact preorder streams exported from the audited fixed-point verifiers by
`AgentMeanValueIdealTopologyExporter.py`.  The alphabet is:

* `N`: natural zero-face leaf;
* `M`: centered mean-value leaf;
* `k`: binary midpoint split in `k`;
* `h`: binary midpoint split in `chi`.

The strings have no leading root marker and no trailing newline.  In
particular, the two `L0 = 14 * log 2` components remain separately rooted at
`[1,2]` and `[2,4]`; their theorem-level join is at `k = 2`, not the arithmetic
midpoint `5/2` of `[1,4]`.

This module contains inert data only.  The kernel-checked packed decoder and
leaf oracles remain responsible for accepting or rejecting every stream.
-/

namespace CourtadeKumar.LRIdealHistoricalTopologyData

/-- Audited metadata for one full-input preorder component. -/
structure ComponentMetadata where
  nodes : Nat
  leaves : Nat
  naturalLeaves : Nat
  meanLeaves : Nat
  splitK : Nat
  splitChi : Nat
  maxDepth : Nat
  bytes : Nat
  minimumAcceptedNumerator : Nat
  minimumAcceptedDenominatorPower : Nat
  sha256 : String

/-- Aggregate audited statistics for a separately rooted forest. -/
structure ForestMetadata where
  roots : Nat
  nodes : Nat
  leaves : Nat
  naturalLeaves : Nat
  meanLeaves : Nat
  splitK : Nat
  splitChi : Nat
  maxDepth : Nat
  minimumAcceptedNumerator : Nat
  minimumAcceptedDenominatorPower : Nat

/-! ## `L0 = 7 * log 2` low-`k` forest -/

/-- Historical global-`L` component on `k in [1/32,5/32]`, `chi in [0,1]`. -/
def l7MiddlePacked : String :=
  "hhhhhhkkkkNNkNNkNNkkNNkNNkkkMMkMMkMMkkkkMMMkMMkMMkkkkMMkMMkMMkkMMkMMkkkkkhMMhMMkhMMhMMkhMMhMMkkhMMMhMkMMkkhMkMMhkMMkMMkhhMMkMMhhMkMMkhMMhMkMMkkkkkhMMhMMhkMMMkhMMhMMkhkMMkMMhkMMMkkhkMMMhkMhMMhMMhkhkMMkMMhkhMMhMMkMhMMkhMMhMMkkkkhhMMMhMMhkMMMhkMMkMMkhkMMMhhkMMMM"

def l7MiddleMetadata : ComponentMetadata := {
  nodes := 259
  leaves := 130
  naturalLeaves := 10
  meanLeaves := 120
  splitK := 80
  splitChi := 49
  maxDepth := 10
  bytes := 259
  minimumAcceptedNumerator := 481803854461010443320924230346906229
  minimumAcceptedDenominatorPower := 132
  sha256 := "bbce79e77604b88692b1eeb9b6a90a78143266ef9254f2f7672d5cd614f821a7"
}

/-- Historical monotone-`L` component on `k in [5/32,1/4]`, `chi in [0,1]`. -/
def l7UpperFiveThirtySecondsToQuarterPacked : String :=
  "hhhhhhkkNNkNNkMMkMMkkMMMkkhkhMMMkhMkMMhMMhhMMkhMMMkhMkMMhMMkkhkhkhMMMhMMhkMMMhkMMMhhkMMkMMhMMhkhMMhMMkMMkhhkMMMMhhMMM"

def l7UpperFiveThirtySecondsToQuarterMetadata : ComponentMetadata := {
  nodes := 117
  leaves := 59
  naturalLeaves := 4
  meanLeaves := 55
  splitK := 27
  splitChi := 31
  maxDepth := 9
  bytes := 117
  minimumAcceptedNumerator := 218374426433392617335629898558890314
  minimumAcceptedDenominatorPower := 132
  sha256 := "a0f64ce27fb3f089151e6371d2b7fb2fbc64a7294deee0f7c4d49350d7fd8fda"
}

/-- Historical monotone-`L` component on `k in [1/4,1/2]`, `chi in [0,1]`. -/
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
  minimumAcceptedNumerator := 8753322384624460137962015333027728515
  minimumAcceptedDenominatorPower := 132
  sha256 := "f21f34514f4b620af5a9978728b1a71956e7b0ee3394b759eee1f94071d1e637"
}

/-- Historical monotone-`L` component on `k in [1/2,1]`, `chi in [0,1]`. -/
def l7UpperHalfToOnePacked : String :=
  "hhhhhhkkkNNkNNkkNNkNNkkMMMkkMMkMMkkkMMhMkMMkhMkMMhMkMMkkkhhMMkMMhhMMkMMhkhMMhMMkkMMhMMkhkhMMhMkMMkhkMMkMMhkMMkMMhhkMhMMkkMMhMkMMkhkMMkMMhkhMMhMMkMhMMkkhkhkMMMhkMMMkMMhhkkMMhMMkMMhkMMMhkhkhMMhkMMMkMMhkhkMMMhkMMMkMMkhkMMMhMMkhkhkMMMhMMkMMhhkMMkMMhMM"

def l7UpperHalfToOneMetadata : ComponentMetadata := {
  nodes := 247
  leaves := 124
  naturalLeaves := 8
  meanLeaves := 116
  splitK := 70
  splitChi := 53
  maxDepth := 10
  bytes := 247
  minimumAcceptedNumerator := 48802738503892749841851230557891704
  minimumAcceptedDenominatorPower := 132
  sha256 := "601ad120a236df9b6b24b64a7f8fb07a3de248517deea8405e9dea01d2145fae"
}

def l7ForestMetadata : ForestMetadata := {
  roots := 4
  nodes := 736
  leaves := 370
  naturalLeaves := 28
  meanLeaves := 342
  splitK := 209
  splitChi := 157
  maxDepth := 10
  minimumAcceptedNumerator := 48802738503892749841851230557891704
  minimumAcceptedDenominatorPower := 132
}

/-! ## `L0 = 14 * log 2` restricted forest -/

/-- Historical restricted component on `k in [1,2]`, `chi in [0,1]`. -/
def l14LowerPacked : String :=
  "hhhhhhkkkkNNNkNNkkNNkNNkkMMMkkMMkMMkkhkMMkMMhMkMMkhMMhMMkkhkhMkMMhMMkkhMMMkMMhkhMMhMMkhMMMkhkhMMMkMMhhMMkMMkhkkhkMMMhhMMMhkMMkMMkhkMMMhMMhkhkMMMhMMkhMMhMMkhkhkMMMhMMkMMhhkMMkMMhMM"

def l14LowerMetadata : ComponentMetadata := {
  nodes := 179
  leaves := 90
  naturalLeaves := 9
  meanLeaves := 81
  splitK := 49
  splitChi := 40
  maxDepth := 10
  bytes := 179
  minimumAcceptedNumerator := 36328667091307581281806663650599973471
  minimumAcceptedDenominatorPower := 132
  sha256 := "4bd04f0091232e662360cf9ffb3a0173c69a9e9765a13e99ed06afd44608c70c"
}

/-- Historical restricted component on `k in [2,4]`, `chi in [0,1]`. -/
def l14UpperPacked : String :=
  "hhhhhhkkkkNNkNNkkNNkNNkkkNNkNNkkNNkNNkkMMMkkMMkMMkkkhMMhMMhMMkhMMhMMkkhkhMMMkMMhkMMkMMhkkMMMkMMkhkhkMMkMMhkMMMkhMMhMMhkhMMhMMkhMMhMMkhkhkMMMhMMkhMMhMMhhkMMkMMhkMMM"

def l14UpperMetadata : ComponentMetadata := {
  nodes := 163
  leaves := 82
  naturalLeaves := 16
  meanLeaves := 66
  splitK := 48
  splitChi := 33
  maxDepth := 10
  bytes := 163
  minimumAcceptedNumerator := 13018621285071233161345868642234756831
  minimumAcceptedDenominatorPower := 132
  sha256 := "7f781c80cd4d0ab033dd0e0c599e55febeb70d801aa53202bddfcfb0d22ed3d8"
}

def l14ForestMetadata : ForestMetadata := {
  roots := 2
  nodes := 342
  leaves := 172
  naturalLeaves := 25
  meanLeaves := 147
  splitK := 97
  splitChi := 73
  maxDepth := 10
  minimumAcceptedNumerator := 13018621285071233161345868642234756831
  minimumAcceptedDenominatorPower := 132
}

end CourtadeKumar.LRIdealHistoricalTopologyData
