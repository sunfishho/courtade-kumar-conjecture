import InformationTheory.CourtadeKumar.AnalyticExtension.CompactCheckerCore

/-! Compact serialization of untrusted certificate data.
The decoder needs no correctness assumption: its entire output is passed to
checkTree, whose soundness holds for every tree, including malformed decodings.
Packing avoids elaborating hundreds of thousands of rational record literals. -/
namespace CourtadeKumar.LRCompactReducedCertificate.Packed
open LRMidpointReducedCertificate (RoundedLog)
abbrev Decoder := StateM (List Int)

def readInt : Decoder Int := do
  match ← get with
  | [] => return 0
  | x::xs => set xs; return x

def readRat : Decoder ℚ := do
  let n ← readInt
  let d ← readInt
  return (n:ℚ)/(d:ℚ)

def readLog : Decoder RoundedLog := do
  let exponent ← readInt
  let mantissa ← readRat
  let lower ← readRat
  let upper ← readRat
  return ⟨⟨exponent,mantissa⟩,lower,upper⟩

def readEndpoint : Decoder EndpointLog := do
  let reciprocal ← readInt
  let witness ← readLog
  return ⟨decide (reciprocal ≠ 0),witness⟩

def readLogInterval : Decoder LogInterval := do
  let lower ← readEndpoint
  let upper ← readEndpoint
  return ⟨lower,upper⟩

def readB : Decoder BData := do
  let logV ← readLogInterval
  let logS ← readLogInterval
  return ⟨logV,logS⟩

def readLeaf : Decoder Leaf := do
  let logA ← readLog
  let logB ← readLog
  let logU ← readLog
  let logC ← readLog
  let wholeB ← readB
  let pointB ← readB
  return ⟨⟨logA,logB,logU,logC⟩,wholeB,pointB⟩

def readTree : Nat → Decoder Tree
  | 0 => return .discard ()
  | n+1 => do
    let tag ← readInt
    if tag == 0 then return .discard ()
    if tag == 1 then return .accept (← readLeaf)
    let cut ← readRat
    let lower ← readTree n
    let upper ← readTree n
    let axis := if tag == 2 then CertificateAxis.s else
      if tag == 3 then CertificateAxis.k else CertificateAxis.chi
    return .split axis cut lower upper

def decode (payload : String) : Tree :=
  let tokens := (payload.splitOn " ").map (fun s => s.toInt?.getD 0)
  ((readTree tokens.length).run tokens).1

end CourtadeKumar.LRCompactReducedCertificate.Packed
