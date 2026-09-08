import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCheckerCore
namespace CourtadeKumar.LRCompactReducedCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def logTwoWitness : LRMidpointReducedCertificate.RoundedLog := ⟨⟨1, 1⟩, (1386294361 / 2000000000), (108304247 / 156250000)⟩
def logTwo : RationalEnclosure := ⟨logTwoWitness.lower,logTwoWitness.upper⟩
theorem logTwo_checked : logTwoWitness.check 2 = true := by decide +kernel
end CourtadeKumar.LRCompactReducedCertificate
