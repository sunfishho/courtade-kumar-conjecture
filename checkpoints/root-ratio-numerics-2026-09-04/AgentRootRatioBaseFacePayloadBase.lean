import AgentRootRatioBaseFacePilotData
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-! One finite payload receipt for the actual depth-eight base-face pilot.
The ordinary Lean kernel must reduce this closed Boolean to true. -/

namespace CourtadeKumar.RootRatioBaseFacePayloadReceipts
open CourtadeKumar.RootRatioBaseFaceGroupedPilot

#kernel_checked_bool baseChecked ((pilotPayload 8).payloadBaseCheck (pilotBox 8))

#print axioms CourtadeKumar.RootRatioBaseFacePayloadReceipts.baseChecked

end CourtadeKumar.RootRatioBaseFacePayloadReceipts
