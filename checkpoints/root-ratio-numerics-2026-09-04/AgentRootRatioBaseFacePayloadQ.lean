import AgentRootRatioBaseFacePilotData
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-! One finite payload receipt for the actual depth-eight base-face pilot.
The ordinary Lean kernel must reduce this closed Boolean to true. -/

namespace CourtadeKumar.RootRatioBaseFacePayloadReceipts
open CourtadeKumar.RootRatioBaseFaceGroupedPilot

#kernel_checked_bool qChecked ((pilotPayload 8).payloadQCheck (pilotBox 8))

#print axioms CourtadeKumar.RootRatioBaseFacePayloadReceipts.qChecked

end CourtadeKumar.RootRatioBaseFacePayloadReceipts
