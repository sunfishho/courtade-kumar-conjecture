import InformationTheory.CourtadeKumar.ChannelCap
import InformationTheory.CourtadeKumar.BellmanInduction

/-! From the Bellman envelope to the channel-capacity bound. -/

open Set
open scoped ENNReal NNReal

namespace CourtadeKumar

/-- The entropy deficit dominates its quadratic term on the full bias
interval. -/
theorem half_sq_le_topPhi {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    x ^ 2 / 2 ≤ topPhi x := by
  have hnonneg : ∀ {y : ℝ}, y ∈ Icc (0 : ℝ) 1 → y ^ 2 / 2 ≤ topPhi y := by
    intro y hy
    let f : ℝ → ℝ := fun z ↦ topPhi z - z ^ 2 / 2
    have hmono : MonotoneOn f (Icc (0 : ℝ) 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      · exact (continuous_topPhi.sub ((continuous_id.pow 2).div_const 2)).continuousOn
      · intro z hz
        rw [interior_Icc] at hz
        have hz' : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
        have hsq : HasDerivAt (fun w : ℝ ↦ w ^ 2 / 2) z z := by
          convert ((hasDerivAt_id z).mul (hasDerivAt_id z)).div_const 2 using 1 <;>
            simp [id_eq] <;> ring
        exact ((hasDerivAt_topPhi hz').sub hsq).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hz' : z ∈ Ioo (0 : ℝ) 1 := hz
        have hderiv : deriv f z = Real.artanh z - z := by
          have hz'' : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
          have hsq : HasDerivAt (fun w : ℝ ↦ w ^ 2 / 2) z z := by
            convert ((hasDerivAt_id z).mul (hasDerivAt_id z)).div_const 2 using 1 <;>
              simp [id_eq] <;> ring
          exact ((hasDerivAt_topPhi hz'').sub hsq).deriv
        exact sub_nonneg.mpr (self_lt_artanh hz').le
    have h0y := hmono (show (0 : ℝ) ∈ Icc 0 1 by simp) hy hy.1
    simpa [f] using h0y
  by_cases hx0 : 0 ≤ x
  · exact hnonneg ⟨hx0, hx.2⟩
  · have hneg : -x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
    have h := hnonneg hneg
    simpa using h

/-- The equal-multiplier coefficient is at most half the squared channel
correlation. -/
theorem topEll_le_half_sq {rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) :
    topEll rho ≤ rho ^ 2 / 2 := by
  have hphi := half_sq_le_topPhi
    (show rho ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hrho.1], hrho.2⟩)
  have hlog : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1 <;>
      norm_num
  have hscaled := mul_le_mul_of_nonneg_left hlog (sq_nonneg rho)
  unfold topEll topR
  linarith

/-- In natural units, the entropy gap above the Bellman envelope is at
most the BSC capacity. -/
theorem topJ_sub_topEnvelope_le_capacity
    {rho x : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    topJ x - topEnvelope rho x ≤ topPhi rho := by
  have hphi := half_sq_le_topPhi hx
  have hell := topEll_le_half_sq hrho
  have hphiScaled := mul_le_mul_of_nonneg_left hphi (sq_nonneg rho)
  have hellScaled := mul_le_mul_of_nonneg_right hell (sq_nonneg x)
  have hid : topPhi rho - (topJ x - topEnvelope rho x) =
      rho ^ 2 * topPhi x - topEll rho * x ^ 2 := by
    unfold topEnvelope topJ topS topR topEll
    unfold topR
    ring
  rw [← sub_nonneg, hid]
  nlinarith [hphiScaled, hellScaled]

lemma topPhi_channelRho_unitConversion (alpha : ℝ) :
    topPhi (channelRho alpha) =
      Real.log 2 * (1 - binaryEntropyBits alpha) := by
  have h : topJ (channelRho alpha) =
      Real.log 2 * binaryEntropyBits alpha := by
    simpa [channelRho] using topJ_unitConversion alpha
  unfold topJ at h
  linarith

/-- Bit-valued form of the elementary envelope-to-capacity estimate. -/
theorem binaryEntropy_sub_bellmanEnvelope_le_capacity
    {alpha p : ℝ} (halpha : alpha ∈ Icc (0 : ℝ) (1 / 2 : ℝ))
    (hp : p ∈ Icc (0 : ℝ) 1) :
    binaryEntropyBits p - bellmanEnvelope alpha p ≤
      1 - binaryEntropyBits alpha := by
  have hrho : channelRho alpha ∈ Icc (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hx : 1 - 2 * p ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hp.1, hp.2]
  have h := topJ_sub_topEnvelope_le_capacity hrho hx
  rw [topJ_unitConversion p, topEnvelope_unitConversion,
    topPhi_channelRho_unitConversion] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Once the scalar Bellman step is supplied, the complete
measure-theoretic Courtade--Kumar bound follows. -/
theorem bscMutualInformation_le_capacity_of_step
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2)
    (hBellman : BooleanBellmanStep alpha)
    (n : ℕ) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one halpha) b).toMeasure
      ≤ ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) := by
  let ha1 : alpha ≤ 1 := crossover_le_one halpha
  have hentropy :=
    bscAveragePosteriorBinaryEntropy_ge_bellmanEnvelope_of_step
      alpha ha1 hBellman n b
  let p : ℝ := bscPriorBias n b
  have hp : p ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact ENNReal.toReal_nonneg
    · exact (ENNReal.toReal_le_toReal
        (((uniformInputPMF n).map b).apply_ne_top true) ENNReal.one_ne_top).2
        (((uniformInputPMF n).map b).coe_le_one true)
  have hcap := binaryEntropy_sub_bellmanEnvelope_le_capacity
    (show (alpha : ℝ) ∈ Icc (0 : ℝ) (1 / 2 : ℝ) from ⟨alpha.2, halpha⟩) hp
  have hreal :
      binaryEntropyBits p - bscAveragePosteriorBinaryEntropy n alpha ha1 b ≤
        1 - binaryEntropyBits (alpha : ℝ) := by
    dsimp [p] at hentropy ⊢
    linarith
  rw [bscMutualInformation_eq_scalarEntropyDefect]
  exact ENNReal.ofReal_le_ofReal hreal

end CourtadeKumar
