import InformationTheory.CourtadeKumar.SingleRayContactOrdering

/-! Monotonicity of radial channel entropy with respect to ray shape. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Contracting a radial shape toward its mean increases the average
channel-output entropy. -/
theorem radialTriangleChannelEntropy_one_le
    {alpha : ℝ≥0} {r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) (1 / 2 : ℝ)) :
    radialTriangleChannelEntropy alpha 1 z ≤
      radialTriangleChannelEntropy alpha r z := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let a : ℝ := (1 - rho) * z
  let b : ℝ := (1 + rho) * z
  let u : ℝ := (1 + r) / 2
  let v : ℝ := (1 - r) / 2
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    dsimp [a]
    constructor
    · exact mul_nonneg (by linarith [hrho.2]) hz.1
    · calc
        (1 - rho) * z ≤ 1 * z :=
          mul_le_mul_of_nonneg_right (by linarith [hrho.1]) hz.1
        _ ≤ 1 := by linarith [hz.2]
  have hb : b ∈ Icc (0 : ℝ) 1 := by
    dsimp [b]
    constructor
    · exact mul_nonneg (by linarith [hrho.1]) hz.1
    · calc
        (1 + rho) * z ≤ 2 * z :=
          mul_le_mul_of_nonneg_right (by linarith [hrho.2]) hz.1
        _ ≤ 1 := by linarith [hz.2]
  have hu : 0 ≤ u := by dsimp [u]; linarith [hr.1]
  have hv : 0 ≤ v := by dsimp [v]; linarith [hr.2]
  have huv : u + v = 1 := by dsimp [u, v]; ring
  have hleft := binaryEntropyBits_concaveOn.2 ha hb hu hv huv
  have hright := binaryEntropyBits_concaveOn.2 ha hb hv hu (by linarith [huv])
  simp only [smul_eq_mul] at hleft hright
  have hargLeft : u * a + v * b = (1 - rho * r) * z := by
    dsimp [u, v, a, b]
    ring
  have hargRight : v * a + u * b = (1 + rho * r) * z := by
    dsimp [u, v, a, b]
    ring
  rw [hargLeft] at hleft
  rw [hargRight] at hright
  unfold radialTriangleChannelEntropy
  simp only [mul_one]
  dsimp [rho, a, b, u, v] at hleft hright
  nlinarith

/-- The one-ray lower bound therefore extends to every contracted radial
shape. -/
theorem bellmanEnvelope_le_radialChannelEntropy
    {alpha : ℝ≥0} {r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) (1 / 2 : ℝ)) :
    bellmanEnvelope (alpha : ℝ) z ≤
      radialTriangleChannelEntropy alpha r z :=
  (bellmanEnvelope_le_oneRayChannelEntropy halpha hz).trans
    (radialTriangleChannelEntropy_one_le halpha hr hz)

end CourtadeKumar
