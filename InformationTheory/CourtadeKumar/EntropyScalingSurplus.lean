import InformationTheory.CourtadeKumar.SingleRayChannelShape

/-! Convexity of the entropy surplus created by scaling a probability. -/

open Set

namespace CourtadeKumar

noncomputable def entropyScalingSurplusNat (c p : ℝ) : ℝ :=
  Real.binEntropy (c * p) - c * Real.binEntropy p

noncomputable def entropyScalingSurplusNatDeriv (c p : ℝ) : ℝ :=
  c * (Real.log (1 - c * p) - Real.log (c * p)) -
    c * (Real.log (1 - p) - Real.log p)

noncomputable def entropyScalingSurplusNatDeriv2 (c p : ℝ) : ℝ :=
  c * (1 - c) / ((1 - p) * (1 - c * p))

theorem hasDerivAt_entropyScalingSurplusNat
    {c p : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (entropyScalingSurplusNat c)
      (entropyScalingSurplusNatDeriv c p) p := by
  have hcp : c * p ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hc.1 hp.1
    · calc
        c * p < 1 * p := mul_lt_mul_of_pos_right hc.2 hp.1
        _ < 1 := by simpa using hp.2
  have hlinear : HasDerivAt (fun x : ℝ ↦ c * x) c p := by
    simpa [id_eq] using (hasDerivAt_id p).const_mul c
  have hscaled := (Real.hasDerivAt_binEntropy hcp.1.ne' hcp.2.ne).comp p hlinear
  have hbase := (Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne).const_mul c
  unfold entropyScalingSurplusNat entropyScalingSurplusNatDeriv
  convert hscaled.sub hbase using 1
  ring

theorem hasDerivAt_entropyScalingSurplusNatDeriv
    {c p : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (entropyScalingSurplusNatDeriv c)
      (entropyScalingSurplusNatDeriv2 c p) p := by
  have hcp : c * p ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hc.1 hp.1
    · calc
        c * p < 1 * p := mul_lt_mul_of_pos_right hc.2 hp.1
        _ < 1 := by simpa using hp.2
  have hpNe : p ≠ 0 := hp.1.ne'
  have hcpNe : c * p ≠ 0 := hcp.1.ne'
  have hOnePNe : 1 - p ≠ 0 := by linarith [hp.2]
  have hOneCPNe : 1 - c * p ≠ 0 := by linarith [hcp.2]
  have hOneP : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
    simpa [id_eq] using (hasDerivAt_const p 1).sub (hasDerivAt_id p)
  have hCP : HasDerivAt (fun x : ℝ ↦ c * x) c p := by
    simpa [id_eq] using (hasDerivAt_id p).const_mul c
  have hOneCP : HasDerivAt (fun x : ℝ ↦ 1 - c * x) (-c) p := by
    convert (hasDerivAt_const p 1).sub hCP using 1 <;> simp
  have hleft := ((Real.hasDerivAt_log hOneCPNe).comp p hOneCP).sub
    ((Real.hasDerivAt_log hcpNe).comp p hCP) |>.const_mul c
  have hright := ((Real.hasDerivAt_log hOnePNe).comp p hOneP).sub
    (Real.hasDerivAt_log hpNe) |>.const_mul c
  unfold entropyScalingSurplusNatDeriv entropyScalingSurplusNatDeriv2
  convert hleft.sub hright using 1
  field_simp [hpNe, hOnePNe, hOneCPNe]
  ring

theorem entropyScalingSurplusNatDeriv2_nonneg
    {c p : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ entropyScalingSurplusNatDeriv2 c p := by
  unfold entropyScalingSurplusNatDeriv2
  exact div_nonneg
    (mul_nonneg hc.1.le (sub_nonneg.2 hc.2.le))
    (mul_nonneg (sub_nonneg.2 hp.2.le)
      (sub_nonneg.2 (by
        have hcp : c * p < 1 := by
          calc
            c * p < 1 * p := mul_lt_mul_of_pos_right hc.2 hp.1
            _ < 1 := by simpa using hp.2
        linarith)))

/-- For a fixed scaling factor in `(0,1)`, entropy's scaling surplus is
convex on the probability interval. -/
theorem entropyScalingSurplusNat_convexOn
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (entropyScalingSurplusNat c) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
  · unfold entropyScalingSurplusNat
    fun_prop
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_entropyScalingSurplusNat hc hp).hasDerivWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_entropyScalingSurplusNatDeriv hc hp).hasDerivWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact entropyScalingSurplusNatDeriv2_nonneg hc hp

/-- A symmetric pair has no larger scaling surplus after its half-width is
contracted. -/
theorem entropyScalingSurplusNat_pair_contraction
    {c rho r z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Icc (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Icc (0 : ℝ) 1) :
    (entropyScalingSurplusNat c ((1 - rho * r) * z) +
        entropyScalingSurplusNat c ((1 + rho * r) * z)) / 2 ≤
      (entropyScalingSurplusNat c ((1 - r) * z) +
        entropyScalingSurplusNat c ((1 + r) * z)) / 2 := by
  let a : ℝ := (1 - r) * z
  let b : ℝ := (1 + r) * z
  let u : ℝ := (1 + rho) / 2
  let v : ℝ := (1 - rho) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith [hrho.1]
  have hv : 0 ≤ v := by dsimp [v]; linarith [hrho.2]
  have huv : u + v = 1 := by dsimp [u, v]; ring
  have hconvex := entropyScalingSurplusNat_convexOn hc
  have hleft := hconvex.2 hminus hplus hu hv huv
  have hright := hconvex.2 hminus hplus hv hu (by linarith [huv])
  simp only [smul_eq_mul] at hleft hright
  have hargLeft : u * a + v * b = (1 - rho * r) * z := by
    dsimp [u, v, a, b]
    ring
  have hargRight : v * a + u * b = (1 + rho * r) * z := by
    dsimp [u, v, a, b]
    ring
  rw [hargLeft] at hleft
  rw [hargRight] at hright
  have hsum := add_le_add hleft hright
  calc
    (entropyScalingSurplusNat c ((1 - rho * r) * z) +
        entropyScalingSurplusNat c ((1 + rho * r) * z)) / 2 ≤
      ((u * entropyScalingSurplusNat c ((1 - r) * z) +
          v * entropyScalingSurplusNat c ((1 + r) * z)) +
        (v * entropyScalingSurplusNat c ((1 - r) * z) +
          u * entropyScalingSurplusNat c ((1 + r) * z))) / 2 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = (entropyScalingSurplusNat c ((1 - r) * z) +
        entropyScalingSurplusNat c ((1 + r) * z)) / 2 := by
      rw [show
        (u * entropyScalingSurplusNat c ((1 - r) * z) +
            v * entropyScalingSurplusNat c ((1 + r) * z)) +
          (v * entropyScalingSurplusNat c ((1 - r) * z) +
            u * entropyScalingSurplusNat c ((1 + r) * z)) =
          (u + v) * entropyScalingSurplusNat c ((1 - r) * z) +
            (u + v) * entropyScalingSurplusNat c ((1 + r) * z) by ring,
        huv]
      ring

/-- Equivalently, the radial entropy scaling deficit decreases when the
ray is contracted. -/
theorem radialNatEntropy_scalingDeficit_contraction
    {c rho r z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Icc (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Icc (0 : ℝ) 1) :
    radialNatEntropy rho r (c * z) - c * radialNatEntropy rho r z ≤
      radialNatEntropy 1 r (c * z) - c * radialNatEntropy 1 r z := by
  have h := entropyScalingSurplusNat_pair_contraction hc hrho hminus hplus
  unfold entropyScalingSurplusNat at h
  unfold radialNatEntropy
  convert h using 1 <;> ring

end CourtadeKumar
