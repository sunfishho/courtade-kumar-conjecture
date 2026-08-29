import InformationTheory.CourtadeKumar.PerspectiveFullWidth

/-!
# The singular full-width LR endpoint from open rays

This module formalizes the continuity closure implicit in Chapter 12 of the
audited assembly.  For fixed full-width data, let the shape `r` approach `1`
from below.  The prescribed Bellman entropy level has a unique pre-midpoint
radial contact `z(r)` for all `r` sufficiently close to `1`.  Strict decrease
of entropy per unit mass forces `z(r) → z(1)`.  The open-ray scalar theorem
may then be passed to the limit.

No numerical decision procedure is used.  The only noncomputable operation
is `Classical.choose` applied to the already-proved unique-contact theorem.
-/

open Filter Set
open scoped NNReal Topology

namespace CourtadeKumar

/-- The prescribed entropy-per-mass level at shape `r`. -/
noncomputable def fullWidthApproxTarget
    (alpha : ℝ≥0) (M r : ℝ) : ℝ :=
  (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
      bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / (2 * M)

/-- A totalized choice of the unique pre-midpoint entropy contact.  Only its
eventual branch near `r = 1` is used below. -/
noncomputable def fullWidthApproxRoot
    (alpha : ℝ≥0) (M r : ℝ) : ℝ :=
  if h : r ∈ Ioo (0 : ℝ) 1 ∧
      radialEntropyRatio r (1 / 2) < fullWidthApproxTarget alpha M r then
    Classical.choose
      (existsUnique_radialEntropyRatio_eq_before_half h.1 h.2).exists
  else
    1 / 4

lemma fullWidthApproxRoot_spec
    {alpha : ℝ≥0} {M r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hlevel : radialEntropyRatio r (1 / 2) <
      fullWidthApproxTarget alpha M r) :
    fullWidthApproxRoot alpha M r ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) ∧
      radialEntropyRatio r (fullWidthApproxRoot alpha M r) =
        fullWidthApproxTarget alpha M r := by
  rw [fullWidthApproxRoot, dif_pos ⟨hr, hlevel⟩]
  exact Classical.choose_spec
    (existsUnique_radialEntropyRatio_eq_before_half hr hlevel).exists

lemma radialEntropyRatio_oneRay_half_eq_zero :
    radialEntropyRatio 1 (1 / 2 : ℝ) = 0 := by
  rw [radialEntropyRatio_oneRay_eq]
  simp [binaryEntropyBits, Real.binEntropy]

lemma continuous_fullWidthApproxTarget
    (alpha : ℝ≥0) (M : ℝ) :
    Continuous (fullWidthApproxTarget alpha M) := by
  unfold fullWidthApproxTarget bellmanEnvelope binaryEntropyBits
  fun_prop

lemma continuous_radialEntropyRatio_in_shape_at
    (z : ℝ) :
    Continuous (fun r : ℝ ↦ radialEntropyRatio r z) := by
  unfold radialEntropyRatio radialTriangleEntropy binaryEntropyBits
  fun_prop

lemma continuous_radialChannelPerspective_at
    (alpha : ℝ≥0) (M r z : ℝ) (hz : z ≠ 0) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦
        M / p.2 * radialTriangleChannelEntropy alpha p.1 p.2)
      (r, z) := by
  have hz' : (r, z).2 ≠ 0 := by simpa using hz
  have hscale : ContinuousAt (fun p : ℝ × ℝ ↦ M / p.2) (r, z) :=
    continuousAt_const.div continuousAt_snd hz'
  have hchannel : ContinuousAt
      (fun p : ℝ × ℝ ↦ radialTriangleChannelEntropy alpha p.1 p.2)
      (r, z) := by
    unfold radialTriangleChannelEntropy binaryEntropyBits
    fun_prop
  exact hscale.mul hchannel

/-- The entropy contact selected on open rays converges to the prescribed
singular-ray contact. -/
theorem tendsto_fullWidthApproxRoot
    {alpha : ℝ≥0} {M z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hcontact : radialEntropyRatio 1 z =
      fullWidthApproxTarget alpha M 1)
    (htarget : 0 < fullWidthApproxTarget alpha M 1) :
    Tendsto (fullWidthApproxRoot alpha M)
      (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)) (nhds z) := by
  let l : Filter ℝ := nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)
  have htargetTendsto : Tendsto (fullWidthApproxTarget alpha M) l
      (nhds (fullWidthApproxTarget alpha M 1)) :=
    (continuous_fullWidthApproxTarget alpha M).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hhalfTendsto : Tendsto
      (fun r : ℝ ↦ radialEntropyRatio r (1 / 2 : ℝ)) l (nhds 0) := by
    have hfull : Tendsto
        (fun r : ℝ ↦ radialEntropyRatio r (1 / 2 : ℝ))
        (nhds (1 : ℝ))
        (nhds (radialEntropyRatio 1 (1 / 2 : ℝ))) :=
      (continuous_radialEntropyRatio_in_shape_at (1 / 2 : ℝ)).continuousAt
    have hwithin := hfull.mono_left
      (show nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1) ≤ nhds 1 from
        nhdsWithin_le_nhds)
    rw [radialEntropyRatio_oneRay_half_eq_zero] at hwithin
    exact hwithin
  have hlevelEventually : ∀ᶠ r in l,
      radialEntropyRatio r (1 / 2) < fullWidthApproxTarget alpha M r :=
    hhalfTendsto.eventually_lt htargetTendsto htarget
  have hrEventually : ∀ᶠ r in l, r ∈ Ioo (0 : ℝ) 1 :=
    self_mem_nhdsWithin
  have hspecEventually : ∀ᶠ r in l,
      fullWidthApproxRoot alpha M r ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) ∧
        radialEntropyRatio r (fullWidthApproxRoot alpha M r) =
          fullWidthApproxTarget alpha M r := by
    filter_upwards [hrEventually, hlevelEventually] with r hr hlevel
    exact fullWidthApproxRoot_spec hr hlevel
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    by_cases ha0 : a ≤ 0
    · exact hspecEventually.mono (fun _ hs ↦ ha0.trans_lt hs.1.1)
    · have haPos : 0 < a := lt_of_not_ge ha0
      have haHalf : a < 1 / 2 := ha.trans hz.2
      have haDomainOne : a ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := ⟨haPos, haHalf⟩
      have hstrictOne : radialEntropyRatio 1 z < radialEntropyRatio 1 a :=
        strictAntiOn_radialEntropyRatio_oneRay haDomainOne hz ha
      have haTendsto : Tendsto (fun r : ℝ ↦ radialEntropyRatio r a) l
          (nhds (radialEntropyRatio 1 a)) :=
        (continuous_radialEntropyRatio_in_shape_at a).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have horderEventually : ∀ᶠ r in l,
          fullWidthApproxTarget alpha M r < radialEntropyRatio r a := by
        apply htargetTendsto.eventually_lt haTendsto
        simpa [hcontact] using hstrictOne
      filter_upwards [hrEventually, hspecEventually, horderEventually] with r hr hs horder
      have hcap : (1 / 2 : ℝ) < (1 + r)⁻¹ := by
        rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
        nlinarith [hr.2]
      have haPhysical : a ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
        ⟨haPos, haHalf.trans hcap⟩
      have hrootPhysical : fullWidthApproxRoot alpha M r ∈
          Ioo (0 : ℝ) (1 + r)⁻¹ :=
        ⟨hs.1.1, hs.1.2.trans hcap⟩
      apply ((strictAntiOn_radialEntropyRatio hr).lt_iff_gt
        hrootPhysical haPhysical).mp
      simpa [hs.2] using horder
  · intro b hb
    by_cases hhalfB : (1 / 2 : ℝ) ≤ b
    · exact hspecEventually.mono (fun _ hs ↦ hs.1.2.trans_le hhalfB)
    · have hbHalf : b < 1 / 2 := lt_of_not_ge hhalfB
      have hbPos : 0 < b := hz.1.trans (hb)
      have hbDomainOne : b ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := ⟨hbPos, hbHalf⟩
      have hstrictOne : radialEntropyRatio 1 b < radialEntropyRatio 1 z :=
        strictAntiOn_radialEntropyRatio_oneRay hz hbDomainOne hb
      have hbTendsto : Tendsto (fun r : ℝ ↦ radialEntropyRatio r b) l
          (nhds (radialEntropyRatio 1 b)) :=
        (continuous_radialEntropyRatio_in_shape_at b).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have horderEventually : ∀ᶠ r in l,
          radialEntropyRatio r b < fullWidthApproxTarget alpha M r := by
        apply hbTendsto.eventually_lt htargetTendsto
        simpa [hcontact] using hstrictOne
      filter_upwards [hrEventually, hspecEventually, horderEventually] with r hr hs horder
      have hcap : (1 / 2 : ℝ) < (1 + r)⁻¹ := by
        rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
        nlinarith [hr.2]
      have hbPhysical : b ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
        ⟨hbPos, hbHalf.trans hcap⟩
      have hrootPhysical : fullWidthApproxRoot alpha M r ∈
          Ioo (0 : ℝ) (1 + r)⁻¹ :=
        ⟨hs.1.1, hs.1.2.trans hcap⟩
      apply ((strictAntiOn_radialEntropyRatio hr).lt_iff_gt
        hbPhysical hrootPhysical).mp
      simpa [hs.2] using horder

/-- The open single-ray scalar theorem already implies the singular
full-width specialization.  No new analytic inequality is needed at `r=1`;
only continuity and uniqueness of the entropy contact are used. -/
theorem fullWidthLR_of_singleRayScalarContact
    (alpha : ℝ≥0) (hscalar : SingleRayScalarContactTheorem alpha) :
    FullWidthLRTheorem alpha := by
  intro M E0 h
  have hMne : M ≠ 0 := h.mean_interior.1.ne'
  have hzne : h.z ≠ 0 := h.contact_before_half.1.ne'
  have h2M : 2 * M ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [h.mean_interior.1, h.mean_interior.2]
  have hcontactLevel : radialEntropyRatio 1 h.z =
      fullWidthApproxTarget alpha M 1 := by
    unfold radialEntropyRatio fullWidthApproxTarget
    rw [show M * (1 - (1 : ℝ)) = 0 by ring,
      show M * (1 + (1 : ℝ)) = 2 * M by ring,
      bellmanEnvelope_zero, zero_add]
    calc
      radialTriangleEntropy 1 h.z / h.z =
          (M / h.z * radialTriangleEntropy 1 h.z) / M := by
        field_simp [hMne, hzne]
      _ = E0 / M := by rw [← h.entropy_contact]
      _ = (bellmanEnvelope (alpha : ℝ) (2 * M) / 2) / M := by
        rw [h.threshold_eq]
      _ = bellmanEnvelope (alpha : ℝ) (2 * M) / (2 * M) := by
        field_simp [hMne]
  have htarget : 0 < fullWidthApproxTarget alpha M 1 := by
    unfold fullWidthApproxTarget
    rw [show M * (1 - (1 : ℝ)) = 0 by ring,
      show M * (1 + (1 : ℝ)) = 2 * M by ring,
      bellmanEnvelope_zero, zero_add]
    exact div_pos (bellmanEnvelope_pos_of_mem_Ioo h.alpha_interior h2M)
      (mul_pos (by norm_num) h.mean_interior.1)
  let l : Filter ℝ := nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)
  have hlNeBot : l.NeBot := by
    dsimp [l]
    exact right_nhdsWithin_Ioo_neBot (show (0 : ℝ) < 1 by norm_num)
  letI : l.NeBot := hlNeBot
  have hrTendsto : Tendsto (fun r : ℝ ↦ r) l (nhds 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hrootTendsto : Tendsto (fullWidthApproxRoot alpha M) l (nhds h.z) :=
    tendsto_fullWidthApproxRoot h.contact_before_half hcontactLevel htarget
  have hvalueTendsto : Tendsto
      (fun r : ℝ ↦ M / fullWidthApproxRoot alpha M r *
        radialTriangleChannelEntropy alpha r
          (fullWidthApproxRoot alpha M r)) l
      (nhds (M / h.z * radialTriangleChannelEntropy alpha 1 h.z)) := by
    exact (continuous_radialChannelPerspective_at alpha M 1 h.z hzne).tendsto.comp
      (hrTendsto.prodMk_nhds hrootTendsto)
  have hrEventually : ∀ᶠ r in l, r ∈ Ioo (0 : ℝ) 1 :=
    self_mem_nhdsWithin
  have htargetTendsto : Tendsto (fullWidthApproxTarget alpha M) l
      (nhds (fullWidthApproxTarget alpha M 1)) :=
    (continuous_fullWidthApproxTarget alpha M).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hhalfTendsto : Tendsto
      (fun r : ℝ ↦ radialEntropyRatio r (1 / 2 : ℝ)) l (nhds 0) := by
    have hfull : Tendsto
        (fun r : ℝ ↦ radialEntropyRatio r (1 / 2 : ℝ))
        (nhds (1 : ℝ))
        (nhds (radialEntropyRatio 1 (1 / 2 : ℝ))) :=
      (continuous_radialEntropyRatio_in_shape_at (1 / 2 : ℝ)).continuousAt
    have hwithin := hfull.mono_left
      (show nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1) ≤ nhds 1 from
        nhdsWithin_le_nhds)
    rw [radialEntropyRatio_oneRay_half_eq_zero] at hwithin
    exact hwithin
  have hlevelEventually : ∀ᶠ r in l,
      radialEntropyRatio r (1 / 2) < fullWidthApproxTarget alpha M r :=
    hhalfTendsto.eventually_lt htargetTendsto htarget
  have hineqEventually : ∀ᶠ r in l,
      bellmanEnvelope (alpha : ℝ) M ≤
        M / fullWidthApproxRoot alpha M r *
          radialTriangleChannelEntropy alpha r
            (fullWidthApproxRoot alpha M r) := by
    filter_upwards [hrEventually, hlevelEventually] with r hr hlevel
    have hspec := fullWidthApproxRoot_spec (alpha := alpha) (M := M) hr hlevel
    have hcontact : M / fullWidthApproxRoot alpha M r *
        radialTriangleEntropy r (fullWidthApproxRoot alpha M r) =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
          bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 := by
      have hspecEq := hspec.2
      unfold radialEntropyRatio fullWidthApproxTarget at hspecEq
      field_simp [hMne, hspec.1.1.ne'] at hspecEq ⊢
      linarith [hspecEq]
    exact hscalar h.alpha_interior M r (fullWidthApproxRoot alpha M r)
      h.mean_interior hr hspec.1 hcontact
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hvalueTendsto hineqEventually

end CourtadeKumar
