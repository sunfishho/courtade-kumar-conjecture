import InformationTheory.CourtadeKumar.CanonicalCenteredGeometry
import InformationTheory.CourtadeKumar.CanonicalSingleRayGeometry
import InformationTheory.CourtadeKumar.RadialContactShape
import InformationTheory.CourtadeKumar.RadialEntropyRatio
import InformationTheory.CourtadeKumar.SingleRayContactOrdering

/-! Direct scalar selection of the centered and single-ray geometries. -/

open Filter Set
open scoped NNReal Topology

namespace CourtadeKumar

/-- Every genuine radial Euler contact defines an interior multiplier. -/
theorem radialEulerLogRatio_mem_Ioo_physical
    {rho r z : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹) :
    radialEulerLogRatio rho r z ∈ Ioo (0 : ℝ) 1 := by
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) :=
        mul_lt_mul_of_pos_right hz.2 (by linarith [hr.1])
      _ = 1 := inv_mul_cancel₀ (by linarith [hr.1] : 1 + r ≠ 0)
  obtain ⟨harg1, hargR, horder⟩ :=
    radialEulerLogArg_order_physical
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
      hr.1 hz.1 hupper
  have harg1' : radialEulerLogArg 1 r z ∈ Ioo (0 : ℝ) 1 :=
    ⟨harg1.1, harg1.2.trans (by linarith [hz.1])⟩
  have hargR' : radialEulerLogArg rho r z ∈ Ioo (0 : ℝ) 1 :=
    ⟨hargR.1, hargR.2.trans (by linarith [hz.1])⟩
  have hden : 0 < radialEulerLog 1 r z :=
    radialEulerLog_pos_of_arg harg1'
  have hnum : 0 < radialEulerLog rho r z :=
    radialEulerLog_pos_of_arg hargR'
  have hlogOrder : Real.log (radialEulerLogArg 1 r z) <
      Real.log (radialEulerLogArg rho r z) :=
    Real.log_lt_log harg1.1 horder
  have hnumden : radialEulerLog rho r z < radialEulerLog 1 r z := by
    unfold radialEulerLog
    nlinarith
  unfold radialEulerLogRatio
  exact ⟨div_pos hnum hden, (div_lt_one hden).2 hnumden⟩

/-- A centered entropy contact satisfying the phase shape condition produces
the canonical centered geometry record. -/
noncomputable def canonicalCenteredGeometry_of_entropyContact
    {alpha : ℝ≥0} {M d E0 s : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hd : 0 < d)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hshape : d / M ≤ s)
    (hentropy : E0 =
      2 * d / s * radialTriangleEntropy s (1 / 2))
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    CenteredEndpointGeometryData alpha M d E0 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let theta : ℝ := radialEulerLogRatio rho s (1 / 2)
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hhalfcap : (1 / 2 : ℝ) < (1 + s)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hs.1] : 0 < 1 + s)]
    nlinarith [hs.2]
  have htheta : theta ∈ Ioo (0 : ℝ) 1 :=
    radialEulerLogRatio_mem_Ioo_physical hrho hs
      ⟨by norm_num, hhalfcap⟩
  exact canonicalCenteredEndpointGeometryData
    halpha hM hd hs hshape htheta (by rfl) hentropy hthreshold

/-- An entropy-matched contact before the midpoint produces the canonical
single-ray geometry.  Its centered threshold is automatically behind the
observed ray. -/
noncomputable def canonicalSingleRayGeometry_of_entropyContact
    {alpha : ℝ≥0} {M d E0 r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2))
    (hmoment : d = M * r)
    (hentropy : E0 / M = radialEntropyRatio r z)
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    SingleRayGeometryData alpha M d E0 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hhalfcap : (1 / 2 : ℝ) < (1 + r)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
    nlinarith [hr.2]
  have hzphys : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hz.1, hz.2.trans hhalfcap⟩
  have hcontact : M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 := by
    have hE : E0 = M / z * radialTriangleEntropy r z := by
      calc
        E0 = M * (E0 / M) := by field_simp [hM.1.ne']
        _ = M * radialEntropyRatio r z := by rw [hentropy]
        _ = M / z * radialTriangleEntropy r z := by
          unfold radialEntropyRatio
          ring
    rw [← hE, hthreshold]
    rw [show M - d = M * (1 - r) by linarith [hmoment],
      show M + d = M * (1 + r) by linarith [hmoment]]
  have hMle : M ≤ z :=
    singleRay_mean_le_contact halpha hM hr hz hcontact
  have hMopen : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) :=
    ⟨hM.1, hMle.trans_lt hz.2⟩
  let theta : ℝ := radialEulerLogRatio rho r z
  have htheta : theta ∈ Ioo (0 : ℝ) 1 :=
    radialEulerLogRatio_mem_Ioo_physical hrho hr hzphys
  let hroot := existsUnique_centeredRadialShape hrho htheta
  let rstar : ℝ := Classical.choose hroot.exists
  have hrstarSpec : rstar ∈ Ioo (0 : ℝ) 1 ∧
      radialEulerLogRatio rho rstar (1 / 2) = theta :=
    Classical.choose_spec hroot.exists
  have hrstar := hrstarSpec.1
  have hcenter := hrstarSpec.2
  have hcanonical :
      canonicalRadialContactZ alpha theta halpha htheta r = z := by
    have hspec := canonicalRadialContactZ_spec halpha htheta hr.1
    exact (existsUnique_radialEulerLogRatio_eq
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
      htheta hr.1).unique ⟨hspec.1, hspec.2⟩ ⟨hzphys, rfl⟩
  have hrstarr : rstar < r := by
    by_contra hn
    have hle : r ≤ rstar := le_of_not_gt hn
    rcases hle.eq_or_lt with hEq | hlt
    · have hhalf := canonicalRadialContactZ_eq_half_of_centeredRoot
        halpha htheta hrstar hcenter
      rw [← hEq, hcanonical] at hhalf
      linarith [hz.2]
    · have hgt := canonicalRadialContactZ_gt_half_before_threshold
        halpha htheta hrstar hcenter hr hlt
      rw [hcanonical] at hgt
      linarith [hz.2]
  have hentropy' : E0 = M /
      canonicalRadialContactZ alpha theta halpha htheta r *
        radialTriangleEntropy r
          (canonicalRadialContactZ alpha theta halpha htheta r) := by
    rw [hcanonical]
    calc
      E0 = M * (E0 / M) := by field_simp [hM.1.ne']
      _ = M * radialEntropyRatio r z := by rw [hentropy]
      _ = M / z * radialTriangleEntropy r z := by
        unfold radialEntropyRatio
        ring
  exact canonicalSingleRayGeometryData
    halpha hMopen htheta hrstar hcenter ⟨hrstarr, hr.2⟩ hmoment hentropy' hthreshold

/-- The centered entropy root itself decides the geometric phase.  If the
observed moment ray lies before it, use the centered chord.  Otherwise the
entropy level selects a unique pre-midpoint single-ray contact. -/
theorem canonicalTwoPhaseGeometry_of_centeredEntropyContact
    {alpha : ℝ≥0} {M d E0 s r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hd : 0 < d)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hmoment : d = M * r)
    (hentropy : E0 =
      2 * d / s * radialTriangleEntropy s (1 / 2))
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    Nonempty (SingleRayGeometryData alpha M d E0) ∨
      Nonempty (CenteredEndpointGeometryData alpha M d E0) := by
  have hdr : d / M = r := by
    rw [hmoment]
    field_simp [hM.1.ne']
  by_cases hrs : r ≤ s
  · exact Or.inr ⟨canonicalCenteredGeometry_of_entropyContact
      halpha hM hd hs (hdr.trans_le hrs) hentropy hthreshold⟩
  · have hsr : s < r := lt_of_not_ge hrs
    have hanti : centeredEntropyRatio r < centeredEntropyRatio s :=
      strictAntiOn_centeredEntropyRatio hs hr hsr
    have hlevel : E0 / M = 2 * r * centeredEntropyRatio s := by
      rw [hentropy, hmoment, centeredEntropyRatio_eq_radial]
      field_simp [hM.1.ne', hs.1.ne']
    have habove : radialEntropyRatio r (1 / 2) < E0 / M := by
      rw [radialEntropyRatio_half hr.1.ne', hlevel]
      exact mul_lt_mul_of_pos_left hanti (mul_pos (by norm_num) hr.1)
    obtain ⟨z, hz, hzeq⟩ :=
      (existsUnique_radialEntropyRatio_eq_before_half hr habove).exists
    exact Or.inl ⟨canonicalSingleRayGeometry_of_entropyContact
      halpha hM hr hz hmoment hzeq.symm hthreshold⟩

/-- Complete interior geometric classification from a positive target
entropy level.  Both scalar contacts are constructed internally. -/
theorem canonicalInteriorTwoPhaseGeometry
    {alpha : ℝ≥0} {M d E0 : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hd : 0 < d)
    (hdM : d < M)
    (hE0 : 0 < E0)
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    Nonempty (SingleRayGeometryData alpha M d E0) ∨
      Nonempty (CenteredEndpointGeometryData alpha M d E0) := by
  let t : ℝ := E0 / (2 * d)
  have ht : 0 < t := div_pos hE0 (mul_pos (by norm_num) hd)
  obtain ⟨s, hs, hseq⟩ :=
    (existsUnique_centeredEntropyRatio_eq ht).exists
  let r : ℝ := d / M
  have hr : r ∈ Ioo (0 : ℝ) 1 := by
    dsimp [r]
    exact ⟨div_pos hd hM.1, (div_lt_one hM.1).2 hdM⟩
  have hmoment : d = M * r := by
    dsimp [r]
    field_simp [hM.1.ne']
  have hentropy : E0 =
      2 * d / s * radialTriangleEntropy s (1 / 2) := by
    rw [centeredEntropyRatio_eq_radial] at hseq
    dsimp [t] at hseq
    calc
      E0 = 2 * d * (E0 / (2 * d)) := by field_simp [hd.ne']
      _ = 2 * d * (radialTriangleEntropy s (1 / 2) / s) := by rw [← hseq]
      _ = 2 * d / s * radialTriangleEntropy s (1 / 2) := by ring
  exact canonicalTwoPhaseGeometry_of_centeredEntropyContact
    halpha hM hd hs hr hmoment hentropy hthreshold

end CourtadeKumar
