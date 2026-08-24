import InformationTheory.CourtadeKumar.TopEndpointIdentity

/-! Concavity of the corrected TOP reserve and its two-endpoint reduction. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

noncomputable def topPerspectiveCore (r c : ℝ) : ℝ :=
  (2 - c) * topPhi (c * r / (2 - c))

/-- The restriction of the perspective of `Phi` occurring in TOP is convex. -/
theorem topPerspectiveCore_convexOn
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (topPerspectiveCore r) := by
  constructor
  · exact convex_Icc 0 1
  · intro c₁ hc₁ c₂ hc₂ a b ha hb hab
    let C : ℝ := a * c₁ + b * c₂
    let w₁ : ℝ := 2 - c₁
    let w₂ : ℝ := 2 - c₂
    let W : ℝ := 2 - C
    let A : ℝ := a * w₁ / W
    let B : ℝ := b * w₂ / W
    let x₁ : ℝ := c₁ * r / w₁
    let x₂ : ℝ := c₂ * r / w₂
    have hw₁ : 0 < w₁ := by dsimp [w₁]; linarith [hc₁.2]
    have hw₂ : 0 < w₂ := by dsimp [w₂]; linarith [hc₂.2]
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact add_nonneg (mul_nonneg ha hc₁.1) (mul_nonneg hb hc₂.1)
    have hC1 : C ≤ 1 := by
      dsimp [C]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hc₁.2),
        mul_nonneg hb (sub_nonneg.mpr hc₂.2)]
    have hW : 0 < W := by dsimp [W]; linarith
    have hW_eq : W = a * w₁ + b * w₂ := by
      dsimp [W, C, w₁, w₂]
      nlinarith [hab]
    have hA : 0 ≤ A := by
      dsimp [A]
      exact div_nonneg (mul_nonneg ha hw₁.le) hW.le
    have hB : 0 ≤ B := by
      dsimp [B]
      exact div_nonneg (mul_nonneg hb hw₂.le) hW.le
    have hAB : A + B = 1 := by
      dsimp [A, B]
      calc
        a * w₁ / W + b * w₂ / W = (a * w₁ + b * w₂) / W := by ring
        _ = W / W := by rw [← hW_eq]
        _ = 1 := div_self hW.ne'
    have hx₁ : x₁ ∈ Icc (-1 : ℝ) 1 := by
      have hxnonneg : 0 ≤ x₁ := by
        dsimp [x₁]
        exact div_nonneg (mul_nonneg hc₁.1 hr0) hw₁.le
      constructor
      · linarith
      · dsimp [x₁]
        rw [div_le_iff₀ hw₁]
        have hprod : c₁ * r ≤ c₁ := mul_le_of_le_one_right hc₁.1 hr1
        linarith [hc₁.2]
    have hx₂ : x₂ ∈ Icc (-1 : ℝ) 1 := by
      have hxnonneg : 0 ≤ x₂ := by
        dsimp [x₂]
        exact div_nonneg (mul_nonneg hc₂.1 hr0) hw₂.le
      constructor
      · linarith
      · dsimp [x₂]
        rw [div_le_iff₀ hw₂]
        have hprod : c₂ * r ≤ c₂ := mul_le_of_le_one_right hc₂.1 hr1
        linarith [hc₂.2]
    have hxcombo : C * r / W = A * x₁ + B * x₂ := by
      dsimp [A, B, x₁, x₂]
      field_simp [hw₁.ne', hw₂.ne', hW.ne']
      ring
    have hphi := topPhi_convexOn.2 hx₁ hx₂ hA hB hAB
    simp only [smul_eq_mul] at hphi ⊢
    rw [← hxcombo] at hphi
    have hscaled := mul_le_mul_of_nonneg_left hphi hW.le
    dsimp [topPerspectiveCore]
    change W * topPhi (C * r / W) ≤
      a * (w₁ * topPhi (c₁ * r / w₁)) +
        b * (w₂ * topPhi (c₂ * r / w₂))
    calc
      W * topPhi (C * r / W) ≤
          W * (A * topPhi x₁ + B * topPhi x₂) := hscaled
      _ = a * (w₁ * topPhi (c₁ * r / w₁)) +
          b * (w₂ * topPhi (c₂ * r / w₂)) := by
            dsimp [A, B, x₁, x₂]
            field_simp [hW.ne']

/-- The perspective difference `S(c,r)` is concave in `c`. -/
theorem topPerspectiveTerm_concaveOn
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun c ↦ topPerspectiveTerm c r) := by
  have hcore := topPerspectiveCore_convexOn hr0 hr1
  constructor
  · exact convex_Icc 0 1
  · intro c₁ hc₁ c₂ hc₂ a b ha hb hab
    have h := hcore.2 hc₁ hc₂ ha hb hab
    simp only [smul_eq_mul] at h ⊢
    unfold topPerspectiveCore at h
    unfold topPerspectiveTerm
    nlinarith [h]

private lemma negQuadratic_concaveOn (k : ℝ) (hk : 0 ≤ k) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun c : ℝ ↦ -k * c ^ 2) := by
  constructor
  · exact convex_Icc 0 1
  · intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have hsq : 0 ≤ k * a * b * (x - y) ^ 2 := by positivity
    have hb' : b = 1 - a := by linarith
    subst b
    nlinarith

/-- For fixed `(rho,r)`, the corrected explicit TOP reserve is concave in
the weight `c`, conditional on the elementary coefficient signs. -/
theorem topReserve_concaveOn
    {rho r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun c ↦ topReserve rho c r) := by
  have hS := (topPerspectiveTerm_concaveOn hr0 hr1).smul hs
  have hlinear : ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun c : ℝ ↦ c * topEnergy rho r) := by
    constructor
    · exact convex_Icc 0 1
    · intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      ring_nf
      exact le_refl _
  have hquad := negQuadratic_concaveOn (topEll rho * r ^ 2) (by positivity)
  apply ((hS.add hlinear).add hquad).congr
  intro c hc
  simp only [Pi.add_apply, smul_eq_mul]
  unfold topReserve
  ring

/-- A concave function nonnegative at two endpoints is nonnegative between
them. -/
lemma concaveOn_nonneg_of_endpoints
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f)
    {a x b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) :
    0 ≤ f x := by
  by_cases hab : a = b
  · have hx : x = a := by linarith
    simpa [hx] using hfa
  have hablt : a < b := lt_of_le_of_ne (hax.trans hxb) hab
  let A : ℝ := (b - x) / (b - a)
  let B : ℝ := (x - a) / (b - a)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hablt.le)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hablt.le)
  have hAB : A + B = 1 := by
    dsimp [A, B]
    field_simp [sub_ne_zero.mpr hablt.ne']
    ring
  have hxcombo : A * a + B * b = x := by
    dsimp [A, B]
    field_simp [sub_ne_zero.mpr hablt.ne']
    ring
  have hconc := hf.2 ha hb hA hB hAB
  simp only [smul_eq_mul, hxcombo] at hconc
  exact (add_nonneg (mul_nonneg hA hfa) (mul_nonneg hB hfb)).trans hconc

/-- Concavity reduces corrected-reserve positivity to the balanced and
transition endpoint certificates. -/
theorem topReserve_nonneg_between
    {rho r cₜ c cᵦ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho)
    (hct : cₜ ∈ Icc (0 : ℝ) 1) (hcb : cᵦ ∈ Icc (0 : ℝ) 1)
    (hleft : cₜ ≤ c) (hright : c ≤ cᵦ)
    (htransition : 0 ≤ topReserve rho cₜ r)
    (hbalanced : 0 ≤ topReserve rho cᵦ r) :
    0 ≤ topReserve rho c r :=
  concaveOn_nonneg_of_endpoints (topReserve_concaveOn hr0 hr1 hs hell)
    hct hcb hleft hright htransition hbalanced

end CourtadeKumar
