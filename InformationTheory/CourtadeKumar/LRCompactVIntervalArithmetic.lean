import InformationTheory.CourtadeKumar.LRCompactVCertificateTarget

/-!
# Exact interval arithmetic for the compact `V` certificate

The structured certificate is only useful computationally if its positive
polynomial factors are enclosed without destroying their cancellations.
This file gives executable rational endpoint formulas for the channel score,
the shape monomial, and its complementary coefficient.  Their soundness
theorems use the analytic monotonicity proved in `LRCompactVSeries`.

The inherited certificate coordinates are interpreted as `s=R`, `k=v`, and
`chi=x=t²` throughout.
-/

open Set

namespace CourtadeKumar

/-- Closed unit-box conditions used by every compact interval leaf. -/
def LRCompactVBoxValid (box : CertificateBox) : Prop :=
  (0 : ℚ) ≤ box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi ≤ 1 ∧
  (0 : ℚ) ≤ box.kLo ∧ box.kLo ≤ box.kHi ∧ box.kHi ≤ 1 ∧
  (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧ box.chiHi ≤ 1

/-- Executable unit-box check. -/
def LRCompactVBoxValid.check (box : CertificateBox) : Bool :=
  decide (
    (0 : ℚ) ≤ box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi ≤ 1 ∧
    (0 : ℚ) ≤ box.kLo ∧ box.kLo ≤ box.kHi ∧ box.kHi ≤ 1 ∧
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧ box.chiHi ≤ 1)

theorem LRCompactVBoxValid.of_check {box : CertificateBox}
    (hcheck : LRCompactVBoxValid.check box = true) :
    LRCompactVBoxValid box := by
  simpa [LRCompactVBoxValid.check, LRCompactVBoxValid] using hcheck

/-- Exact rational counterpart of `lrCompactVScore`. -/
def lrCompactVScoreQ (R : ℚ) (n : ℕ) : ℚ :=
  1 - (n : ℚ) * R ^ (n - 1) + ((n : ℚ) - 1) * R ^ n

/-- Exact rational counterpart of `lrCompactVT`. -/
def lrCompactVTQ (v x : ℚ) (n : ℕ) : ℚ :=
  x ^ n * (1 + v ^ (2 * n - 1))

/-- Exact rational counterpart of `lrCompactVC`. -/
def lrCompactVCQ (v x : ℚ) (n : ℕ) : ℚ :=
  4 / (1 + v) - lrCompactVTQ v x n

@[simp] theorem cast_lrCompactVScoreQ (R : ℚ) (n : ℕ) :
    (lrCompactVScoreQ R n : ℝ) = lrCompactVScore R n := by
  simp only [lrCompactVScoreQ, lrCompactVScore]
  push_cast
  rfl

@[simp] theorem cast_lrCompactVTQ (v x : ℚ) (n : ℕ) :
    (lrCompactVTQ v x n : ℝ) = lrCompactVT v x n := by
  simp only [lrCompactVTQ, lrCompactVT]
  push_cast
  rfl

@[simp] theorem cast_lrCompactVCQ (v x : ℚ) (n : ℕ) :
    (lrCompactVCQ v x n : ℝ) = lrCompactVC v x n := by
  simp only [lrCompactVCQ, lrCompactVC]
  push_cast
  rw [cast_lrCompactVTQ]

/-- Tight endpoint enclosure for the score, which is decreasing in `R` on
the unit interval. -/
def lrCompactVScoreEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  ⟨lrCompactVScoreQ box.sHi n, lrCompactVScoreQ box.sLo n⟩

/-- Tight endpoint enclosure for `T_n`, increasing in both `v` and `x`. -/
def lrCompactVTEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  ⟨lrCompactVTQ box.kLo box.chiLo n,
    lrCompactVTQ box.kHi box.chiHi n⟩

/-- Tight endpoint enclosure for `c_n`, decreasing in both `v` and `x`. -/
def lrCompactVCEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  ⟨lrCompactVCQ box.kHi box.chiHi n,
    lrCompactVCQ box.kLo box.chiLo n⟩

theorem lrCompactVScoreEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint} {n : ℕ}
    (hn : 1 ≤ n) (hLo : (0 : ℚ) ≤ box.sLo)
    (hHi : box.sHi ≤ 1) (hpoint : box.Contains point) :
    (lrCompactVScoreEnclosure box n).Contains
      (lrCompactVScore point.s n) := by
  rcases hpoint with ⟨hsLo, hsHi, hkLo, hkHi, hxLo, hxHi⟩
  have hsLoUnit : (box.sLo : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hLo
    · exact hsLo.trans (hsHi.trans (by exact_mod_cast hHi))
  have hsHiUnit : (box.sHi : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (by exact_mod_cast hLo : (0 : ℝ) ≤ box.sLo) |>.trans
        (hsLo.trans hsHi)
    · exact_mod_cast hHi
  have hpUnit : point.s ∈ Icc (0 : ℝ) 1 := by
    exact ⟨hsLoUnit.1.trans hsLo, hsHi.trans hsHiUnit.2⟩
  have hanti := lrCompactVScore_antitoneOn_unit hn
  constructor
  · change (lrCompactVScoreQ box.sHi n : ℝ) ≤
      lrCompactVScore point.s n
    rw [cast_lrCompactVScoreQ]
    exact hanti hpUnit hsHiUnit hsHi
  · change lrCompactVScore point.s n ≤
      (lrCompactVScoreQ box.sLo n : ℝ)
    rw [cast_lrCompactVScoreQ]
    exact hanti hsLoUnit hpUnit hsLo

theorem lrCompactVTEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint} {n : ℕ}
    (hvLo : (0 : ℚ) ≤ box.kLo) (hxLo : (0 : ℚ) ≤ box.chiLo)
    (hpoint : box.Contains point) :
    (lrCompactVTEnclosure box n).Contains
      (lrCompactVT point.k point.chi n) := by
  rcases hpoint with ⟨hsLo, hsHi, hvLower, hvUpper, hxLower, hxUpper⟩
  have hvLoReal : (0 : ℝ) ≤ box.kLo := by exact_mod_cast hvLo
  have hxLoReal : (0 : ℝ) ≤ box.chiLo := by exact_mod_cast hxLo
  have hvPoint : 0 ≤ point.k := hvLoReal.trans hvLower
  have hxPoint : 0 ≤ point.chi := hxLoReal.trans hxLower
  constructor
  · change (lrCompactVTQ box.kLo box.chiLo n : ℝ) ≤
      lrCompactVT point.k point.chi n
    rw [cast_lrCompactVTQ]
    exact (lrCompactVT_mono_x hvLoReal hxLoReal hxLower n).trans
      (lrCompactVT_mono_v hvLoReal hvLower hxPoint n)
  · change lrCompactVT point.k point.chi n ≤
      (lrCompactVTQ box.kHi box.chiHi n : ℝ)
    rw [cast_lrCompactVTQ]
    exact (lrCompactVT_mono_v hvPoint hvUpper hxPoint n).trans
      (lrCompactVT_mono_x
        (hvPoint.trans hvUpper) hxPoint hxUpper n)

theorem lrCompactVCEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint} {n : ℕ}
    (hvLo : (0 : ℚ) ≤ box.kLo) (hxLo : (0 : ℚ) ≤ box.chiLo)
    (hpoint : box.Contains point) :
    (lrCompactVCEnclosure box n).Contains
      (lrCompactVC point.k point.chi n) := by
  rcases hpoint with ⟨hsLo, hsHi, hvLower, hvUpper, hxLower, hxUpper⟩
  have hvLoReal : (0 : ℝ) ≤ box.kLo := by exact_mod_cast hvLo
  have hxLoReal : (0 : ℝ) ≤ box.chiLo := by exact_mod_cast hxLo
  have hvPoint : 0 ≤ point.k := hvLoReal.trans hvLower
  have hxPoint : 0 ≤ point.chi := hxLoReal.trans hxLower
  constructor
  · change (lrCompactVCQ box.kHi box.chiHi n : ℝ) ≤
      lrCompactVC point.k point.chi n
    rw [cast_lrCompactVCQ]
    exact (lrCompactVC_antitone_x
      (hvPoint.trans hvUpper) hxPoint hxUpper n).trans
      (lrCompactVC_antitone_v hvPoint hvUpper hxPoint n)
  · change lrCompactVC point.k point.chi n ≤
      (lrCompactVCQ box.kLo box.chiLo n : ℝ)
    rw [cast_lrCompactVCQ]
    exact (lrCompactVC_antitone_v hvLoReal hvLower hxPoint n).trans
      (lrCompactVC_antitone_x hvLoReal hxLoReal hxLower n)

/-- Exact rational entropy-series coefficient. -/
def lrLowAQ (n : ℕ) : ℚ :=
  1 / (2 * (n : ℚ) * (2 * (n : ℚ) - 1))

@[simp] theorem cast_lrLowAQ (n : ℕ) :
    (lrLowAQ n : ℝ) = lrLowA n := by
  simp only [lrLowAQ, lrLowA]
  push_cast
  rfl

namespace RationalEnclosure

/-- Tight natural-power enclosure for a nonnegative input interval. -/
def powNonnegative (a : RationalEnclosure) (n : ℕ) : RationalEnclosure :=
  ⟨a.lower ^ n, a.upper ^ n⟩

theorem contains_powNonnegative
    {a : RationalEnclosure} {x : ℝ} (ha : (0 : ℚ) ≤ a.lower)
    (hx : a.Contains x) (n : ℕ) :
    (powNonnegative a n).Contains (x ^ n) := by
  have haReal : (0 : ℝ) ≤ a.lower := by exact_mod_cast ha
  have hxReal : 0 ≤ x := haReal.trans hx.1
  constructor
  · change (((a.lower ^ n : ℚ) : ℝ)) ≤ x ^ n
    norm_num only [Rat.cast_pow]
    gcongr
    exact hx.1
  · change x ^ n ≤ (((a.upper ^ n : ℚ) : ℝ))
    norm_num only [Rat.cast_pow]
    gcongr
    exact hx.2

/-- Executable sum of enclosures indexed by `1,…,N`. -/
def sumRangeOne (term : ℕ → RationalEnclosure) : ℕ → RationalEnclosure
  | 0 => point 0
  | N + 1 => add (sumRangeOne term N) (term (N + 1))

theorem contains_sumRangeOne
    {term : ℕ → RationalEnclosure} {f : ℕ → ℝ}
    (hterm : ∀ n, 1 ≤ n → (term n).Contains (f n)) :
    ∀ N, (sumRangeOne term N).Contains
      (∑ j ∈ Finset.range N, f (j + 1))
  | 0 => by simpa [sumRangeOne] using contains_point 0
  | N + 1 => by
      rw [Finset.sum_range_succ]
      simpa [sumRangeOne] using
        contains_add (contains_sumRangeOne hterm N) (hterm (N + 1) (by omega))

end RationalEnclosure

/-- Rational interval for one positive `P_W` head term. -/
def lrCompactVPWTermEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  RationalEnclosure.scale (lrLowAQ n) <|
    RationalEnclosure.mul
      (lrCompactVScoreEnclosure box n) (lrCompactVTEnclosure box n)

/-- Rational interval for one positive `Ψ` head term. -/
def lrCompactVPsiTermEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  RationalEnclosure.scale (lrLowAQ n) <|
    RationalEnclosure.mul (lrCompactVCEnclosure box n) <|
      RationalEnclosure.sub (RationalEnclosure.point 1)
        (lrCompactVScoreEnclosure box n)

theorem lrCompactVPWTermEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVPWTermEnclosure box n).Contains
      (lrCompactVPWTerm point.s point.k point.chi n) := by
  rcases hbox with ⟨hRLo, hRValid, hRHi, hvLo, hvValid, hvHi,
    hxLo, hxValid, hxHi⟩
  have hscore := lrCompactVScoreEnclosure_sound hn hRLo hRHi hpoint
  have hT := lrCompactVTEnclosure_sound (n := n) hvLo hxLo hpoint
  have hmul := RationalEnclosure.contains_mul hscore hT
  have hscale := RationalEnclosure.contains_scale (lrLowAQ n) hmul
  simpa [lrCompactVPWTermEnclosure, lrCompactVPWTerm, mul_assoc] using hscale

theorem lrCompactVPsiTermEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVPsiTermEnclosure box n).Contains
      (lrCompactVPsiTerm point.s point.k point.chi n) := by
  rcases hbox with ⟨hRLo, hRValid, hRHi, hvLo, hvValid, hvHi,
    hxLo, hxValid, hxHi⟩
  have hscore := lrCompactVScoreEnclosure_sound hn hRLo hRHi hpoint
  have hC := lrCompactVCEnclosure_sound (n := n) hvLo hxLo hpoint
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  have hcomp := RationalEnclosure.contains_sub hone hscore
  have hmul := RationalEnclosure.contains_mul hC hcomp
  have hscale := RationalEnclosure.contains_scale (lrLowAQ n) hmul
  simpa [lrCompactVPsiTermEnclosure, lrCompactVPsiTerm, mul_assoc] using hscale

/-- Enclosure of the finite positive head of `P_W`. -/
def lrCompactVPWHeadEnclosure (N : ℕ) (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.sumRangeOne (lrCompactVPWTermEnclosure box) N

/-- Enclosure of the finite polynomial part of the `Ψ` head.  The
nonnegative transcendental residual `f₀` is deliberately omitted; dropping it
gives a sharper and simpler certified lower bound for uses where only the
lower endpoint of `Ψ` matters. -/
def lrCompactVPsiPolynomialHeadEnclosure (N : ℕ)
    (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sumRangeOne (lrCompactVPsiTermEnclosure box) N

theorem lrCompactVPWHeadEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVPWHeadEnclosure N box).Contains
      (lrCompactVPWHead N point.s point.k point.chi) := by
  unfold lrCompactVPWHeadEnclosure lrCompactVPWHead
  exact RationalEnclosure.contains_sumRangeOne
    (fun n hn ↦ lrCompactVPWTermEnclosure_sound hbox hpoint hn) N

theorem lrCompactVPsiPolynomialHeadEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVPsiPolynomialHeadEnclosure N box).Contains
      (∑ j ∈ Finset.range N,
        lrCompactVPsiTerm point.s point.k point.chi (j + 1)) := by
  unfold lrCompactVPsiPolynomialHeadEnclosure
  exact RationalEnclosure.contains_sumRangeOne
    (fun n hn ↦ lrCompactVPsiTermEnclosure_sound hbox hpoint hn) N

/-- The polynomial head alone is a certified lower bound for `Ψ`, since
the omitted scalar residual `f₀(v)` is nonnegative on the compact chart. -/
theorem lrCompactVPsiPolynomialHead_lower
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hvPos : 0 < point.k) :
    ((lrCompactVPsiPolynomialHeadEnclosure N box).lower : ℝ) ≤
      lrCompactVPsiHead N point.s point.k point.chi := by
  have hcontains :=
    lrCompactVPsiPolynomialHeadEnclosure_sound (N := N) hbox hpoint
  have hvLe : point.k ≤ 1 := by
    rcases hpoint with ⟨_, _, _, hvUpper, _, _⟩
    exact hvUpper.trans (by exact_mod_cast hbox.2.2.2.2.2.1)
  have hfzero := lrCompactVFZero_nonneg
    (show point.k ∈ Ioc (0 : ℝ) 1 from ⟨hvPos, hvLe⟩)
  unfold lrCompactVPsiHead
  linarith [hcontains.1]

/-- Tight enclosure of `y=v²x`, increasing in both compact coordinates. -/
def lrCompactVYEnclosure (box : CertificateBox) : RationalEnclosure :=
  ⟨box.kLo ^ 2 * box.chiLo, box.kHi ^ 2 * box.chiHi⟩

theorem lrCompactVYEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVYEnclosure box).Contains (point.k ^ 2 * point.chi) := by
  rcases hbox with ⟨hRLo, hRValid, hRHi, hvLo, hvValid, hvHi,
    hxLo, hxValid, hxHi⟩
  rcases hpoint with ⟨hRpLo, hRpHi, hvpLo, hvpHi, hxpLo, hxpHi⟩
  have hvLoReal : (0 : ℝ) ≤ box.kLo := by exact_mod_cast hvLo
  have hxLoReal : (0 : ℝ) ≤ box.chiLo := by exact_mod_cast hxLo
  have hvPoint : 0 ≤ point.k := hvLoReal.trans hvpLo
  have hxPoint : 0 ≤ point.chi := hxLoReal.trans hxpLo
  constructor
  · change (((box.kLo ^ 2 * box.chiLo : ℚ) : ℝ)) ≤
      point.k ^ 2 * point.chi
    norm_num only [Rat.cast_mul, Rat.cast_pow]
    exact mul_le_mul (by gcongr) hxpLo hxLoReal (sq_nonneg point.k)
  · change point.k ^ 2 * point.chi ≤
      (((box.kHi ^ 2 * box.chiHi : ℚ) : ℝ))
    norm_num only [Rat.cast_mul, Rat.cast_pow]
    exact mul_le_mul (by gcongr) hxpHi hxPoint
      (sq_nonneg (box.kHi : ℝ))

/-- Enclosure of `1-R^n`, decreasing in `R`. -/
def lrCompactVOneSubRPowEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1) <|
    RationalEnclosure.powNonnegative box.sInterval n

theorem lrCompactVOneSubRPowEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (n : ℕ) :
    (lrCompactVOneSubRPowEnclosure box n).Contains
      (1 - point.s ^ n) := by
  have hR : box.sInterval.Contains point.s := by
    exact ⟨hpoint.1, hpoint.2.1⟩
  have hpow := RationalEnclosure.contains_powNonnegative hbox.1 hR n
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  simpa [lrCompactVOneSubRPowEnclosure] using
    RationalEnclosure.contains_sub hone hpow

/-- Enclosure of `y^n`, with `y=v²x`. -/
def lrCompactVYPowEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  RationalEnclosure.powNonnegative (lrCompactVYEnclosure box) n

theorem lrCompactVYPowEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (n : ℕ) :
    (lrCompactVYPowEnclosure box n).Contains
      ((point.k ^ 2 * point.chi) ^ n) := by
  have hy := lrCompactVYEnclosure_sound hbox hpoint
  have hyLower : (0 : ℚ) ≤ (lrCompactVYEnclosure box).lower := by
    simp only [lrCompactVYEnclosure]
    exact mul_nonneg (sq_nonneg box.kLo) hbox.2.2.2.2.2.2.1
  exact RationalEnclosure.contains_powNonnegative hyLower hy n

/-- Exact interval for the `n`th positive term of `D=A-B`. -/
def lrCompactVDTermEnclosure (box : CertificateBox) (n : ℕ) :
    RationalEnclosure :=
  RationalEnclosure.scale (1 / (2 * (n : ℚ))) <|
    RationalEnclosure.mulNonnegative
      (lrCompactVOneSubRPowEnclosure box n)
      (lrCompactVYPowEnclosure box n)

theorem lrCompactVDTermEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVDTermEnclosure box n).Contains
      (lrCompactVDTerm point.s (point.k ^ 2 * point.chi) n) := by
  have hR := lrCompactVOneSubRPowEnclosure_sound hbox hpoint n
  have hy := lrCompactVYPowEnclosure_sound hbox hpoint n
  have hRLower :
      (0 : ℚ) ≤ (lrCompactVOneSubRPowEnclosure box n).lower := by
    simp only [lrCompactVOneSubRPowEnclosure, RationalEnclosure.sub,
      RationalEnclosure.add, RationalEnclosure.neg,
      RationalEnclosure.point, RationalEnclosure.powNonnegative,
      CertificateBox.sInterval]
    have hsHiNonneg : (0 : ℚ) ≤ box.sHi := hbox.1.trans hbox.2.1
    have hpow : box.sHi ^ n ≤ (1 : ℚ) ^ n :=
      pow_le_pow_left₀ hsHiNonneg hbox.2.2.1 n
    simpa using hpow
  have hyLower :
      (0 : ℚ) ≤ (lrCompactVYPowEnclosure box n).lower := by
    simp only [lrCompactVYPowEnclosure, RationalEnclosure.powNonnegative,
      lrCompactVYEnclosure]
    exact pow_nonneg
      (mul_nonneg (sq_nonneg box.kLo) hbox.2.2.2.2.2.2.1) n
  have hmul := RationalEnclosure.contains_mulNonnegative
    hRLower hyLower hR hy
  have hscale := RationalEnclosure.contains_scale
    (1 / (2 * (n : ℚ))) hmul
  unfold lrCompactVDTermEnclosure
  convert hscale using 1
  unfold lrCompactVDTerm
  push_cast
  ring

/-- Enclosure of the finite `D=A-B` head. -/
def lrCompactVDHeadEnclosure (N : ℕ) (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.sumRangeOne (lrCompactVDTermEnclosure box) N

theorem lrCompactVDHeadEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVDHeadEnclosure N box).Contains
      (lrCompactVDHead N point.s (point.k ^ 2 * point.chi)) := by
  unfold lrCompactVDHeadEnclosure lrCompactVDHead
  exact RationalEnclosure.contains_sumRangeOne
    (fun n hn ↦ lrCompactVDTermEnclosure_sound hbox hpoint hn) N

/-- Enclosure of one summand in the finite error `E_N` from the enhanced
`P_W` lower bound.  General signed multiplication is intentional here: a
wide box may not itself prove the score difference positive, although its
exact value is positive by monotonicity in the index. -/
def lrCompactVPWErrorTermEnclosure
    (N : ℕ) (box : CertificateBox) (n : ℕ) : RationalEnclosure :=
  RationalEnclosure.scale (lrLowAQ n) <|
    RationalEnclosure.mul
      (RationalEnclosure.sub
        (lrCompactVScoreEnclosure box (N + 1))
        (lrCompactVScoreEnclosure box n))
      (lrCompactVTEnclosure box n)

theorem lrCompactVPWErrorTermEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVPWErrorTermEnclosure N box n).Contains
      (lrLowA n *
        (lrCompactVScore point.s (N + 1) -
          lrCompactVScore point.s n) *
        lrCompactVT point.k point.chi n) := by
  have hscoreN := lrCompactVScoreEnclosure_sound
    (n := N + 1) (by omega) hbox.1 hbox.2.2.1 hpoint
  have hscore := lrCompactVScoreEnclosure_sound hn
    hbox.1 hbox.2.2.1 hpoint
  have hdiff := RationalEnclosure.contains_sub hscoreN hscore
  have hT := lrCompactVTEnclosure_sound (n := n)
    hbox.2.2.2.1 hbox.2.2.2.2.2.2.1 hpoint
  have hmul := RationalEnclosure.contains_mul hdiff hT
  have hscale := RationalEnclosure.contains_scale (lrLowAQ n) hmul
  simpa [lrCompactVPWErrorTermEnclosure, mul_assoc] using hscale

/-- Enclosure of the complete finite error `E_N`. -/
def lrCompactVPWErrorEnclosure (N : ℕ) (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.sumRangeOne
    (lrCompactVPWErrorTermEnclosure N box) N

theorem lrCompactVPWErrorEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVPWErrorEnclosure N box).Contains
      (lrCompactVPWError N point.s point.k point.chi) := by
  unfold lrCompactVPWErrorEnclosure lrCompactVPWError
  exact RationalEnclosure.contains_sumRangeOne
    (fun n hn ↦
      lrCompactVPWErrorTermEnclosure_sound hbox hpoint hn) N

/-- The `x`-coordinate form of the positive base series `P₀`. -/
noncomputable def lrCompactVPZeroX (v x : ℝ) : ℝ :=
  topPhi (Real.sqrt x) + topPhi (v * Real.sqrt x) / v

/-- Enclose the enhanced lower expression `w_{N+1}P₀-E_N` from any
independently certified enclosure of `P₀`. -/
def lrCompactVPWLowerEnclosure
    (N : ℕ) (box : CertificateBox) (pZero : RationalEnclosure) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.mul (lrCompactVScoreEnclosure box (N + 1)) pZero)
    (lrCompactVPWErrorEnclosure N box)

theorem lrCompactVPWLowerEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {pZero : RationalEnclosure}
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi)) :
    (lrCompactVPWLowerEnclosure N box pZero).Contains
      (lrCompactVScore point.s (N + 1) *
          lrCompactVPZeroX point.k point.chi -
        lrCompactVPWError N point.s point.k point.chi) := by
  have hscore := lrCompactVScoreEnclosure_sound
    (n := N + 1) (by omega) hbox.1 hbox.2.2.1 hpoint
  exact RationalEnclosure.contains_sub
    (RationalEnclosure.contains_mul hscore hpZero)
    (lrCompactVPWErrorEnclosure_sound hbox hpoint)

theorem lrCompactVPWLowerEnclosure_sound_sqrt
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {pZero : RationalEnclosure}
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi)) :
    (lrCompactVPWLowerEnclosure N box pZero).Contains
      (lrCompactVPWLower N point.s point.k (Real.sqrt point.chi)) := by
  have hxNonneg : 0 ≤ point.chi := by
    exact (by exact_mod_cast hbox.2.2.2.2.2.2.1 :
      (0 : ℝ) ≤ box.chiLo) |>.trans hpoint.2.2.2.2.1
  have hsquare : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hxNonneg
  simpa [lrCompactVPWLower, lrCompactVPZeroX, hsquare] using
    lrCompactVPWLowerEnclosure_sound hbox hpoint hpZero

/-- Rational coupling `M_x=vx/(1+v)` in the grouped reserve. -/
def lrCompactVMxQ (v x : ℚ) : ℚ := v * x / (1 + v)

noncomputable def lrCompactVMx (v x : ℝ) : ℝ := v * x / (1 + v)

@[simp] theorem cast_lrCompactVMxQ (v x : ℚ) :
    (lrCompactVMxQ v x : ℝ) = lrCompactVMx v x := by
  simp only [lrCompactVMxQ, lrCompactVMx]
  push_cast
  rfl

/-- Tight endpoint enclosure for `M_x`, increasing in both `v` and `x`. -/
def lrCompactVMxEnclosure (box : CertificateBox) : RationalEnclosure :=
  ⟨lrCompactVMxQ box.kLo box.chiLo,
    lrCompactVMxQ box.kHi box.chiHi⟩

theorem lrCompactVMxEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVMxEnclosure box).Contains
      (lrCompactVMx point.k point.chi) := by
  rcases hbox with ⟨hRLo, hRValid, hRHi, hvLo, hvValid, hvHi,
    hxLo, hxValid, hxHi⟩
  rcases hpoint with ⟨hRpLo, hRpHi, hvpLo, hvpHi, hxpLo, hxpHi⟩
  have hvLoReal : (0 : ℝ) ≤ box.kLo := by exact_mod_cast hvLo
  have hxLoReal : (0 : ℝ) ≤ box.chiLo := by exact_mod_cast hxLo
  have hvPoint : 0 ≤ point.k := hvLoReal.trans hvpLo
  have hxPoint : 0 ≤ point.chi := hxLoReal.trans hxpLo
  have hdenLo : 0 < 1 + (box.kLo : ℝ) := by linarith
  have hdenPoint : 0 < 1 + point.k := by linarith
  have hdenHi : 0 < 1 + (box.kHi : ℝ) := by
    have : (0 : ℝ) ≤ box.kHi := hvPoint.trans hvpHi
    linarith
  have hmonoVLo :
      lrCompactVMx (box.kLo : ℝ) point.chi ≤
        lrCompactVMx point.k point.chi := by
    unfold lrCompactVMx
    rw [div_le_div_iff₀ hdenLo hdenPoint]
    nlinarith [mul_nonneg hxPoint (sub_nonneg.mpr hvpLo)]
  have hmonoVHi :
      lrCompactVMx point.k point.chi ≤
        lrCompactVMx (box.kHi : ℝ) point.chi := by
    unfold lrCompactVMx
    rw [div_le_div_iff₀ hdenPoint hdenHi]
    nlinarith [mul_nonneg hxPoint (sub_nonneg.mpr hvpHi)]
  constructor
  · change (lrCompactVMxQ box.kLo box.chiLo : ℝ) ≤
      lrCompactVMx point.k point.chi
    rw [cast_lrCompactVMxQ]
    have hxMonoLo :
        lrCompactVMx (box.kLo : ℝ) (box.chiLo : ℝ) ≤
          lrCompactVMx (box.kLo : ℝ) point.chi := by
      unfold lrCompactVMx
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxpLo hvLoReal) hdenLo.le
    exact hxMonoLo.trans hmonoVLo
  · change lrCompactVMx point.k point.chi ≤
      (lrCompactVMxQ box.kHi box.chiHi : ℝ)
    rw [cast_lrCompactVMxQ]
    have hxMonoHi :
        lrCompactVMx (box.kHi : ℝ) point.chi ≤
          lrCompactVMx (box.kHi : ℝ) (box.chiHi : ℝ) := by
      unfold lrCompactVMx
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxpHi (hvPoint.trans hvpHi)) hdenHi.le
    exact hmonoVHi.trans hxMonoHi

end CourtadeKumar
