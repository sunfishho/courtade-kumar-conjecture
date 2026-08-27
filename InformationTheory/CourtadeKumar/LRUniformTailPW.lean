import InformationTheory.CourtadeKumar.LRUniformTailOmega

/-!
# The uniform-tail lower bound for `P_W`

This file proves manuscript (M19) in the original flow coordinates.  The
proof keeps the two correlated noise-kernel terms together, which preserves
the factor `(1 + v) (1 + v⁻³)` used in the paper.
-/

open Set

namespace CourtadeKumar

lemma lrUniformTail_v_factor
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    4 / (v * (1 + v)) ≤ 1 / v ^ 4 + 1 / v := by
  have hvPos : 0 < v := hv.1
  have hdenPos : 0 < v * (1 + v) := mul_pos hvPos (by linarith)
  have hv4Pos : 0 < v ^ 4 := pow_pos hvPos 4
  have hright : 1 / v ^ 4 + 1 / v = (1 + v ^ 3) / v ^ 4 := by
    field_simp [hvPos.ne']
  rw [hright, div_le_div_iff₀ hdenPos hv4Pos]
  have hvSqNonneg : 0 ≤ v ^ 2 := sq_nonneg v
  have hquotNeg : v ^ 3 - 2 * v ^ 2 - 2 * v - 1 < 0 := by
    have hvCubeLeSq : v ^ 3 ≤ v ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hv.2 hvSqNonneg]
    nlinarith
  have hfactor :
      0 ≤ (1 - v) * (-(v ^ 3 - 2 * v ^ 2 - 2 * v - 1)) :=
    mul_nonneg (sub_nonneg.mpr hv.2) (neg_nonneg.mpr hquotNeg.le)
  nlinarith [hfactor]

lemma lrUniformTail_denominator_factor
    {s e : ℝ} (hs : 0 < s) (he : 0 < e) (hk : 3 * s ≤ e) :
    1 / (16 * e) ≤ 1 / (12 * (e + s)) := by
  rw [div_le_div_iff₀ (mul_pos (by norm_num) he)
    (mul_pos (by norm_num) (add_pos he hs))]
  nlinarith

/-- Manuscript (M19), with `e = 1-v²t²` and `s = 1-R`. -/
theorem lrUniformTailPW_div_lower
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hk : 3 * (1 - R) ≤ 1 - v ^ 2 * t ^ 2) :
    (1 - R) * (v ^ 2 * t ^ 2) ^ 2 /
        (4 * (1 - v ^ 2 * t ^ 2) * v * (1 + v)) ≤
      lrFlowPW R v t / (1 - R) := by
  have hs : 1 - R ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hR.1, hR.2]
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have he : 1 - v ^ 2 * t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    have hsquare : (v * t) ^ 2 = v ^ 2 * t ^ 2 := by ring
    constructor
    · rw [← hsquare]
      nlinarith [(sq_lt_sq₀ hvtPos.le (by norm_num)).2 hvtLt]
    · nlinarith [sq_pos_of_pos hv.1, sq_pos_of_pos ht.1]
  have hy0 : 1 - t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · nlinarith [(sq_lt_sq₀ ht.1.le (by norm_num)).2 ht.2]
    · nlinarith [sq_pos_of_pos ht.1]
  have hy0LeE : 1 - t ^ 2 ≤ 1 - v ^ 2 * t ^ 2 := by
    have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    nlinarith [mul_le_mul_of_nonneg_right hvSqLe (sq_nonneg t)]
  have homegaT := lrCertificateOmega_lower hs hy0
  have homegaVT := lrCertificateOmega_lower hs he
  have hdenY : 0 < 12 * ((1 - t ^ 2) + (1 - R)) :=
    mul_pos (by norm_num) (add_pos hy0.1 hs.1)
  have hdenE : 0 < 12 * ((1 - v ^ 2 * t ^ 2) + (1 - R)) :=
    mul_pos (by norm_num) (add_pos he.1 hs.1)
  have hnumT : 0 ≤ (1 - R) ^ 2 * t ^ 4 := by positivity
  have hdenOrder :
      12 * ((1 - t ^ 2) + (1 - R)) ≤
        12 * ((1 - v ^ 2 * t ^ 2) + (1 - R)) := by
    nlinarith
  have homegaT' :
      (1 - R) ^ 2 * t ^ 4 /
          (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) ≤
        lrCertificateOmega (1 - R) (1 - t ^ 2) := by
    apply le_trans _ homegaT
    rw [show (1 - (1 - t ^ 2)) ^ 2 = t ^ 4 by ring]
    exact div_le_div_of_nonneg_left hnumT hdenY hdenOrder
  have homegaVT' :
      ((1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
          (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R)))) / v ≤
        lrCertificateOmega (1 - R) (1 - v ^ 2 * t ^ 2) / v := by
    have hbase :
        (1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
            (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) ≤
          lrCertificateOmega (1 - R) (1 - v ^ 2 * t ^ 2) := by
      simpa [show (1 - (1 - v ^ 2 * t ^ 2)) ^ 2 =
          (v ^ 2 * t ^ 2) ^ 2 by ring] using homegaVT
    exact div_le_div_of_nonneg_right hbase hv.1.le
  have hsum :
      (1 - R) ^ 2 * t ^ 4 /
          (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) +
        ((1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
          (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R)))) / v ≤
      lrCertificateOmega (1 - R) (1 - t ^ 2) +
        lrCertificateOmega (1 - R) (1 - v ^ 2 * t ^ 2) / v :=
    add_le_add homegaT' homegaVT'
  have hrecip := lrUniformTail_denominator_factor hs.1 he.1 hk
  have hvFactor := lrUniformTail_v_factor
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hfactorNonneg : 0 ≤ 4 / (v * (1 + v)) :=
    div_nonneg (by norm_num) (mul_nonneg hv.1.le (by linarith [hv.1]))
  have hrecipNonneg : 0 ≤ 1 / (16 * (1 - v ^ 2 * t ^ 2)) :=
    div_nonneg (by norm_num) (mul_nonneg (by norm_num) he.1.le)
  have hrecipUpperNonneg :
      0 ≤ 1 / (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) :=
    div_nonneg (by norm_num) hdenE.le
  have hproduct :
      1 / (16 * (1 - v ^ 2 * t ^ 2)) * (4 / (v * (1 + v))) ≤
        1 / (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) *
          (1 / v ^ 4 + 1 / v) :=
    mul_le_mul hrecip hvFactor hfactorNonneg hrecipUpperNonneg
  have hscale : 0 ≤ (1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 := by positivity
  have hlower :
      (1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
          (4 * (1 - v ^ 2 * t ^ 2) * v * (1 + v)) ≤
        (1 - R) ^ 2 * t ^ 4 /
            (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) +
          ((1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
            (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R)))) / v := by
    have hscaled := mul_le_mul_of_nonneg_left hproduct hscale
    have hleftEq :
        ((1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2) *
            (1 / (16 * (1 - v ^ 2 * t ^ 2)) *
              (4 / (v * (1 + v)))) =
          (1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
            (4 * (1 - v ^ 2 * t ^ 2) * v * (1 + v)) := by
      field_simp [hv.1.ne', he.1.ne']
      ring
    have hrightEq :
        ((1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2) *
            (1 / (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) *
              (1 / v ^ 4 + 1 / v)) =
          (1 - R) ^ 2 * t ^ 4 /
              (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R))) +
            ((1 - R) ^ 2 * (v ^ 2 * t ^ 2) ^ 2 /
              (12 * ((1 - v ^ 2 * t ^ 2) + (1 - R)))) / v := by
      field_simp [hv.1.ne', hdenE.ne']
    rw [hleftEq, hrightEq] at hscaled
    exact hscaled
  have hkernelT := lrCertificateOmega_one_sub_sq hs
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hkernelVT := lrCertificateOmega_one_sub_sq hs
    (show v * t ∈ Ioc (0 : ℝ) 1 from ⟨hvtPos, hvtLt.le⟩)
  have hpw :
      lrCertificateOmega (1 - R) (1 - t ^ 2) +
          lrCertificateOmega (1 - R) (1 - v ^ 2 * t ^ 2) / v =
        lrFlowPW R v t := by
    rw [hkernelT]
    rw [show 1 - (v * t) ^ 2 = 1 - v ^ 2 * t ^ 2 by ring] at hkernelVT
    rw [hkernelVT]
    simpa [lrFlowPW]
  rw [hpw] at hsum
  have hPW := hlower.trans hsum
  rw [le_div_iff₀ hs.1]
  convert hPW using 1 <;> ring

end CourtadeKumar
