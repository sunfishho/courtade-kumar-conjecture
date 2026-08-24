import InformationTheory.CourtadeKumar.TopCertificatePolynomial

/-! Extraction of the rational finite lower bound from the exact TOP
Bernstein numerator certificate. -/

open Set

namespace CourtadeKumar

lemma topCertR_mem_Ioo {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCertR c z ∈ Ioo (0 : ℝ) 1 := by
  have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc.1
  have hc2lt : c ^ 2 < 1 := by nlinarith [hc.1, hc.2]
  constructor
  · unfold topCertR
    nlinarith [mul_pos hc2pos hz.1]
  · have hprod : 0 < c ^ 2 * (1 - z) := mul_pos hc2pos (sub_pos.mpr hz.2)
    unfold topCertR
    nlinarith

lemma topCertD_pos {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    0 < topCertD c := by
  unfold topCertD
  exact mul_pos (by linarith [hc.1]) (sq_pos_of_pos (by linarith [hc.2]))

lemma topCertB_pos {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < topCertB c z := by
  unfold topCertB
  exact mul_pos (mul_pos hz.1 (sq_pos_of_pos hc.1)) (by linarith [hc.2])

lemma topCertH_pos {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < topCertH c z := by
  unfold topCertH
  have hd := topCertD_pos hc
  have hb := topCertB_pos hc hz
  linarith

lemma topCertZDen_pos {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < topCertZDen c z := by
  unfold topCertZDen
  have hd := topCertD_pos hc
  have hb := topCertB_pos hc hz
  have hh := topCertH_pos hc hz
  positivity

lemma topCertificate_commonDenominator {c z : ℝ}
    (hR : topCertR c z ≠ 0) (hden : topCertZDen c z ≠ 0) :
    topCertW8 c z + topCertZNum c z / topCertZDen c z +
          topCertEnum c z / topCertR c z ^ 9 - 1 / 100 =
      topCertificatePolynomial c z /
        (topCertR c z ^ 9 * topCertZDen c z) := by
  unfold topCertificatePolynomial
  field_simp
  ring

/-- Exact finite claim from the audited TOP certificate. -/
theorem topFiniteClaim {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (1 : ℝ) / 100 ≤
      topCertW8 c z + topCertZNum c z / topCertZDen c z +
        topCertEnum c z / topCertR c z ^ 9 := by
  have hR := topCertR_mem_Ioo hc hz
  have hden := topCertZDen_pos hc hz
  have hP := topCertificatePolynomial_nonneg
    (show c ∈ Icc (0 : ℝ) 1 from ⟨hc.1.le, hc.2.le⟩)
    (show z ∈ Icc (0 : ℝ) 1 from ⟨hz.1.le, hz.2.le⟩)
  have hdenom : 0 < topCertR c z ^ 9 * topCertZDen c z :=
    mul_pos (pow_pos hR.1 _) hden
  have hquot : 0 ≤ topCertificatePolynomial c z /
      (topCertR c z ^ 9 * topCertZDen c z) :=
    div_nonneg hP hdenom.le
  rw [← topCertificate_commonDenominator hR.1.ne' hden.ne'] at hquot
  linarith

end CourtadeKumar
