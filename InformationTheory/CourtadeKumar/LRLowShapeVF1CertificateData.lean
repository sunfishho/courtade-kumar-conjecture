import InformationTheory.CourtadeKumar.LRLowShapeVMinorantBridge

/-! Generated exact tensor-Bernstein certificate for the low-shape `f_1` minorant. -/

open Set
namespace CourtadeKumar

noncomputable def lrLowVF1BernsteinRow0 (z : ℝ) : ℝ :=
  (15329709056 * bernsteinBasis 1 0 z + 13616109056 * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow0_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow0 z := by
  unfold lrLowVF1BernsteinRow0
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow1 (z : ℝ) : ℝ :=
  ((422706635264/19) * bernsteinBasis 1 0 z + (365301035264/19) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow1_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow1 z := by
  unfold lrLowVF1BernsteinRow1
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow2 (z : ℝ) : ℝ :=
  ((1892690649088/57) * bernsteinBasis 1 0 z + (1589383449088/57) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow2_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow2 z := by
  unfold lrLowVF1BernsteinRow2
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow3 (z : ℝ) : ℝ :=
  ((16339975476224/323) * bernsteinBasis 1 0 z + (13316328276224/323) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow3_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow3 z := by
  unfold lrLowVF1BernsteinRow3
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow4 (z : ℝ) : ℝ :=
  ((25260361510240/323) * bernsteinBasis 1 0 z + (19947076960240/323) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow4_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow4 z := by
  unfold lrLowVF1BernsteinRow4
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow5 (z : ℝ) : ℝ :=
  ((39451730617328/323) * bernsteinBasis 1 0 z + (30125542942328/323) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow5_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow5 z := by
  unfold lrLowVF1BernsteinRow5
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow6 (z : ℝ) : ℝ :=
  ((434387032310384/2261) * bernsteinBasis 1 0 z + (319927896785384/2261) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow6_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow6 z := by
  unfold lrLowVF1BernsteinRow6
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow7 (z : ℝ) : ℝ :=
  ((1275189474466664/4199) * bernsteinBasis 1 0 z + (902926782879164/4199) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow7_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow7 z := by
  unfold lrLowVF1BernsteinRow7
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow8 (z : ℝ) : ℝ :=
  ((1400228779018478/2907) * bernsteinBasis 1 0 z + (12342271244918339/37791) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow8_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow8 z := by
  unfold lrLowVF1BernsteinRow8
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow9 (z : ℝ) : ℝ :=
  ((35367909920478969/46189) * bernsteinBasis 1 0 z + (4154920849467483/8398) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow9_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow9 z := by
  unfold lrLowVF1BernsteinRow9
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow10 (z : ℝ) : ℝ :=
  ((56306780252682880/46189) * bernsteinBasis 1 0 z + (34463291691339130/46189) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow10_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow10 z := by
  unfold lrLowVF1BernsteinRow10
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow11 (z : ℝ) : ℝ :=
  ((24468101399992751/12597) * bernsteinBasis 1 0 z + (14082946108774001/12597) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow11_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow11 z := by
  unfold lrLowVF1BernsteinRow11
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow12 (z : ℝ) : ℝ :=
  ((999972397926456/323) * bernsteinBasis 1 0 z + (6971906981543928/4199) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow12_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow12 z := by
  unfold lrLowVF1BernsteinRow12
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow13 (z : ℝ) : ℝ :=
  ((11155800713058776/2261) * bernsteinBasis 1 0 z + (5510714338683776/2261) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow13_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow13 z := by
  unfold lrLowVF1BernsteinRow13
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow14 (z : ℝ) : ℝ :=
  ((7616406907492384/969) * bernsteinBasis 1 0 z + (3413451083992384/969) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow14_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow14 z := by
  unfold lrLowVF1BernsteinRow14
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow15 (z : ℝ) : ℝ :=
  ((4041439619719248/323) * bernsteinBasis 1 0 z + (1610390321419248/323) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow15_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow15 z := by
  unfold lrLowVF1BernsteinRow15
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow16 (z : ℝ) : ℝ :=
  ((6427008215335424/323) * bernsteinBasis 1 0 z + (2213408044135424/323) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow16_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow16 z := by
  unfold lrLowVF1BernsteinRow16
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow17 (z : ℝ) : ℝ :=
  ((5404259987474432/171) * bernsteinBasis 1 0 z + (1542313669874432/171) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow17_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow17 z := by
  unfold lrLowVF1BernsteinRow17
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow18 (z : ℝ) : ℝ :=
  ((952339896895488/19) * bernsteinBasis 1 0 z + (210306543295488/19) * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow18_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow18 z := by
  unfold lrLowVF1BernsteinRow18
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1BernsteinRow19 (z : ℝ) : ℝ :=
  (79361546074624 * bernsteinBasis 1 0 z + 11903968474624 * bernsteinBasis 1 1 z)

lemma lrLowVF1BernsteinRow19_nonneg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1BernsteinRow19 z := by
  unfold lrLowVF1BernsteinRow19
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)

noncomputable def lrLowVF1Bernstein (v z : ℝ) : ℝ :=
  ((((lrLowVF1BernsteinRow0 z * bernsteinBasis 19 0 v + lrLowVF1BernsteinRow1 z * bernsteinBasis 19 1 v) + (lrLowVF1BernsteinRow2 z * bernsteinBasis 19 2 v + (lrLowVF1BernsteinRow3 z * bernsteinBasis 19 3 v + lrLowVF1BernsteinRow4 z * bernsteinBasis 19 4 v))) + ((lrLowVF1BernsteinRow5 z * bernsteinBasis 19 5 v + lrLowVF1BernsteinRow6 z * bernsteinBasis 19 6 v) + (lrLowVF1BernsteinRow7 z * bernsteinBasis 19 7 v + (lrLowVF1BernsteinRow8 z * bernsteinBasis 19 8 v + lrLowVF1BernsteinRow9 z * bernsteinBasis 19 9 v)))) + (((lrLowVF1BernsteinRow10 z * bernsteinBasis 19 10 v + lrLowVF1BernsteinRow11 z * bernsteinBasis 19 11 v) + (lrLowVF1BernsteinRow12 z * bernsteinBasis 19 12 v + (lrLowVF1BernsteinRow13 z * bernsteinBasis 19 13 v + lrLowVF1BernsteinRow14 z * bernsteinBasis 19 14 v))) + ((lrLowVF1BernsteinRow15 z * bernsteinBasis 19 15 v + lrLowVF1BernsteinRow16 z * bernsteinBasis 19 16 v) + (lrLowVF1BernsteinRow17 z * bernsteinBasis 19 17 v + (lrLowVF1BernsteinRow18 z * bernsteinBasis 19 18 v + lrLowVF1BernsteinRow19 z * bernsteinBasis 19 19 v)))))

lemma lrLowVF1Bernstein_nonneg
    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1Bernstein v z := by
  unfold lrLowVF1Bernstein
  repeat' apply add_nonneg
  · exact mul_nonneg (lrLowVF1BernsteinRow0_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow1_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow2_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow3_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow4_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow5_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow6_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow7_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow8_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow9_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow10_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow11_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow12_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow13_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow14_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow15_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow16_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow17_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow18_nonneg hz) (bernsteinBasis_nonneg hv)
  · exact mul_nonneg (lrLowVF1BernsteinRow19_nonneg hz) (bernsteinBasis_nonneg hv)

end CourtadeKumar
