import InformationTheory.CourtadeKumar.LRLowShapeVF1CertificateData

/-! Separable exact reconstruction of the low-shape `f_1` certificate. -/

namespace CourtadeKumar

noncomputable def lrLowVF1ZPowerEvalRow0 (z : ℝ) : ℝ :=
  (15329709056 * z ^ 0 + -1713600000 * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow0_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow0 z = lrLowVF1ZPowerEvalRow0 z := by
  unfold lrLowVF1BernsteinRow0 lrLowVF1ZPowerEvalRow0 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow1 (z : ℝ) : ℝ :=
  ((422706635264/19) * z ^ 0 + (-57405600000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow1_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow1 z = lrLowVF1ZPowerEvalRow1 z := by
  unfold lrLowVF1BernsteinRow1 lrLowVF1ZPowerEvalRow1 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow2 (z : ℝ) : ℝ :=
  ((1892690649088/57) * z ^ 0 + (-101102400000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow2_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow2 z = lrLowVF1ZPowerEvalRow2 z := by
  unfold lrLowVF1BernsteinRow2 lrLowVF1ZPowerEvalRow2 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow3 (z : ℝ) : ℝ :=
  ((16339975476224/323) * z ^ 0 + (-177861600000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow3_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow3 z = lrLowVF1ZPowerEvalRow3 z := by
  unfold lrLowVF1BernsteinRow3 lrLowVF1ZPowerEvalRow3 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow4 (z : ℝ) : ℝ :=
  ((25260361510240/323) * z ^ 0 + (-312546150000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow4_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow4 z = lrLowVF1ZPowerEvalRow4 z := by
  unfold lrLowVF1BernsteinRow4 lrLowVF1ZPowerEvalRow4 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow5 (z : ℝ) : ℝ :=
  ((39451730617328/323) * z ^ 0 + (-548599275000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow5_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow5 z = lrLowVF1ZPowerEvalRow5 z := by
  unfold lrLowVF1BernsteinRow5 lrLowVF1ZPowerEvalRow5 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow6 (z : ℝ) : ℝ :=
  ((434387032310384/2261) * z ^ 0 + (-961841475000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow6_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow6 z = lrLowVF1ZPowerEvalRow6 z := by
  unfold lrLowVF1BernsteinRow6 lrLowVF1ZPowerEvalRow6 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow7 (z : ℝ) : ℝ :=
  ((1275189474466664/4199) * z ^ 0 + (-21897805387500/247) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow7_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow7 z = lrLowVF1ZPowerEvalRow7 z := by
  unfold lrLowVF1BernsteinRow7 lrLowVF1ZPowerEvalRow7 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow8 (z : ℝ) : ℝ :=
  ((1400228779018478/2907) * z ^ 0 + (-38305247596875/247) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow8_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow8 z = lrLowVF1ZPowerEvalRow8 z := by
  unfold lrLowVF1BernsteinRow8 lrLowVF1ZPowerEvalRow8 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow9 (z : ℝ) : ℝ :=
  ((35367909920478969/46189) * z ^ 0 + (-1472452382165625/5434) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow9_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow9 z = lrLowVF1ZPowerEvalRow9 z := by
  unfold lrLowVF1BernsteinRow9 lrLowVF1ZPowerEvalRow9 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow10 (z : ℝ) : ℝ :=
  ((56306780252682880/46189) * z ^ 0 + (-1284911091843750/2717) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow10_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow10 z = lrLowVF1ZPowerEvalRow10 z := by
  unfold lrLowVF1BernsteinRow10 lrLowVF1ZPowerEvalRow10 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow11 (z : ℝ) : ℝ :=
  ((24468101399992751/12597) * z ^ 0 + (-203630495906250/247) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow11_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow11 z = lrLowVF1ZPowerEvalRow11 z := by
  unfold lrLowVF1BernsteinRow11 lrLowVF1ZPowerEvalRow11 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow12 (z : ℝ) : ℝ :=
  ((999972397926456/323) * z ^ 0 + (-354572599500000/247) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow12_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow12 z = lrLowVF1ZPowerEvalRow12 z := by
  unfold lrLowVF1BernsteinRow12 lrLowVF1ZPowerEvalRow12 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow13 (z : ℝ) : ℝ :=
  ((11155800713058776/2261) * z ^ 0 + (-47437700625000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow13_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow13 z = lrLowVF1ZPowerEvalRow13 z := by
  unfold lrLowVF1BernsteinRow13 lrLowVF1ZPowerEvalRow13 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow14 (z : ℝ) : ℝ :=
  ((7616406907492384/969) * z ^ 0 + (-82410898500000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow14_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow14 z = lrLowVF1ZPowerEvalRow14 z := by
  unfold lrLowVF1BernsteinRow14 lrLowVF1ZPowerEvalRow14 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow15 (z : ℝ) : ℝ :=
  ((4041439619719248/323) * z ^ 0 + (-143002899900000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow15_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow15 z = lrLowVF1ZPowerEvalRow15 z := by
  unfold lrLowVF1BernsteinRow15 lrLowVF1ZPowerEvalRow15 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow16 (z : ℝ) : ℝ :=
  ((6427008215335424/323) * z ^ 0 + (-247858833600000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow16_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow16 z = lrLowVF1ZPowerEvalRow16 z := by
  unfold lrLowVF1BernsteinRow16 lrLowVF1ZPowerEvalRow16 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow17 (z : ℝ) : ℝ :=
  ((5404259987474432/171) * z ^ 0 + (-429105146400000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow17_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow17 z = lrLowVF1ZPowerEvalRow17 z := by
  unfold lrLowVF1BernsteinRow17 lrLowVF1ZPowerEvalRow17 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow18 (z : ℝ) : ℝ :=
  ((952339896895488/19) * z ^ 0 + (-742033353600000/19) * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow18_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow18 z = lrLowVF1ZPowerEvalRow18 z := by
  unfold lrLowVF1BernsteinRow18 lrLowVF1ZPowerEvalRow18 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerEvalRow19 (z : ℝ) : ℝ :=
  (79361546074624 * z ^ 0 + -67457577600000 * z ^ 1)

set_option maxHeartbeats 2000000 in
lemma lrLowVF1BernsteinRow19_eq_power (z : ℝ) :
    lrLowVF1BernsteinRow19 z = lrLowVF1ZPowerEvalRow19 z := by
  unfold lrLowVF1BernsteinRow19 lrLowVF1ZPowerEvalRow19 bernsteinBasis
  norm_num [Nat.choose]
  ring

noncomputable def lrLowVF1ZPowerRowsEval (v z : ℝ) : ℝ :=
  ((((lrLowVF1ZPowerEvalRow0 z * bernsteinBasis 19 0 v + lrLowVF1ZPowerEvalRow1 z * bernsteinBasis 19 1 v) + (lrLowVF1ZPowerEvalRow2 z * bernsteinBasis 19 2 v + (lrLowVF1ZPowerEvalRow3 z * bernsteinBasis 19 3 v + lrLowVF1ZPowerEvalRow4 z * bernsteinBasis 19 4 v))) + ((lrLowVF1ZPowerEvalRow5 z * bernsteinBasis 19 5 v + lrLowVF1ZPowerEvalRow6 z * bernsteinBasis 19 6 v) + (lrLowVF1ZPowerEvalRow7 z * bernsteinBasis 19 7 v + (lrLowVF1ZPowerEvalRow8 z * bernsteinBasis 19 8 v + lrLowVF1ZPowerEvalRow9 z * bernsteinBasis 19 9 v)))) + (((lrLowVF1ZPowerEvalRow10 z * bernsteinBasis 19 10 v + lrLowVF1ZPowerEvalRow11 z * bernsteinBasis 19 11 v) + (lrLowVF1ZPowerEvalRow12 z * bernsteinBasis 19 12 v + (lrLowVF1ZPowerEvalRow13 z * bernsteinBasis 19 13 v + lrLowVF1ZPowerEvalRow14 z * bernsteinBasis 19 14 v))) + ((lrLowVF1ZPowerEvalRow15 z * bernsteinBasis 19 15 v + lrLowVF1ZPowerEvalRow16 z * bernsteinBasis 19 16 v) + (lrLowVF1ZPowerEvalRow17 z * bernsteinBasis 19 17 v + (lrLowVF1ZPowerEvalRow18 z * bernsteinBasis 19 18 v + lrLowVF1ZPowerEvalRow19 z * bernsteinBasis 19 19 v)))))

lemma lrLowVF1Bernstein_eq_zPowerRows (v z : ℝ) :
    lrLowVF1Bernstein v z = lrLowVF1ZPowerRowsEval v z := by
  unfold lrLowVF1Bernstein lrLowVF1ZPowerRowsEval
  rw [lrLowVF1BernsteinRow0_eq_power, lrLowVF1BernsteinRow1_eq_power, lrLowVF1BernsteinRow2_eq_power, lrLowVF1BernsteinRow3_eq_power, lrLowVF1BernsteinRow4_eq_power, lrLowVF1BernsteinRow5_eq_power, lrLowVF1BernsteinRow6_eq_power, lrLowVF1BernsteinRow7_eq_power]
  rw [lrLowVF1BernsteinRow8_eq_power, lrLowVF1BernsteinRow9_eq_power, lrLowVF1BernsteinRow10_eq_power, lrLowVF1BernsteinRow11_eq_power, lrLowVF1BernsteinRow12_eq_power, lrLowVF1BernsteinRow13_eq_power, lrLowVF1BernsteinRow14_eq_power, lrLowVF1BernsteinRow15_eq_power]
  rw [lrLowVF1BernsteinRow16_eq_power, lrLowVF1BernsteinRow17_eq_power, lrLowVF1BernsteinRow18_eq_power, lrLowVF1BernsteinRow19_eq_power]

noncomputable def lrLowVF1ZPowerEvalCol0 (v : ℝ) : ℝ :=
  ((((15329709056 * bernsteinBasis 19 0 v + (422706635264/19) * bernsteinBasis 19 1 v) + ((1892690649088/57) * bernsteinBasis 19 2 v + ((16339975476224/323) * bernsteinBasis 19 3 v + (25260361510240/323) * bernsteinBasis 19 4 v))) + (((39451730617328/323) * bernsteinBasis 19 5 v + (434387032310384/2261) * bernsteinBasis 19 6 v) + ((1275189474466664/4199) * bernsteinBasis 19 7 v + ((1400228779018478/2907) * bernsteinBasis 19 8 v + (35367909920478969/46189) * bernsteinBasis 19 9 v)))) + ((((56306780252682880/46189) * bernsteinBasis 19 10 v + (24468101399992751/12597) * bernsteinBasis 19 11 v) + ((999972397926456/323) * bernsteinBasis 19 12 v + ((11155800713058776/2261) * bernsteinBasis 19 13 v + (7616406907492384/969) * bernsteinBasis 19 14 v))) + (((4041439619719248/323) * bernsteinBasis 19 15 v + (6427008215335424/323) * bernsteinBasis 19 16 v) + ((5404259987474432/171) * bernsteinBasis 19 17 v + ((952339896895488/19) * bernsteinBasis 19 18 v + 79361546074624 * bernsteinBasis 19 19 v)))))

noncomputable def lrLowVF1VPowerEvalCol0 (v : ℝ) : ℝ :=
  ((((15329709056 * v ^ 0 + 131442163200 * v ^ 1) + (690732761088 * v ^ 2 + 2312330445312 * v ^ 3)) + ((5512638017664 * v ^ 4 + 9927924686400 * v ^ 5) + (13855309091136 * v ^ 6 + (15241797276768 * v ^ 7 + 13383590194348 * v ^ 8)))) + (((9431766178446 * v ^ 9 + 5325926882112 * v ^ 10) + (2394768309864 * v ^ 11 + 849032162328 * v ^ 12)) + ((233356706676 * v ^ 13 + 48060357792 * v ^ 14) + (6917204808 * v ^ 15 + (601861788 * v ^ 16 + 22065838 * v ^ 17)))))

noncomputable def lrLowVF1ZPowerEvalCol1 (v : ℝ) : ℝ :=
  ((((-1713600000 * bernsteinBasis 19 0 v + (-57405600000/19) * bernsteinBasis 19 1 v) + ((-101102400000/19) * bernsteinBasis 19 2 v + ((-177861600000/19) * bernsteinBasis 19 3 v + (-312546150000/19) * bernsteinBasis 19 4 v))) + (((-548599275000/19) * bernsteinBasis 19 5 v + (-961841475000/19) * bernsteinBasis 19 6 v) + ((-21897805387500/247) * bernsteinBasis 19 7 v + ((-38305247596875/247) * bernsteinBasis 19 8 v + (-1472452382165625/5434) * bernsteinBasis 19 9 v)))) + ((((-1284911091843750/2717) * bernsteinBasis 19 10 v + (-203630495906250/247) * bernsteinBasis 19 11 v) + ((-354572599500000/247) * bernsteinBasis 19 12 v + ((-47437700625000/19) * bernsteinBasis 19 13 v + (-82410898500000/19) * bernsteinBasis 19 14 v))) + (((-143002899900000/19) * bernsteinBasis 19 15 v + (-247858833600000/19) * bernsteinBasis 19 16 v) + ((-429105146400000/19) * bernsteinBasis 19 17 v + ((-742033353600000/19) * bernsteinBasis 19 18 v + -67457577600000 * bernsteinBasis 19 19 v)))))

noncomputable def lrLowVF1VPowerEvalCol1 (v : ℝ) : ℝ :=
  ((((-1713600000 * v ^ 0 + -24847200000 * v ^ 1) + (-169646400000 * v ^ 2 + (-724852800000 * v ^ 3 + -2172630600000 * v ^ 4))) + ((-4853236500000 * v ^ 5 + -8377897500000 * v ^ 6) + (-11435870250000 * v ^ 7 + (-12524976843750 * v ^ 8 + -11103073734375 * v ^ 9)))) + (((-7999044637500 * v ^ 10 + -4683258759375 * v ^ 11) + (-2219098612500 * v ^ 12 + (-843553068750 * v ^ 13 + -253505700000 * v ^ 14))) + ((-58858143750 * v ^ 15 + -10181193750 * v ^ 16) + (-1234996875 * v ^ 17 + (-93712500 * v ^ 18 + -3346875 * v ^ 19)))))

noncomputable def lrLowVF1ZPowerColsEval (v z : ℝ) : ℝ :=
  (lrLowVF1ZPowerEvalCol0 v * z ^ 0 + lrLowVF1ZPowerEvalCol1 v * z ^ 1)

noncomputable def lrLowVF1PowerEval (v z : ℝ) : ℝ :=
  (lrLowVF1VPowerEvalCol0 v * z ^ 0 + lrLowVF1VPowerEvalCol1 v * z ^ 1)

set_option maxHeartbeats 8000000 in
lemma lrLowVF1ZPowerRows_eq_cols (v z : ℝ) :
    lrLowVF1ZPowerRowsEval v z = lrLowVF1ZPowerColsEval v z := by
  unfold lrLowVF1ZPowerRowsEval lrLowVF1ZPowerColsEval
  unfold lrLowVF1ZPowerEvalRow0
  unfold lrLowVF1ZPowerEvalRow1
  unfold lrLowVF1ZPowerEvalRow2
  unfold lrLowVF1ZPowerEvalRow3
  unfold lrLowVF1ZPowerEvalRow4
  unfold lrLowVF1ZPowerEvalRow5
  unfold lrLowVF1ZPowerEvalRow6
  unfold lrLowVF1ZPowerEvalRow7
  unfold lrLowVF1ZPowerEvalRow8
  unfold lrLowVF1ZPowerEvalRow9
  unfold lrLowVF1ZPowerEvalRow10
  unfold lrLowVF1ZPowerEvalRow11
  unfold lrLowVF1ZPowerEvalRow12
  unfold lrLowVF1ZPowerEvalRow13
  unfold lrLowVF1ZPowerEvalRow14
  unfold lrLowVF1ZPowerEvalRow15
  unfold lrLowVF1ZPowerEvalRow16
  unfold lrLowVF1ZPowerEvalRow17
  unfold lrLowVF1ZPowerEvalRow18
  unfold lrLowVF1ZPowerEvalRow19
  unfold lrLowVF1ZPowerEvalCol0
  unfold lrLowVF1ZPowerEvalCol1
  ring

set_option maxHeartbeats 8000000 in
lemma lrLowVF1ZPowerEvalCol0_eq_power (v : ℝ) :
    lrLowVF1ZPowerEvalCol0 v = lrLowVF1VPowerEvalCol0 v := by
  unfold lrLowVF1ZPowerEvalCol0 lrLowVF1VPowerEvalCol0 bernsteinBasis
  norm_num [Nat.choose]
  ring

set_option maxHeartbeats 8000000 in
lemma lrLowVF1ZPowerEvalCol1_eq_power (v : ℝ) :
    lrLowVF1ZPowerEvalCol1 v = lrLowVF1VPowerEvalCol1 v := by
  unfold lrLowVF1ZPowerEvalCol1 lrLowVF1VPowerEvalCol1 bernsteinBasis
  norm_num [Nat.choose]
  ring

lemma lrLowVF1ZPowerCols_eq_power (v z : ℝ) :
    lrLowVF1ZPowerColsEval v z = lrLowVF1PowerEval v z := by
  unfold lrLowVF1ZPowerColsEval lrLowVF1PowerEval
  rw [lrLowVF1ZPowerEvalCol0_eq_power, lrLowVF1ZPowerEvalCol1_eq_power]

theorem lrLowVF1Bernstein_eq_power (v z : ℝ) :
    lrLowVF1Bernstein v z = lrLowVF1PowerEval v z := by
  rw [lrLowVF1Bernstein_eq_zPowerRows, lrLowVF1ZPowerRows_eq_cols,
    lrLowVF1ZPowerCols_eq_power]

end CourtadeKumar
