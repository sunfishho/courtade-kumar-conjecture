import InformationTheory.CourtadeKumar.LRLowShapeVGCertificate

/-! Exact Bernstein certificate for the low-shape V endpoint. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowVPhiEndpointFirstUpper : ℝ :=
  (∑ k ∈ Finset.range 12, lrLowA (k + 1) * (17 / 20 : ℝ) ^ (k + 1)) +
    lrLowA 13 * (17 / 20 : ℝ) ^ 13 / (1 - 17 / 20)

noncomputable def lrLowVPhiEndpointSecondUpper (v : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 12,
    lrLowA (k + 1) * (17 / 20 : ℝ) ^ (k + 1) *
      v ^ (2 * (k + 1) - 1)) +
    lrLowA 13 * (17 / 20 : ℝ) ^ 13 * v ^ 25 /
      (1 - (17 / 20 : ℝ) * v ^ 2)

noncomputable def lrLowVLEndpointUpper (v : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 12,
    ((17 / 20 : ℝ) * v ^ 2) ^ (k + 1) / (2 * (k + 1))) +
    ((17 / 20 : ℝ) * v ^ 2) ^ 13 /
      (26 * (1 - (17 / 20 : ℝ) * v ^ 2))

noncomputable def lrLowVBetaEndpointUpper (v : ℝ) : ℝ :=
  lrAtanh5 (v / (2 + v)) +
    v ^ 11 / (22 * (1 + v) * (2 + v) ^ 9)

noncomputable def lrLowVEndpointMinorant (v : ℝ) : ℝ :=
  lrLowGLower v - lrLowVPhiEndpointFirstUpper -
    lrLowVPhiEndpointSecondUpper v -
    2 * (1 - (17 / 20 : ℝ) * v ^ 2) *
      (lrLowVBetaEndpointUpper v + lrLowVLEndpointUpper v) /
      (v * (1 + v))

noncomputable def lrLowVEndpointCertificateBase (v : ℝ) : ℝ :=
  (1 + v) ^ 9 * (2 + v) ^ 9 *
    (20 * (1 - (17 / 20 : ℝ) * v ^ 2))

noncomputable def lrLowVEndpointBernstein (v : ℝ) : ℝ :=
  (((((135125583766319859291468165120 * bernsteinBasis 44 0 v + (1648917133819139177314854873600/11) * bernsteinBasis 44 1 v) + ((78946964318797037448724467116544/473) * bernsteinBasis 44 2 v + ((8014700918990893547186054291328/43) * bernsteinBasis 44 3 v + (28316713815005391413410654558609920/135751) * bernsteinBasis 44 4 v))) + (((31733143120504804149669098769261600/135751) * bernsteinBasis 44 5 v + ((35581643699016036239129863871072544/135751) * bernsteinBasis 44 6 v + (108266994653441371718228611431867000/368467) * bernsteinBasis 44 7 v)) + ((4486225251177836649533876065026014576/13633279) * bernsteinBasis 44 8 v + ((116638158885153090641970651218051470/317053) * bernsteinBasis 44 9 v + (1058185830731066072692613465819601954/2579269) * bernsteinBasis 44 10 v)))) + ((((1130516076311956128462191343099085765/2478778) * bernsteinBasis 44 11 v + (48196852023388238095862882804534677084/95432953) * bernsteinBasis 44 12 v) + ((212497489756378785354573372996665319993/381731812) * bernsteinBasis 44 13 v + ((8769656987251468708011210764989428014221/14369476066) * bernsteinBasis 44 14 v + (38222648817839383381020775141742132908255/57477904264) * bernsteinBasis 44 15 v))) + (((149925484678481503262900514056062024271412/208357402957) * bernsteinBasis 44 16 v + ((9467696179675798331842292925026498741586/12256317821) * bernsteinBasis 44 17 v + (211548369212561376005081870483000762747663/257382674241) * bernsteinBasis 44 18 v)) + ((46912459992100345516501955472909974099405/54185826156) * bernsteinBasis 44 19 v + ((550166871544755157961623585010486693294/610200745) * bernsteinBasis 44 20 v + (116587415207308857197117160379874117457931/125788525005) * bernsteinBasis 44 21 v))))) + (((((10735328859430999249677906929539409763746/11435320455) * bernsteinBasis 44 22 v + (78393628708118136984362138201669576037539/83859016670) * bernsteinBasis 44 23 v) + ((803688125142658986193868527633098575194192/880519675035) * bernsteinBasis 44 24 v + ((153393012139840222117891980963574794405773/176103935007) * bernsteinBasis 44 25 v + (69443624268105559095398146307724260363477/85794224747) * bernsteinBasis 44 26 v))) + (((250326817371204502315562671540149628933945/343176898988) * bernsteinBasis 44 27 v + ((707793433786056788642170431433654946078/1114210711) * bernsteinBasis 44 28 v + (903601877552113421281651935033127887669/1690526596) * bernsteinBasis 44 29 v)) + ((371520859028509661124254243964982243645/845263298) * bernsteinBasis 44 30 v + ((129230739535051792943012215484898433175/350780584) * bernsteinBasis 44 31 v + (178127204090126596384382343470624948400/514406893) * bernsteinBasis 44 32 v)))) + ((((779331671052184153389218495028645057935/1917334783) * bernsteinBasis 44 33 v + ((733624537886205580987886730141678629255/1240628389) * bernsteinBasis 44 34 v + (337598607848759994394869586822410868013/354465254) * bernsteinBasis 44 35 v)) + ((274594435373902123276347025131386554995/177232627) * bernsteinBasis 44 36 v + ((11719375394734461350932689938999339506/4790071) * bernsteinBasis 44 37 v + (6541532119370237212495426851203225924/1764763) * bernsteinBasis 44 38 v))) + (((66370004460029905706464657915720032/12341) * bernsteinBasis 44 39 v + ((144914552339743582836266616199428064/19393) * bernsteinBasis 44 40 v + (426948709949581069134887142316736/43) * bernsteinBasis 44 41 v)) + ((5934711720469123326486226154720640/473) * bernsteinBasis 44 42 v + ((163447768698534506956778329137536/11) * bernsteinBasis 44 43 v + 15844673176732054853724768154368 * bernsteinBasis 44 44 v))))))

lemma lrLowVEndpointBernstein_nonneg
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVEndpointBernstein v := by
  unfold lrLowVEndpointBernstein
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hv)

noncomputable def lrLowVEndpointPowerEval (v : ℝ) : ℝ :=
  (((((135125583766319859291468165120 * v ^ 0 + 650142849558482900434820229120 * v ^ 1) + (2108983863640723289022780177408 * v ^ 2 + (3268336223834558845500908533248 * v ^ 3 + 30894970587055954292245223424 * v ^ 4))) + ((-8855331830763144181084630091520 * v ^ 5 + (-17024826311069983806216463750272 * v ^ 6 + -13645787501468036718398905996608 * v ^ 7)) + (4856733094866633001909834429808 * v ^ 8 + (25922519376937499579916432379912 * v ^ 9 + 32276981461811668194275170763788 * v ^ 10)))) + (((21020632546144906648492618287422 * v ^ 11 + 3886017050297237317354977602154 * v ^ 12) + (-7435357241993913070332762261912 * v ^ 13 + (-10188829222968312088151801410704 * v ^ 14 + -8009787335992677062415115648668 * v ^ 15))) + ((-4960493115090857721068534749236 * v ^ 16 + (-2808976039750383344010660187680 * v ^ 17 + -1618847361317674700238819345772 * v ^ 18)) + (-997071240502110693630310629042 * v ^ 19 + (-654340151247119839410307611446 * v ^ 20 + -449397938244976615378679808000 * v ^ 21))))) + ((((-318760413526410280133889024000 * v ^ 22 + -231714032244076000379552716800 * v ^ 23) + (-171787922995288044815971968000 * v ^ 24 + (-129455760378966270925856543232 * v ^ 25 + -98913440760932408517840383232 * v ^ 26))) + ((-76521032091388231407853999616 * v ^ 27 + (-60241475042386724769761520000 * v ^ 28 + -49961094347862005567207994112 * v ^ 29)) + (-47774484434029570430462698368 * v ^ 30 + (-55964280720993241299312296112 * v ^ 31 + -72248967608057041588194136488 * v ^ 32)))) + (((-87256265672791185000981684132 * v ^ 33 + (-89671673072383675205282340858 * v ^ 34 + -75527202120969288840425138116 * v ^ 35)) + (-51383130140440487020808651527 * v ^ 36 + (-27994625139365529683740003184 * v ^ 37 + -12097485051571041330755213408 * v ^ 38))) + ((-4088011299862373373111679536 * v ^ 39 + (-1056592248982639292719513530 * v ^ 40 + -201616252650948482930739372 * v ^ 41)) + (-26758787689032633252068862 * v ^ 42 + (-2205380562587270357934876 * v ^ 43 + -84986182288459227898815 * v ^ 44))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma lrLowVEndpointBernstein_eq_power (v : ℝ) :
    lrLowVEndpointBernstein v = lrLowVEndpointPowerEval v := by
  unfold lrLowVEndpointBernstein lrLowVEndpointPowerEval bernsteinBasis
  norm_num [Nat.choose]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma lrLowVEndpoint_certificate_identity
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVEndpointMinorant v * lrLowVEndpointCertificateBase v *
        6450271027200000000000000 =
      lrLowVEndpointPowerEval v := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
      (by linarith [hv.1] : 0 ≤ 1 + v)]
  have hqPos : 0 < 1 - (17 / 20 : ℝ) * v ^ 2 := by
    nlinarith
  have hq : 1 - (17 / 20 : ℝ) * v ^ 2 ≠ 0 := hqPos.ne'
  have hq20 : 20 - v ^ 2 * 17 ≠ 0 := by nlinarith [hvSq]
  unfold lrLowVEndpointMinorant lrLowVPhiEndpointFirstUpper
    lrLowVPhiEndpointSecondUpper lrLowVLEndpointUpper
    lrLowVBetaEndpointUpper
    lrLowVEndpointCertificateBase lrLowVEndpointPowerEval
    lrLowGLower lrLowBetaLower lrLowMinusLogLower lrAtanh5 lrLowA
  norm_num [Finset.sum_range_succ, Nat.choose]
  field_simp [hv0, h1, h2, hq, hq20]
  ring_nf

theorem lrLowVEndpointMinorant_nonneg
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrLowVEndpointMinorant v := by
  have hbern := lrLowVEndpointBernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩)
  have hpower : 0 ≤ lrLowVEndpointPowerEval v := by
    rw [← lrLowVEndpointBernstein_eq_power]
    exact hbern
  have hid := lrLowVEndpoint_certificate_identity hv
  have hbase : 0 < lrLowVEndpointCertificateBase v := by
    unfold lrLowVEndpointCertificateBase
    have hvSq : v ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
        (by linarith [hv.1] : 0 ≤ 1 + v)]
    have hqPos : 0 < 1 - (17 / 20 : ℝ) * v ^ 2 := by nlinarith
    exact mul_pos
      (mul_pos (pow_pos (by linarith [hv.1]) _)
        (pow_pos (by linarith [hv.1]) _))
      (mul_pos (by norm_num) hqPos)
  have hscale : 0 < lrLowVEndpointCertificateBase v *
      (6450271027200000000000000 : ℝ) := mul_pos hbase (by norm_num)
  have hprod : 0 ≤ (lrLowVEndpointCertificateBase v *
      6450271027200000000000000) * lrLowVEndpointMinorant v := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

end CourtadeKumar
