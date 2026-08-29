import InformationTheory.CourtadeKumar.LRDeterminantContinuationTail

/-!
# Exact scalar restoration ledger for the determinant low-`k` bridge

This scratch module isolates the entirely rational part of (DA7).  In
particular, it checks the four restoration budgets, the auxiliary channel
relaxations, the endpoint-monotonicity polynomials, and the final
`19 / 50 - restore > 2 / 25` subtraction.  The analytic comparison between
the exact determinant and these four losses is deliberately left as an
explicit hypothesis of the final assembly theorem.
-/

namespace CourtadeKumar

noncomputable def lrDA7S0 : ℝ := 1 / 128

noncomputable def lrDA7LMinus : ℝ := 4851 / 1000

noncomputable def lrDA7LPlus : ℝ := 49 / 10

/-- The rational window used in the replay really brackets `7 log 2`. -/
theorem lrDA7_log_window :
    lrDA7LMinus < 7 * Real.log 2 ∧
      7 * Real.log 2 < lrDA7LPlus := by
  constructor
  · dsimp [lrDA7LMinus]
    nlinarith [Real.log_two_gt_d9]
  · dsimp [lrDA7LPlus]
    nlinarith [Real.log_two_lt_d9]

/-! ## Exact rational endpoint comparisons -/

/-- Rational comparisons used after the analytic channel estimates in DA7.
The theorem verifies the endpoint arithmetic; it does not itself derive the
underlying `v`- and `e`-dependent channel inequalities. -/
theorem lrDA7_channel_relaxations :
    (128 / 255 : ℝ) * (128 / 127) = 16384 / (127 * 255) ∧
      16384 / (127 * 255 : ℝ) < 51 / 100 ∧
      2 * (128 / 255 : ℝ) * (128 / 255) = 32768 / 65025 ∧
      32768 / 65025 < (51 / 100 : ℝ) ∧
      2 * (128 / 255 : ℝ) ^ 2 < 51 / 100 ∧
      (128 / 255 : ℝ) ^ 2 * (16384 / (127 * 255)) < 1 / 7 := by
  norm_num

/-- Exact value, and the convenient `7/10` upper bound, for the generalized
coefficient-restoration factor. -/
theorem lrDA7_coefficient_factor :
    ((lrDA7LMinus + 7 / 5) / (3 * lrDA7LMinus)) *
        (1 / 3 + 2 / lrDA7LMinus *
          (lrDA7LMinus / 2 + 7 / 10 + 1 / 256)) =
          112529609 / 161363664 ∧
      (112529609 / 161363664 : ℝ) < 7 / 10 := by
  norm_num [lrDA7LMinus]

/-- The positive channel change in `T` is below `1/10`. -/
theorem lrDA7_delta_t_positive_endpoint :
    lrDA7S0 *
        (2 / 5 + 51 / 100 * (lrDA7LPlus + 7 / 5)) =
          3613 / 128000 ∧
      (3613 / 128000 : ℝ) < 1 / 10 := by
  norm_num [lrDA7S0, lrDA7LPlus]

/-- The radial `T` factor used for the negative channel payment is below
`1/10`. -/
theorem lrDA7_radial_t_factor_lt_one_tenth :
    (3 / 14 : ℝ) * (4 / 7) * (7 / 10) * (128 / 127) < 1 / 10 := by
  norm_num

/-! ## The four exact endpoint budgets -/

noncomputable def lrDA7FiniteEndpoint : ℝ :=
  lrDA7S0 * (lrDA7LPlus + lrDA7S0) / 2 +
    lrDA7S0 / 2 * (lrDA7LPlus + 12 / 5) +
    lrDA7S0 * (lrDA7LPlus / 2 + 7 / 10) +
    lrDA7S0 / 2 * (lrDA7LPlus + 4) +
    lrDA7S0 ^ 2 / 2 +
    lrDA7S0 / (3 * lrDA7LMinus) *
      (2 * (lrDA7LPlus / 2 + 7 / 10) + lrDA7S0 / 2) *
      (lrDA7LPlus + 7 / 5)

noncomputable def lrDA7ChannelEndpoint : ℝ :=
  (51 / 50) * lrDA7S0 * (lrDA7LPlus + lrDA7S0) +
    (51 / 100) * lrDA7S0 * (lrDA7LPlus + 4 / 5) +
    lrDA7S0 / 10 + (7 / 10) * lrDA7S0

noncomputable def lrDA7EntropyEndpoint : ℝ :=
  (3 / 2) * lrDA7S0 * (lrDA7LPlus + 7 / 5) *
    ((lrDA7LPlus / 2 + 7 / 10 + 1 / 256) *
      (lrDA7LPlus + 3 / 2) / (3 * lrDA7LMinus))

noncomputable def lrDA7DirectEndpoint : ℝ :=
  (3 / 14) * lrDA7S0 ^ 3 *
    (lrDA7LPlus + 4 / 5) * (lrDA7LPlus + 7 / 5)

noncomputable def lrDA7RestoreEndpoint : ℝ :=
  lrDA7FiniteEndpoint + lrDA7ChannelEndpoint +
    lrDA7EntropyEndpoint + lrDA7DirectEndpoint

theorem lrDA7_finite_endpoint_exact :
    lrDA7FiniteEndpoint = 2430013 / 18923520 := by
  norm_num [lrDA7FiniteEndpoint, lrDA7S0, lrDA7LMinus, lrDA7LPlus]

theorem lrDA7_channel_endpoint_exact :
    lrDA7ChannelEndpoint = 55763 / 819200 := by
  norm_num [lrDA7ChannelEndpoint, lrDA7S0, lrDA7LPlus]

theorem lrDA7_entropy_endpoint_exact :
    lrDA7EntropyEndpoint = 367 / 3584 := by
  norm_num [lrDA7EntropyEndpoint, lrDA7S0, lrDA7LMinus, lrDA7LPlus]

theorem lrDA7_direct_endpoint_exact :
    lrDA7DirectEndpoint = 1539 / 419430400 := by
  norm_num [lrDA7DirectEndpoint, lrDA7S0, lrDA7LPlus]

/-- The four exact entries sum to the manuscript's restoration fraction. -/
theorem lrDA7_restore_endpoint_exact :
    lrDA7RestoreEndpoint = 5791710961 / 19377684480 := by
  rw [lrDA7RestoreEndpoint, lrDA7_finite_endpoint_exact,
    lrDA7_channel_endpoint_exact, lrDA7_entropy_endpoint_exact,
    lrDA7_direct_endpoint_exact]
  norm_num

/-- Exact slack below `3/10`. -/
theorem lrDA7_restore_slack_exact :
    3 / 10 - lrDA7RestoreEndpoint =
      21594383 / 19377684480 := by
  rw [lrDA7_restore_endpoint_exact]
  norm_num

theorem lrDA7_restore_endpoint_lt_three_tenths :
    lrDA7RestoreEndpoint < 3 / 10 := by
  have hslack := lrDA7_restore_slack_exact
  norm_num at hslack ⊢
  linarith

/-! ## Endpoint-monotonicity polynomials -/

noncomputable def lrDA7PFin (L : ℝ) : ℝ :=
  (L + 7 / 5 + lrDA7S0 / 2) * (L + 7 / 5)

noncomputable def lrDA7PFinPrime (L : ℝ) : ℝ :=
  (L + 7 / 5) + (L + 7 / 5 + lrDA7S0 / 2)

noncomputable def lrDA7PDir (L : ℝ) : ℝ :=
  (L + 4 / 5) * (L + 7 / 5)

noncomputable def lrDA7PDirPrime (L : ℝ) : ℝ :=
  (L + 7 / 5) + (L + 4 / 5)

noncomputable def lrDA7PEnt (L : ℝ) : ℝ :=
  (L + 7 / 5) * (L / 2 + 7 / 10 + 1 / 256) * (L + 3 / 2)

noncomputable def lrDA7PEntPrime (L : ℝ) : ℝ :=
  (L / 2 + 7 / 10 + 1 / 256) * (L + 3 / 2) +
    (L + 7 / 5) / 2 * (L + 3 / 2) +
    (L + 7 / 5) * (L / 2 + 7 / 10 + 1 / 256)

/-- The three endpoint gap values in (DA7). -/
theorem lrDA7_polynomial_gap_endpoints :
    lrDA7PFin lrDA7LMinus - lrDA7PFinPrime lrDA7LMinus =
        850992407 / 32000000 ∧
      3 * lrDA7PDir lrDA7LMinus - lrDA7PDirPrime lrDA7LMinus =
        94071203 / 1000000 ∧
      lrDA7PEnt lrDA7LMinus - lrDA7PEntPrime lrDA7LMinus =
        2078429316241 / 32000000000 := by
  norm_num [lrDA7PFin, lrDA7PFinPrime, lrDA7PDir, lrDA7PDirPrime,
    lrDA7PEnt, lrDA7PEntPrime, lrDA7LMinus, lrDA7S0]

/-- Taylor identity for `P_fin - P_fin'`; its displayed linear coefficient
is the first successive derivative in the manuscript. -/
theorem lrDA7_pFin_gap_taylor (L : ℝ) :
    lrDA7PFin L - lrDA7PFinPrime L =
      850992407 / 32000000 +
        (336189 / 32000) * (L - lrDA7LMinus) +
        (L - lrDA7LMinus) ^ 2 := by
  norm_num [lrDA7PFin, lrDA7PFinPrime, lrDA7LMinus, lrDA7S0]
  ring

/-- Taylor identity for `3 P_dir - P_dir'`. -/
theorem lrDA7_pDir_gap_taylor (L : ℝ) :
    3 * lrDA7PDir L - lrDA7PDirPrime L =
      94071203 / 1000000 +
        (16853 / 500) * (L - lrDA7LMinus) +
        3 * (L - lrDA7LMinus) ^ 2 := by
  norm_num [lrDA7PDir, lrDA7PDirPrime, lrDA7LMinus]
  ring

/-- Taylor identity for `P_ent - P_ent'`.  The coefficients record both
successive derivative checks `646816249/16000000` and
`253773/16000`; the cubic coefficient corresponds to third derivative `3`. -/
theorem lrDA7_pEnt_gap_taylor (L : ℝ) :
    lrDA7PEnt L - lrDA7PEntPrime L =
      2078429316241 / 32000000000 +
        (646816249 / 16000000) * (L - lrDA7LMinus) +
        (253773 / 32000) * (L - lrDA7LMinus) ^ 2 +
        (1 / 2) * (L - lrDA7LMinus) ^ 3 := by
  norm_num [lrDA7PEnt, lrDA7PEntPrime, lrDA7LMinus]
  ring

/-- The three derivative-side gaps are strictly positive throughout the
whole endpoint range `L ≥ L_-`. -/
theorem lrDA7_endpoint_polynomial_gaps_pos
    {L : ℝ} (hL : lrDA7LMinus ≤ L) :
    0 < lrDA7PFin L - lrDA7PFinPrime L ∧
      0 < 3 * lrDA7PDir L - lrDA7PDirPrime L ∧
      0 < lrDA7PEnt L - lrDA7PEntPrime L := by
  have hdelta : 0 ≤ L - lrDA7LMinus := sub_nonneg.mpr hL
  constructor
  · rw [lrDA7_pFin_gap_taylor]
    positivity
  constructor
  · rw [lrDA7_pDir_gap_taylor]
    positivity
  · rw [lrDA7_pEnt_gap_taylor]
    have hcube : 0 ≤ (L - lrDA7LMinus) ^ 3 := by positivity
    positivity

/-! ## Final arithmetic assembly -/

/-- Exact DA7 subtraction, with its strict positive slack made explicit. -/
theorem lrDA7_final_subtraction_exact :
    19 / 50 - lrDA7RestoreEndpoint - 2 / 25 =
      21594383 / 19377684480 := by
  rw [lrDA7_restore_endpoint_exact]
  norm_num

theorem lrDA7_nineteen_fiftieths_sub_restore_gt :
    2 / 25 < 19 / 50 - lrDA7RestoreEndpoint := by
  have h := lrDA7_final_subtraction_exact
  norm_num at h ⊢
  linarith

/-- Plug-in form of the DA7 restoration ledger.  Once the analytic proof
supplies the ideal-core lower bound and shows that the exact quantity loses
at most the four audited budgets, the final `2/25` margin is automatic. -/
theorem lrDA7_final_of_component_bounds
    {exactValue idealValue finiteLoss channelLoss entropyLoss directLoss : ℝ}
    (hideal : 19 / 50 < idealValue)
    (hfinite : finiteLoss ≤ lrDA7FiniteEndpoint)
    (hchannel : channelLoss ≤ lrDA7ChannelEndpoint)
    (hentropy : entropyLoss ≤ lrDA7EntropyEndpoint)
    (hdirect : directLoss ≤ lrDA7DirectEndpoint)
    (hexact :
      idealValue - (finiteLoss + channelLoss + entropyLoss + directLoss) ≤
        exactValue) :
    2 / 25 < exactValue := by
  have hbudget :
      finiteLoss + channelLoss + entropyLoss + directLoss ≤
        lrDA7RestoreEndpoint := by
    dsimp [lrDA7RestoreEndpoint]
    linarith
  have hmargin := lrDA7_nineteen_fiftieths_sub_restore_gt
  linarith

/-- A shorter plug-in form for callers which have already combined the four
restoration losses. -/
theorem lrDA7_final_of_total_restore
    {exactValue idealValue restore : ℝ}
    (hideal : 19 / 50 < idealValue)
    (hrestore : restore ≤ lrDA7RestoreEndpoint)
    (hexact : idealValue - restore ≤ exactValue) :
    2 / 25 < exactValue := by
  have hmargin := lrDA7_nineteen_fiftieths_sub_restore_gt
  linarith

end CourtadeKumar
