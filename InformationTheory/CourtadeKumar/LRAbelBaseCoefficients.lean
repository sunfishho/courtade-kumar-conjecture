import InformationTheory.CourtadeKumar.LRAbelBasePrefixes

/-! Explicit coefficient collection for the base (`R = 0`) Abel series. -/

namespace CourtadeKumar

/-- The manuscript coefficients of `F_v(x) = Z₀ + q E`, zero-indexed.
The first two coefficients contain the finite correction terms; thereafter
the expression is uniform. -/
noncomputable def lrAbelExplicitCoeff (v : ℝ) : ℕ → ℝ
  | 0 => lrAbelFirstPrefix v
  | 1 =>
      (1 + v ^ 3) / 12 +
        (3 - v) * v ^ 4 / 8 -
        (1 + v) * v ^ 2 / 4 -
        (1 + v) / 2 +
        (1 + v) / 2 * Real.log (1 + v)
  | n + 2 =>
      let N : ℕ := n + 3
      (1 + v ^ (2 * N - 1)) /
          (2 * (N : ℝ) * (2 * (N : ℝ) - 1)) +
        (3 - v) * v ^ (2 * N) / (4 * (N : ℝ)) -
        (1 + v) * v ^ (2 * N - 2) / (4 * ((N : ℝ) - 1))

lemma lrAbelBaseCoeff_one (v : ℝ) :
    lrAbelBaseCoeff v 1 = lrAbelExplicitCoeff v 1 := by
  unfold lrAbelBaseCoeff lrAbelBasePrefix lrAbelExplicitCoeff
    lrAbelPrefixS lrAbelFirstPrefix lrAbelPhiPrefixAtOne
    lrAbelPhiDivPrefix lrAbelLogPrefixPow
  norm_num [Finset.sum_range_succ, lrAbelCStar]
  ring

lemma lrAbelBaseCoeff_add_two (v : ℝ) (n : ℕ) :
    lrAbelBaseCoeff v (n + 2) = lrAbelExplicitCoeff v (n + 2) := by
  have hPhiOne :
      lrAbelPhiPrefixAtOne (n + 3) = lrAbelPhiPrefixAtOne (n + 2) +
        1 / (2 * ((n + 3 : ℕ) : ℝ) *
          (2 * ((n + 3 : ℕ) : ℝ) - 1)) := by
    have h := lrAbelPhiPrefixAtOne_succ (n + 2)
    convert h using 1
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hPhiV :
      lrAbelPhiDivPrefix (n + 3) v = lrAbelPhiDivPrefix (n + 2) v +
        v ^ (2 * (n + 3) - 1) /
          (2 * ((n + 3 : ℕ) : ℝ) *
            (2 * ((n + 3 : ℕ) : ℝ) - 1)) := by
    unfold lrAbelPhiDivPrefix
    conv_lhs => rw [show n + 3 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    rw [show 2 * (n + 2) + 1 = 2 * (n + 3) - 1 by omega]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hLog :
      lrAbelLogPrefixPow (n + 2) v =
        lrAbelLogPrefixPow (n + 1) v +
          v ^ (2 * (n + 3) - 2) /
            (2 * (((n + 3 : ℕ) : ℝ) - 1)) := by
    have h := lrAbelLogPrefixPow_succ
      (N := n + 2) (show 1 ≤ n + 2 by omega) v
    rw [show n + 2 - 1 = n + 1 by omega,
      show 2 * (n + 2) = 2 * (n + 3) - 2 by omega] at h
    convert h using 1
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring
  unfold lrAbelBaseCoeff lrAbelBasePrefix lrAbelExplicitCoeff
  dsimp only
  change lrAbelPrefixS (n + 3) v - lrAbelPrefixS (n + 2) v = _
  unfold lrAbelPrefixS
  rw [hPhiOne, hPhiV]
  rw [show n + 3 - 1 = n + 2 by omega, show n + 2 - 1 = n + 1 by omega,
    hLog]
  have hNReal : 0 < ((n + 3 : ℕ) : ℝ) := by positivity
  have hNMinus : 0 < ((n + 3 : ℕ) : ℝ) - 1 := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  have hnTwo : 2 + (n : ℝ) ≠ 0 := by positivity
  have hnOdd : 5 + (n : ℝ) * 2 ≠ 0 := by positivity
  rw [show v ^ (2 * (n + 3) - 2) = v ^ 4 * v ^ (n * 2) by
        rw [show 2 * (n + 3) - 2 = 4 + n * 2 by omega, pow_add],
      show v ^ (2 * (n + 3) - 1) = v ^ 5 * v ^ (n * 2) by
        rw [show 2 * (n + 3) - 1 = 5 + n * 2 by omega, pow_add],
      show v ^ (2 * (n + 3)) = v ^ 6 * v ^ (n * 2) by
        rw [show 2 * (n + 3) = 6 + n * 2 by omega, pow_add],
      show v ^ (2 * (n + 2)) = v ^ 4 * v ^ (n * 2) by
        rw [show 2 * (n + 2) = 4 + n * 2 by omega, pow_add]]
  ring_nf
  field_simp [hnTwo, hnOdd]
  ring

/-- The coefficients recovered from the audited prefix formulas agree with
the coefficients obtained by direct collection in `Z₀ + qE`. -/
theorem lrAbelBaseCoeff_eq_explicit (v : ℝ) (n : ℕ) :
    lrAbelBaseCoeff v n = lrAbelExplicitCoeff v n := by
  rcases n with (_ | _ | n)
  · rfl
  · exact lrAbelBaseCoeff_one v
  · exact lrAbelBaseCoeff_add_two v n

end CourtadeKumar
