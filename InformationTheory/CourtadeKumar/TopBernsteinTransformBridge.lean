import InformationTheory.CourtadeKumar.TopBernsteinLiteralBindings
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.List.GetD

/-!
# Kernel-only bridge for the TOP Bernstein transform

This module imports the separately checked integer/rational table bindings and
proves that the allocation-efficient
adjacent-difference checks implement iterated unit forward differences.
The large arithmetic is performed only in `Int`; the passage to the
production rational table is a generic ring argument.
-/

namespace CourtadeKumar.TopBernsteinTransformBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem all_range_of_all_eq_true {n : Nat} {p : Nat → Bool}
    (h : (List.range n).all p = true) {i : Nat} (hi : i < n) :
    p i = true := by
  exact (List.all_eq_true.mp h) i (List.mem_range.mpr hi)

/-! ## Pointwise access to the checked finite-difference corpus -/

theorem zRowCheck_eq_true (i : Fin 48) :
    TopBernsteinFiniteDifferenceData.zRowCheck i.val = true := by
  exact all_range_of_all_eq_true (show
    (List.range 48).all TopBernsteinFiniteDifferenceData.zRowCheck = true from
    TopBernsteinFiniteDifferenceData.zDifferenceCache_reduction) i.isLt

theorem cColumnCheck_eq_true (b : Fin 23) :
    TopBernsteinFiniteDifferenceData.cColumnCheck b.val = true := by
  exact all_range_of_all_eq_true (show
    (List.range 23).all
        TopBernsteinFiniteDifferenceData.cColumnCheck = true from
    TopBernsteinFiniteDifferenceData.cDifferencePower_reduction) b.isLt

/-! ## Generic semantics of the allocation-efficient checker -/

open TopBernsteinFiniteDifferenceData

private def listValue (xs : List Int) (i : Nat) : Int :=
  (xs[i]?).getD 0

private theorem adjacentDifferencesAux_length (left : Int) (rest : List Int) :
    (adjacentDifferencesAux left rest).length = rest.length := by
  induction rest generalizing left with
  | nil => rfl
  | cons right rest ih =>
      simp [adjacentDifferencesAux, ih]

private theorem adjacentDifferences_length (xs : List Int) :
    (adjacentDifferences xs).length = xs.length - 1 := by
  cases xs with
  | nil => rfl
  | cons left rest =>
      simp [adjacentDifferences, adjacentDifferencesAux_length]

private theorem iterate_adjacentDifferences_length (r : Nat) (xs : List Int) :
    ((adjacentDifferences)^[r] xs).length = xs.length - r := by
  induction r generalizing xs with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', adjacentDifferences_length, ih]
      omega

private theorem listValue_adjacentDifferences (xs : List Int) (i : Nat)
    (hi : i + 1 < xs.length) :
    listValue (adjacentDifferences xs) i =
      listValue xs (i + 1) - listValue xs i := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hi
      | cons left rest =>
          cases rest with
          | nil => simp at hi
          | cons right rest => rfl
  | succ i ih =>
      cases xs with
      | nil => simp at hi
      | cons left rest =>
          cases rest with
          | nil => simp at hi
          | cons right rest =>
              have hi' : i + 1 < (right :: rest).length := by
                simp only [List.length_cons] at hi ⊢
                omega
              simpa [listValue, adjacentDifferences,
                adjacentDifferencesAux, Nat.succ_eq_add_one,
                Nat.add_assoc] using ih (xs := right :: rest) hi'

private theorem listValue_iterate_adjacentDifferences
    (xs : List Int) (f : Nat → Int) (r i : Nat)
    (hbound : i + r < xs.length)
    (hget : ∀ j : Nat, j < xs.length → listValue xs j = f j) :
    listValue ((adjacentDifferences)^[r] xs) i =
      (fwdDiff 1)^[r] f i := by
  induction r generalizing i with
  | zero =>
      simpa using hget i (by simpa using hbound)
  | succ r ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hi' : i + 1 < ((adjacentDifferences)^[r] xs).length := by
        rw [iterate_adjacentDifferences_length]
        omega
      rw [listValue_adjacentDifferences _ _ hi']
      rw [ih (i := i + 1) (by omega), ih (i := i) (by omega)]
      rfl

private theorem listValue_range_map (f : Nat → Int) {n i : Nat}
    (hi : i < n) :
    listValue ((List.range n).map f) i = f i := by
  unfold listValue
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem listValue_iterate_range_map (f : Nat → Int)
    {n r i : Nat} (hi : i + r < n) :
    listValue ((adjacentDifferences)^[r] ((List.range n).map f)) i =
      (fwdDiff 1)^[r] f i := by
  apply listValue_iterate_adjacentDifferences _ f r i
  · simpa using hi
  · intro j hj
    apply listValue_range_map f
    simpa using hj

private theorem zRowCheckSteps_head
    {current expected : List Int}
    (hcheck : zRowCheckSteps current expected = true)
    {r : Nat} (hr : r < expected.length) :
    listValue ((adjacentDifferences)^[r] current) 0 =
      listValue expected r := by
  induction r generalizing current expected with
  | zero =>
      cases expected with
      | nil => simp at hr
      | cons target rest =>
          cases current with
          | nil => simp [zRowCheckSteps] at hcheck
          | cons actual currentRest =>
              have hparts : actual = target ∧
                  zRowCheckSteps
                    (adjacentDifferencesAux actual currentRest) rest = true := by
                simpa [zRowCheckSteps] using hcheck
              simpa [listValue] using hparts.1
  | succ r ih =>
      cases expected with
      | nil => simp at hr
      | cons target rest =>
          cases current with
          | nil => simp [zRowCheckSteps] at hcheck
          | cons actual currentRest =>
              have hparts : actual = target ∧
                  zRowCheckSteps
                    (adjacentDifferencesAux actual currentRest) rest = true := by
                simpa [zRowCheckSteps] using hcheck
              have hr' : r < rest.length := by
                simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hr
              have hrec := ih (current :=
                adjacentDifferencesAux actual currentRest)
                (expected := rest) hparts.2 hr'
              rw [Function.iterate_succ_apply]
              change listValue
                ((adjacentDifferences)^[r]
                  (adjacentDifferencesAux actual currentRest)) 0 =
                listValue rest r
              exact hrec

private theorem zRowCheckSteps_tail_all
    {current expected : List Int}
    (hcheck : zRowCheckSteps current expected = true) :
    (((adjacentDifferences)^[expected.length] current).all
      (fun value ↦ decide (value = 0))) = true := by
  induction expected generalizing current with
  | nil => simpa [zRowCheckSteps] using hcheck
  | cons target rest ih =>
      cases current with
      | nil => simp [zRowCheckSteps] at hcheck
      | cons actual currentRest =>
          have hparts : actual = target ∧
              zRowCheckSteps
                (adjacentDifferencesAux actual currentRest) rest = true := by
            simpa [zRowCheckSteps] using hcheck
          simp only [List.length_cons]
          rw [Function.iterate_succ_apply]
          change (((adjacentDifferences)^[rest.length]
            (adjacentDifferencesAux actual currentRest)).all
              (fun value ↦ decide (value = 0))) = true
          exact ih hparts.2

private theorem adjacentDifferencesAux_all_zero
    (left : Int) (rest : List Int) (hleft : left = 0)
    (hrest : rest.all (fun value ↦ decide (value = 0)) = true) :
    (adjacentDifferencesAux left rest).all
      (fun value ↦ decide (value = 0)) = true := by
  induction rest generalizing left with
  | nil => simp [adjacentDifferencesAux]
  | cons right rest ih =>
      simp only [List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at hrest
      rcases hrest with ⟨hright, hrest⟩
      subst left
      subst right
      simp [adjacentDifferencesAux,
        ih (left := (0 : Int)) rfl hrest]

private theorem adjacentDifferences_all_zero {xs : List Int}
    (hxs : xs.all (fun value ↦ decide (value = 0)) = true) :
    (adjacentDifferences xs).all
      (fun value ↦ decide (value = 0)) = true := by
  cases xs with
  | nil => simp [adjacentDifferences]
  | cons left rest =>
      simp only [List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at hxs
      exact adjacentDifferencesAux_all_zero left rest hxs.1 hxs.2

private theorem iterate_adjacentDifferences_all_zero
    (r : Nat) {xs : List Int}
    (hxs : xs.all (fun value ↦ decide (value = 0)) = true) :
    (((adjacentDifferences)^[r] xs).all
      (fun value ↦ decide (value = 0))) = true := by
  induction r with
  | zero => simpa using hxs
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact adjacentDifferences_all_zero ih

private theorem listValue_zero_of_all_zero {xs : List Int}
    (hxs : xs.all (fun value ↦ decide (value = 0)) = true) :
    listValue xs 0 = 0 := by
  cases xs with
  | nil => rfl
  | cons value rest =>
      have hvalue : decide (value = 0) = true :=
        (List.all_eq_true.mp hxs) value (by simp)
      simpa [listValue] using (of_decide_eq_true hvalue)

private theorem zRowCheckSteps_head_zero
    {current expected : List Int}
    (hcheck : zRowCheckSteps current expected = true)
    {r : Nat} (hr : expected.length ≤ r) :
    listValue ((adjacentDifferences)^[r] current) 0 = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  have htail := zRowCheckSteps_tail_all hcheck
  have hall := iterate_adjacentDifferences_all_zero t htail
  have hzero := listValue_zero_of_all_zero hall
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hzero

private theorem cColumnCheckSteps_head
    {b a : Nat} {current expected : List Int}
    (hcheck : cColumnCheckSteps b a current expected = true)
    {r : Nat} (hr : r < expected.length) :
    (Nat.choose 47 (a + r) : Int) * (Nat.choose 60 b : Int) *
        listValue ((adjacentDifferences)^[r] current) 0 =
      listValue expected r := by
  induction r generalizing a current expected with
  | zero =>
      cases expected with
      | nil => simp at hr
      | cons target rest =>
          cases current with
          | nil => simp [cColumnCheckSteps] at hcheck
          | cons actual currentRest =>
              have hparts :
                  (Nat.choose 47 a : Int) * (Nat.choose 60 b : Int) * actual = target ∧
                    cColumnCheckSteps b (a + 1)
                      (adjacentDifferencesAux actual currentRest) rest = true := by
                simpa [cColumnCheckSteps] using hcheck
              simpa [listValue] using hparts.1
  | succ r ih =>
      cases expected with
      | nil => simp at hr
      | cons target rest =>
          cases current with
          | nil => simp [cColumnCheckSteps] at hcheck
          | cons actual currentRest =>
              have hparts :
                  (Nat.choose 47 a : Int) * (Nat.choose 60 b : Int) * actual = target ∧
                    cColumnCheckSteps b (a + 1)
                      (adjacentDifferencesAux actual currentRest) rest = true := by
                simpa [cColumnCheckSteps] using hcheck
              have hr' : r < rest.length := by
                simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hr
              have hrec := ih (a := a + 1)
                (current := adjacentDifferencesAux actual currentRest)
                (expected := rest) hparts.2 hr'
              have hindex : a + r.succ = (a + 1) + r := by omega
              rw [hindex, Function.iterate_succ_apply]
              change (Nat.choose 47 ((a + 1) + r) : Int) *
                  (Nat.choose 60 b : Int) *
                    listValue ((adjacentDifferences)^[r]
                      (adjacentDifferencesAux actual currentRest)) 0 =
                listValue rest r
              exact hrec

/-! ## Pointwise meaning of the two checked passes -/

/-- The first checker computes the unit forward differences of every input
row, including the authenticated zero tail after order 22. -/
theorem zFwdDiff_eq_expected (i : Fin 48) (b : Fin 61) :
    (fwdDiff 1)^[b.val]
        (fun j ↦ Int.ofNat (topScaledCoeff i.val j)) 0 =
      if hb : b.val < 23 then zHeadCoeff i.val b.val else 0 := by
  have hcheck :
      zRowCheckSteps
        ((List.range 61).map (fun j ↦ Int.ofNat (topScaledCoeff i.val j)))
        ((List.range 23).map (fun b ↦ zHeadCoeff i.val b)) = true := by
    simpa [zRowCheck] using zRowCheck_eq_true i
  have hsem := listValue_iterate_range_map
    (fun j ↦ Int.ofNat (topScaledCoeff i.val j))
    (n := 61) (r := b.val) (i := 0) (by simpa using b.isLt)
  by_cases hb : b.val < 23
  · have hhead := zRowCheckSteps_head hcheck (r := b.val) (by simpa using hb)
    calc
      (fwdDiff 1)^[b.val]
          (fun j ↦ Int.ofNat (topScaledCoeff i.val j)) 0 =
          listValue ((adjacentDifferences)^[b.val]
            ((List.range 61).map
              (fun j ↦ Int.ofNat (topScaledCoeff i.val j)))) 0 := hsem.symm
      _ = listValue
          ((List.range 23).map (fun b ↦ zHeadCoeff i.val b)) b.val := hhead
      _ = zHeadCoeff i.val b.val := listValue_range_map _ hb
      _ = if hb : b.val < 23 then zHeadCoeff i.val b.val else 0 := by simp [hb]
  · have hzero := zRowCheckSteps_head_zero hcheck (r := b.val)
        (by simpa using Nat.le_of_not_gt hb)
    calc
      (fwdDiff 1)^[b.val]
          (fun j ↦ Int.ofNat (topScaledCoeff i.val j)) 0 =
          listValue ((adjacentDifferences)^[b.val]
            ((List.range 61).map
              (fun j ↦ Int.ofNat (topScaledCoeff i.val j)))) 0 := hsem.symm
      _ = 0 := hzero
      _ = if hb : b.val < 23 then zHeadCoeff i.val b.val else 0 := by simp [hb]

/-- The second checker computes every supported mixed power coefficient from
the cached first-pass heads. -/
theorem cFwdDiff_eq_scaledPower (a : Fin 48) (b : Fin 23) :
    (Nat.choose 47 a.val : Int) * (Nat.choose 60 b.val : Int) *
        (fwdDiff 1)^[a.val] (fun i ↦ zHeadCoeff i b.val) 0 =
      scaledPowerCoeff a.val b.val := by
  have hcheck :
      cColumnCheckSteps b.val 0
        ((List.range 48).map (fun i ↦ zHeadCoeff i b.val))
        ((List.range 48).map (fun a ↦ scaledPowerCoeff a b.val)) = true := by
    simpa [cColumnCheck, zHeadColumn, scaledPowerColumn] using
      cColumnCheck_eq_true b
  have hhead := cColumnCheckSteps_head hcheck (r := a.val)
    (by simpa using a.isLt)
  have hsem := listValue_iterate_range_map
    (fun i ↦ zHeadCoeff i b.val)
    (n := 48) (r := a.val) (i := 0) (by simpa using a.isLt)
  calc
    (Nat.choose 47 a.val : Int) * (Nat.choose 60 b.val : Int) *
        (fwdDiff 1)^[a.val] (fun i ↦ zHeadCoeff i b.val) 0 =
      (Nat.choose 47 a.val : Int) * (Nat.choose 60 b.val : Int) *
        listValue ((adjacentDifferences)^[a.val]
          ((List.range 48).map (fun i ↦ zHeadCoeff i b.val))) 0 := by rw [hsem]
    _ = listValue
        ((List.range 48).map (fun a ↦ scaledPowerCoeff a b.val)) a.val := by
          simpa only [Nat.zero_add] using hhead
    _ = scaledPowerCoeff a.val b.val := listValue_range_map _ a.isLt

/-! ## Generic Bernstein-transform soundness -/

private def signedBinomialDifference {R : Type} [CommRing R]
    (order : Nat) (f : Nat → R) : R :=
  ∑ k ∈ Finset.range (order + 1),
    (-1 : R) ^ (order - k) * (Nat.choose order k : R) * f k

private theorem signedBinomialDifference_eq_iterated_fwdDiff
    {R : Type} [CommRing R] (order : Nat) (f : Nat → R) :
    signedBinomialDifference order f = (fwdDiff 1)^[order] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [signedBinomialDifference, zero_add, nsmul_eq_mul, mul_one,
    zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  rfl

private theorem signedBinomialDifference_congr
    {R : Type} [CommRing R] {order : Nat} {f g : Nat → R}
    (h : ∀ k : Nat, k < order + 1 → f k = g k) :
    signedBinomialDifference order f = signedBinomialDifference order g := by
  unfold signedBinomialDifference
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Finset.mem_range.mp hk)]

private theorem fwdDiff_iter_zero_congr
    {R : Type} [CommRing R] {order : Nat} {f g : Nat → R}
    (h : ∀ k : Nat, k < order + 1 → f k = g k) :
    (fwdDiff 1)^[order] f 0 = (fwdDiff 1)^[order] g 0 := by
  rw [← signedBinomialDifference_eq_iterated_fwdDiff order f,
    ← signedBinomialDifference_eq_iterated_fwdDiff order g]
  exact signedBinomialDifference_congr h

private theorem tensorBernsteinPowerCoeff_eq_signedBinomialDifference
    {R : Type} [CommRing R] {m n : Nat}
    (p : Fin (m + 1) → Fin (n + 1) → R) (a b : Nat) :
    tensorBernsteinPowerCoeff p a b =
      (Nat.choose m a : R) * (Nat.choose n b : R) *
        signedBinomialDifference a (fun i ↦
          signedBinomialDifference b (fun j ↦ finTableGet p i j)) := by
  classical
  unfold tensorBernsteinPowerCoeff signedBinomialDifference
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hia : i ≤ a := by
    have : i < a + 1 := Finset.mem_range.mp hi
    omega
  have hjb : j ≤ b := by
    have : j < b + 1 := Finset.mem_range.mp hj
    omega
  have hm := congrArg (fun x : Nat ↦ (x : R))
    (Nat.choose_mul (n := m) (k := a) (s := i) hia)
  have hn := congrArg (fun x : Nat ↦ (x : R))
    (Nat.choose_mul (n := n) (k := b) (s := j) hjb)
  simp only [Nat.cast_mul] at hm hn
  unfold tensorBernsteinPowerSummand
  rw [← hm, ← hn]
  ring

/-- Generic tensor Bernstein-to-power conversion stated directly in terms of
the same iterated forward differences used by the fast checker. -/
theorem tensorBernsteinPowerCoeff_eq_iterated_fwdDiff
    {R : Type} [CommRing R] {m n : Nat}
    (p : Fin (m + 1) → Fin (n + 1) → R) (a b : Nat) :
    tensorBernsteinPowerCoeff p a b =
      (Nat.choose m a : R) * (Nat.choose n b : R) *
        (fwdDiff 1)^[a]
          (fun i ↦ (fwdDiff 1)^[b] (fun j ↦ finTableGet p i j) 0) 0 := by
  calc
    tensorBernsteinPowerCoeff p a b =
        (Nat.choose m a : R) * (Nat.choose n b : R) *
          signedBinomialDifference a (fun i ↦
            signedBinomialDifference b (fun j ↦ finTableGet p i j)) :=
      tensorBernsteinPowerCoeff_eq_signedBinomialDifference p a b
    _ = (Nat.choose m a : R) * (Nat.choose n b : R) *
        (fwdDiff 1)^[a]
          (fun i ↦ signedBinomialDifference b (fun j ↦ finTableGet p i j)) 0 := by
            rw [signedBinomialDifference_eq_iterated_fwdDiff]
    _ = (Nat.choose m a : R) * (Nat.choose n b : R) *
        (fwdDiff 1)^[a]
          (fun i ↦ (fwdDiff 1)^[b] (fun j ↦ finTableGet p i j) 0) 0 := by
            apply congrArg (fun x : R ↦
              (Nat.choose m a : R) * (Nat.choose n b : R) * x)
            apply congrArg (fun f : Nat → R ↦ (fwdDiff 1)^[a] f 0)
            funext i
            exact signedBinomialDifference_eq_iterated_fwdDiff _ _

/-! ## Soundness of the concrete integer replay -/

/-- The scaled TOP input, regarded as a signed integer table. -/
def scaledInputTable (i : Fin 48) (j : Fin 61) : Int :=
  Int.ofNat (topScaledCoeff i.val j.val)

private theorem finTableGet_scaledInputTable {i j : Nat}
    (hi : i < 48) (hj : j < 61) :
    finTableGet scaledInputTable i j = Int.ofNat (topScaledCoeff i j) := by
  simp [finTableGet, scaledInputTable, hi, hj]

/-- The two fast, kernel-checked adjacent-difference passes compute the exact
tensor Bernstein-to-power transform of the scaled input table. -/
theorem scaledInput_tensorBernsteinPowerCoeff_eq_checked
    (a : Fin 48) (b : Fin 61) :
    tensorBernsteinPowerCoeff (p := scaledInputTable) a.val b.val =
      if hb : b.val < 23 then scaledPowerCoeff a.val b.val else 0 := by
  rw [tensorBernsteinPowerCoeff_eq_iterated_fwdDiff]
  have hinner : ∀ i : Nat, i < a.val + 1 →
      (fwdDiff 1)^[b.val] (fun j ↦ finTableGet scaledInputTable i j) 0 =
        if hb : b.val < 23 then zHeadCoeff i b.val else 0 := by
    intro i hi
    have hi48 : i < 48 := by omega
    calc
      (fwdDiff 1)^[b.val] (fun j ↦ finTableGet scaledInputTable i j) 0 =
          (fwdDiff 1)^[b.val]
            (fun j ↦ Int.ofNat (topScaledCoeff i j)) 0 := by
              apply fwdDiff_iter_zero_congr
              intro j hj
              have hj61 : j < 61 := by omega
              rw [finTableGet_scaledInputTable hi48 hj61]
      _ = if hb : b.val < 23 then zHeadCoeff i b.val else 0 :=
        zFwdDiff_eq_expected ⟨i, hi48⟩ b
  by_cases hb : b.val < 23
  · have houter :
        (fwdDiff 1)^[a.val]
            (fun i ↦ (fwdDiff 1)^[b.val]
              (fun j ↦ finTableGet scaledInputTable i j) 0) 0 =
          (fwdDiff 1)^[a.val] (fun i ↦ zHeadCoeff i b.val) 0 := by
      apply fwdDiff_iter_zero_congr
      intro i hi
      simpa [hb] using hinner i hi
    calc
      (Nat.choose 47 a.val : Int) * (Nat.choose 60 b.val : Int) *
          (fwdDiff 1)^[a.val]
            (fun i ↦ (fwdDiff 1)^[b.val]
              (fun j ↦ finTableGet scaledInputTable i j) 0) 0 =
          (Nat.choose 47 a.val : Int) * (Nat.choose 60 b.val : Int) *
            (fwdDiff 1)^[a.val] (fun i ↦ zHeadCoeff i b.val) 0 := by rw [houter]
      _ = scaledPowerCoeff a.val b.val :=
        cFwdDiff_eq_scaledPower a ⟨b.val, hb⟩
      _ = if hb : b.val < 23 then scaledPowerCoeff a.val b.val else 0 := by
        simp [hb]
  · have houter :
        (fwdDiff 1)^[a.val]
            (fun i ↦ (fwdDiff 1)^[b.val]
              (fun j ↦ finTableGet scaledInputTable i j) 0) 0 = 0 := by
      calc
        (fwdDiff 1)^[a.val]
            (fun i ↦ (fwdDiff 1)^[b.val]
              (fun j ↦ finTableGet scaledInputTable i j) 0) 0 =
            (fwdDiff 1)^[a.val] (fun _ ↦ (0 : Int)) 0 := by
              apply fwdDiff_iter_zero_congr
              intro i hi
              simpa [hb] using hinner i hi
        _ = 0 := by simp [fwdDiff_iter_eq_sum_shift]
    simp [houter, hb]

/-! ## Passage from the integer table to the production rational table -/

private theorem scaledInput_tensorBernsteinPowerCoeff_cast (a b : Nat) :
    ((tensorBernsteinPowerCoeff
        (p := scaledInputTable) a b : Int) : ℚ) =
      tensorBernsteinPowerCoeff
        (p := fun i j ↦ (scaledInputTable i j : ℚ)) a b := by
  classical
  unfold tensorBernsteinPowerCoeff tensorBernsteinPowerSummand finTableGet
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases him : i < 48 <;> by_cases hjn : j < 61 <;>
    simp [scaledInputTable, him, hjn]

private theorem tensorBernsteinPowerCoeff_const_mul
    {R : Type} [CommRing R] {m n : Nat}
    (d : R) (p : Fin (m + 1) → Fin (n + 1) → R) (a b : Nat) :
    tensorBernsteinPowerCoeff (p := fun i j ↦ d * p i j) a b =
      d * tensorBernsteinPowerCoeff (p := p) a b := by
  classical
  unfold tensorBernsteinPowerCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold tensorBernsteinPowerSummand finTableGet
  split_ifs <;> ring

/-- Casting the integer transform to `ℚ` is exactly multiplication of the
production rational transform by the common denominator. -/
theorem scaledInput_tensorBernsteinPowerCoeff_cast_eq_scaled
    (a b : Nat) :
    ((tensorBernsteinPowerCoeff
        (p := scaledInputTable) a b : Int) : ℚ) =
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
        tensorBernsteinPowerCoeff
          (p := fun i j ↦ topElevatedBernsteinCoeff i j) a b := by
  have htable :
      (fun i j ↦ (scaledInputTable i j : ℚ)) =
        (fun i j ↦
          (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
            topElevatedBernsteinCoeff i j) := by
    funext i j
    simpa [scaledInputTable] using topScaledCoeff_decode i j
  calc
    ((tensorBernsteinPowerCoeff
        (p := scaledInputTable) a b : Int) : ℚ) =
        tensorBernsteinPowerCoeff
          (p := fun i j ↦ (scaledInputTable i j : ℚ)) a b :=
      scaledInput_tensorBernsteinPowerCoeff_cast a b
    _ = tensorBernsteinPowerCoeff
          (p := fun i j ↦
            (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
              topElevatedBernsteinCoeff i j) a b := by rw [htable]
    _ = (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
        tensorBernsteinPowerCoeff
          (p := fun i j ↦ topElevatedBernsteinCoeff i j) a b :=
      tensorBernsteinPowerCoeff_const_mul _ _ _ _

/-- The missing scaled-transform hypothesis, now discharged entirely by the
kernel-checked integer replay and generic ring identities. -/
theorem topScaledTransform_sound :
    ∀ i : Fin 48, ∀ j : Fin 61,
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
          tensorBernsteinPowerCoeff
            (p := fun a b ↦ topElevatedBernsteinCoeff a b) i.val j.val =
        if hj : j.val < 23 then
          (TopBernsteinFiniteDifferenceData.scaledPowerCoeff i.val j.val : Int)
        else 0 := by
  intro i j
  have hint := scaledInput_tensorBernsteinPowerCoeff_eq_checked i j
  calc
    (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
        tensorBernsteinPowerCoeff
          (p := fun a b ↦ topElevatedBernsteinCoeff a b) i.val j.val =
        ((tensorBernsteinPowerCoeff
          (p := scaledInputTable) i.val j.val : Int) : ℚ) :=
      (scaledInput_tensorBernsteinPowerCoeff_cast_eq_scaled i.val j.val).symm
    _ = ((if hj : j.val < 23 then
        TopBernsteinFiniteDifferenceData.scaledPowerCoeff i.val j.val else 0 : Int) : ℚ) := by
      rw [hint]
    _ = if hj : j.val < 23 then
        (TopBernsteinFiniteDifferenceData.scaledPowerCoeff i.val j.val : Int) else 0 := by
      by_cases hj : j.val < 23 <;> simp [hj]

/-! ## Final denominator-cancellation seam

The hypothesis below is precisely the remaining generic soundness theorem:
the checked two-pass finite-difference computation is the scaled tensor
Bernstein-to-power transform.  Keeping this lemma separate prevents any
literal-table arithmetic from leaking into the later analytic proof.
-/

theorem topBernsteinPowerCoeff_eq_certificate_of_scaled_transform
    (hscaled : ∀ i : Fin 48, ∀ j : Fin 61,
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
          tensorBernsteinPowerCoeff
            (p := fun a b => topElevatedBernsteinCoeff a b) i.val j.val =
        if hj : j.val < 23 then
          (TopBernsteinFiniteDifferenceData.scaledPowerCoeff i.val j.val : Int)
        else 0) :
    ∀ i : Fin 48, ∀ j : Fin 61,
      tensorBernsteinPowerCoeff
          (p := fun a b => topElevatedBernsteinCoeff a b) i.val j.val =
        topCertificatePowerCoeffRat i j := by
  intro i j
  have hD : (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) ≠ 0 := by
    norm_num [TopBernsteinFiniteDifferenceData.commonDenominator]
  apply mul_left_cancel₀ hD
  by_cases hj : j.val < 23
  · calc
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
          tensorBernsteinPowerCoeff
            (p := fun a b => topElevatedBernsteinCoeff a b) i.val j.val =
          (TopBernsteinFiniteDifferenceData.scaledPowerCoeff i.val j.val : Int) := by
            simpa [hj] using hscaled i j
      _ = (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
          topCertificatePowerCoeffRat i j := by
            simpa using
              scaledPowerCoeff_decode i ⟨j.val, hj⟩
  · calc
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
          tensorBernsteinPowerCoeff
            (p := fun a b => topElevatedBernsteinCoeff a b) i.val j.val = 0 := by
            simpa [hj] using hscaled i j
      _ = (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
          topCertificatePowerCoeffRat i j := by
            simp [topCertificatePowerCoeffRat, hj]

/-- Kernel-only replacement for the historical `native_decide` transform
theorem. -/
theorem topBernsteinPowerCoeff_eq_certificate_kernel :
    ∀ i : Fin 48, ∀ j : Fin 61,
      tensorBernsteinPowerCoeff
          (p := fun a b ↦ topElevatedBernsteinCoeff a b) i.val j.val =
        topCertificatePowerCoeffRat i j :=
  topBernsteinPowerCoeff_eq_certificate_of_scaled_transform
    topScaledTransform_sound

end CourtadeKumar.TopBernsteinTransformBridge

namespace CourtadeKumar

/-- Kernel-only public replacement for the historical compiler-backed TOP
Bernstein transform theorem. -/
theorem topBernsteinPowerCoeff_eq_certificate :
    ∀ i : Fin 48, ∀ j : Fin 61,
      tensorBernsteinPowerCoeff
          (p := fun a b ↦ topElevatedBernsteinCoeff a b) i.val j.val =
        topCertificatePowerCoeffRat i j :=
  TopBernsteinTransformBridge.topBernsteinPowerCoeff_eq_certificate_kernel

end CourtadeKumar
