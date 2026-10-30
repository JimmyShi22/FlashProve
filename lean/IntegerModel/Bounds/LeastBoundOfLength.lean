-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LeastBoundOfLength.lean

Whatever passes the length check passes the least-bound check with the matching numbers.

Two worst-case checks with given stretch numbers stand in this folder: `lengthWorstCaseCheck`
(IntegerModel/Bounds/LengthCheck.lean) and `leastBoundWorstCaseCheck`
(IntegerModel/Bounds/LeastBoundCheck.lean), which takes at each place the least of several bounds.
This file ties them.

- `leastBoundNumbersOf settings tables weights taus numbers`: the numbers for the least-bound check
  that match given `StretchNumbers`. They have the same five kinds of number; for an up matrix with
  scaled columns the SiLU table's largest entry times the up matrix's number; for a value head's
  columns their Frobenius norm; and any list of taus.
- `leastBoundNumbersOf_hold`: if the stretch numbers hold, the matching numbers hold.
- `leastBoundWorstCaseCheck_of_lengthWorstCaseCheck`: if no stretch number is negative
  (`StretchNumbers.NonNegative`, which follows from `Hold`) and the length check passes, the
  least-bound check passes with the matching numbers, for every list of taus.
- `frobeniusLeastBoundCheck_of_frobeniusLengthCheck`: the same for the two checks' Frobenius
  numbers, of which the ones match the others (`leastBoundNumbersOf_frobenius`): a statement on two
  tests alone.

The proof: each bound of the least-bound check is at most its counterpart in the length check. The
ball whose radius is a fraction lies in the ball of the whole radius (part 1), so the bounds on the
sums of products are no larger (parts 1 and 2); each minimum of the least-bound check has the length
check's bound among its members (part 4); and by induction over the layers the least-bound check's
bound on the stream is not negative and at most the length check's (`leastStreamLength_le`, part 5).
Every test of the two checks passes at a smaller bound if it passes at a larger one.

Limits. The theorems go one way: nothing is said here of weights that pass the least-bound check.
Alone neither test says anything of the weights: both use their given numbers and do not test them.
This file says of no weights that they pass. Only Lean's core library is used.
-/
import IntegerModel.Bounds.LeastBoundNeverFails
import IntegerModel.Bounds.UniformLengthCheck

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. The fine ball is inside the whole one -/

/-- The least over a list is at most the start. -/
theorem leastOver_le_start (taus : List Int) (f : Int → Int) (start : Int) :
    leastOver taus f start ≤ start := by
  induction taus with
  | nil => exact Int.le_refl _
  | cons tau rest ih =>
    simp only [leastOver]
    omega

/-- The root of `w * m^2`, rounded up, is at most `m` times the root of `w`, rounded up. -/
theorem rootUp_scaled_le (w m : Int) (nonneg : 0 ≤ w) (positive : 0 < m) :
    rootUp (w * (m * m)) ≤ m * rootUp w := by
  have product : 0 ≤ w * (m * m) := Int.mul_nonneg nonneg (Int.mul_nonneg (by omega) (by omega))
  have low := (isqrt_spec (w * (m * m)).toNat).1
  have high := (isqrt_spec w.toNat).2
  unfold rootUp
  generalize integerSquareRoot (w * (m * m)).toNat = q at *
  generalize integerSquareRoot w.toNat = r at *
  have lowInt : (q : Int) * q ≤ w * (m * m) := by
    have : ((q * q : Nat) : Int) ≤ ((w * (m * m)).toNat : Int) := Int.ofNat_le.mpr low
    push_cast at this
    omega
  have highInt : w < ((r : Int) + 1) * ((r : Int) + 1) := by
    have : ((w.toNat : Nat) : Int) < (((r + 1) * (r + 1) : Nat) : Int) := Int.ofNat_lt.mpr high
    push_cast at this
    omega
  have scaled : w * (m * m) < ((r : Int) + 1) * ((r : Int) + 1) * (m * m) :=
    Int.mul_lt_mul_of_pos_right highInt (Int.mul_pos positive positive)
  apply Int.le_of_not_gt
  intro above
  have least : m * ((r : Int) + 1) ≤ q := by omega
  have base : 0 ≤ m * ((r : Int) + 1) := Int.mul_nonneg (by omega) (by omega)
  have squares := Int.mul_le_mul least least base (by omega)
  have same : m * ((r : Int) + 1) * (m * ((r : Int) + 1)) =
      ((r : Int) + 1) * ((r : Int) + 1) * (m * m) := by grind
  omega

/-- The numerator of a norm's ball is not negative. -/
theorem normBall_numerator_nonneg (width bits shift : Nat) (eps rowLength : Int) :
    0 ≤ (normBall width bits shift eps rowLength).numerator := by
  have power : (0 : Int) < 2 ^ bits := Int.pow_pos (by decide)
  have quotient : 0 ≤ (2 : Int) ^ bits / (integerSquareRoot eps.toNat : Int) :=
    Int.ediv_nonneg (Int.le_of_lt power) (by omega)
  have root := (rootUp_spec ((width : Int) * (2 ^ (shift - 1) * 2 ^ (shift - 1)))).1
  simp only [normBall]
  omega

/-- The radius of a norm's ball, rounded up, is at most `ballRadius`. -/
theorem normBall_radius_le (width bits shift : Nat) (eps rowLength : Int) :
    (normBall width bits shift eps rowLength).radius ≤
      ballRadius width bits shift eps rowLength := by
  have half : (0 : Int) < 2 ^ (shift - 1) := Int.pow_pos (by decide)
  have root := rootUp_scaled_le (width : Int) (2 ^ (shift - 1)) (by omega) half
  unfold Ball.radius ballRadius
  simp only [normBall]
  exact shiftUp_le_shiftUp _ _ _ (by omega)

/-- The fine ball's bound on a column's sum is at most the bound of a whole radius that is no
smaller. -/
theorem fineBallColumnBound_le (ball : Ball) (radius : Int) (W : Matrix) (rows column : Nat)
    (nonneg : 0 ≤ ball.numerator) (le : ball.radius ≤ radius) :
    fineBallColumnBound ball W rows column ≤ ballColumnBound radius W rows column := by
  have power : (0 : Int) < 2 ^ ball.shift := Int.pow_pos (by decide)
  have squares : 0 ≤ columnSquares W rows column := sumSquaresOver_nonneg _ _
  have covered : ball.numerator ≤ 2 ^ ball.shift * radius :=
    Int.le_trans (shiftUp_spec _ _) (Int.mul_le_mul_of_nonneg_left le (Int.le_of_lt power))
  unfold fineBallColumnBound ballColumnBound
  generalize columnSquares W rows column = Y at *
  generalize ball.numerator = N at *
  generalize (2 : Int) ^ ball.shift = D at *
  have inner : 0 ≤ N * N * Y := Int.mul_nonneg (Int.mul_nonneg nonneg nonneg) squares
  have low := (isqrt_spec (N * N * Y).toNat).1
  generalize integerSquareRoot (N * N * Y).toNat = t at *
  have lowInt : (t : Int) * t ≤ N * N * Y := by
    have : ((t * t : Nat) : Int) ≤ ((N * N * Y).toNat : Int) := Int.ofNat_le.mpr low
    push_cast at this
    omega
  have quotientNonneg : 0 ≤ (t : Int) / D := Int.ediv_nonneg (by omega) (by omega)
  have below : (t : Int) / D * D ≤ t := Int.ediv_mul_le _ (by omega)
  generalize (t : Int) / D = q at *
  have first : q * D * (q * D) ≤ (t : Int) * t :=
    Int.mul_le_mul below below (Int.mul_nonneg quotientNonneg (by omega)) (by omega)
  have second : N * N ≤ D * radius * (D * radius) :=
    Int.mul_le_mul covered covered nonneg (by omega)
  have third := Int.mul_le_mul_of_nonneg_right second squares
  have e1 : q * D * (q * D) = D * D * (q * q) := by grind
  have e2 : D * radius * (D * radius) * Y = D * D * (radius * radius * Y) := by grind
  have cancel : q * q ≤ radius * radius * Y :=
    Int.le_of_mul_le_mul_left (by omega : D * D * (q * q) ≤ D * D * (radius * radius * Y))
      (Int.mul_pos power power)
  have := magnitude_le_isqrt cancel
  rw [magnitude_le_iff] at this
  exact this.2

/-- The least bound on a column's sum is at most `columnBoundInBall` at a whole radius that is no
smaller. -/
theorem leastColumnBound_le (taus : List Int) (ball : Ball) (radius : Int) (W : Matrix)
    (rows column : Nat) (nonneg : 0 ≤ ball.numerator) (le : ball.radius ≤ radius) :
    leastColumnBound taus ball W rows column ≤ columnBoundInBall radius W rows column := by
  have start := leastOver_le_start taus (fun tau => dualColumnBound ball tau W rows column)
    (min (boxColumnBound W rows column) (fineBallColumnBound ball W rows column))
  have fine := fineBallColumnBound_le ball radius W rows column nonneg le
  unfold leastColumnBound columnBoundInBall
  omega

/-! ## 2. Conditions 3 to 7 -/

/-- `rotatedBound` does not fall when the products' bounds grow. -/
theorem rotatedBound_le_rotatedBound (cosine sine : IntegerVector) (headDim : Nat)
    (smaller larger : Nat → Int) (le : ∀ j, smaller j ≤ larger j) (j : Nat) :
    rotatedBound cosine sine headDim smaller j ≤ rotatedBound cosine sine headDim larger j := by
  unfold rotatedBound
  dsimp only
  split
  · exact Int.add_le_add (Int.mul_le_mul_of_nonneg_left (le _) (magnitude_nonneg _))
      (Int.mul_le_mul_of_nonneg_left (le _) (magnitude_nonneg _))
  · exact Int.add_le_add (Int.mul_le_mul_of_nonneg_left (le _) (magnitude_nonneg _))
      (Int.mul_le_mul_of_nonneg_left (le _) (magnitude_nonneg _))

/-- The least-bound check's bound on a rotated product is at most the length check's. -/
theorem leastRotatedBound_le (cosine sine : IntegerVector) (headDim : Nat) (taus : List Int) (ball : Ball)
    (radius : Int) (W : Matrix) (rows j : Nat) (nonneg : 0 ≤ ball.numerator)
    (le : ball.radius ≤ radius) :
    leastRotatedBound cosine sine headDim taus ball W rows j ≤
      rotatedBound cosine sine headDim (columnBoundInBall radius W rows) j := by
  have least := rotatedBound_le_rotatedBound cosine sine headDim (leastColumnBound taus ball W rows)
    (columnBoundInBall radius W rows)
    (fun c => leastColumnBound_le taus ball radius W rows c nonneg le) j
  unfold leastRotatedBound
  omega

/-- Conditions 3 and 4: the least-bound check's test passes where the length check's does. -/
theorem attentionFitsLeastBound_of_inBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (taus : List Int) (ball : Ball) (radius : Int)
    (nonneg : 0 ≤ ball.numerator) (le : ball.radius ≤ radius)
    (fits : attentionFitsInBall s p tables w radius = true) :
    attentionFitsLeastBound s p tables w taus ball = true := by
  simp only [attentionFitsInBall, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at fits
  simp only [attentionFitsLeastBound, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
  refine ⟨fun t ht => ⟨fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_⟩
  · exact Int.le_trans (roundShift_le_roundShift _ _ _
      (leastRotatedBound_le _ _ _ taus ball radius w.query s.width j nonneg le))
      ((fits.1 t ht).1 j hj)
  · exact Int.le_trans (roundShift_le_roundShift _ _ _
      (leastRotatedBound_le _ _ _ taus ball radius w.key s.width j nonneg le))
      ((fits.1 t ht).2 j hj)
  · exact Int.le_trans (roundShift_le_roundShift _ _ _
      (leastColumnBound_le taus ball radius w.value s.width j nonneg le)) (fits.2 j hj)

/-- Conditions 6 and 7: the least-bound check's test passes where the length check's does. -/
theorem unitsFitLeastBound_of_inBall (w : GatedWeights) (width hidden gateShift upShift : Nat)
    (taus : List Int) (ball : Ball) (radius : Int) (nonneg : 0 ≤ ball.numerator)
    (le : ball.radius ≤ radius)
    (fits : unitsFitInBall w width hidden gateShift upShift radius = true) :
    unitsFitLeastBound w width hidden gateShift upShift taus ball = true := by
  simp only [unitsFitInBall, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at fits
  simp only [unitsFitLeastBound, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
  exact fun j hj =>
    ⟨Int.le_trans (roundShift_le_roundShift _ _ _
      (leastColumnBound_le taus ball radius w.gate width j nonneg le)) (fits j hj).1,
    Int.le_trans (roundShift_le_roundShift _ _ _
      (leastColumnBound_le taus ball radius w.up width j nonneg le)) (fits j hj).2⟩

/-- Conditions 5, 6 and 7: the least-bound check's test passes where the length check's does. -/
theorem feedForwardFitsLeastBound_of_inBall (s : Settings) (p : LayerSettings) (w : LayerWeights)
    (mixture : Bool) (taus : List Int) (ball : Ball) (radius : Int)
    (nonneg : 0 ≤ ball.numerator) (le : ball.radius ≤ radius)
    (fits : feedForwardFitsInBall s p w mixture radius = true) :
    feedForwardFitsLeastBound s p w mixture taus ball = true := by
  cases mixture with
  | false =>
    simp only [feedForwardFitsInBall, Bool.false_eq_true, if_false] at fits
    simp only [feedForwardFitsLeastBound, Bool.false_eq_true, if_false]
    exact unitsFitLeastBound_of_inBall _ _ _ _ _ taus ball radius nonneg le fits
  | true =>
    simp only [feedForwardFitsInBall, if_true, Bool.and_eq_true, allBelow_spec,
      decide_eq_true_eq] at fits
    simp only [feedForwardFitsLeastBound, if_true, Bool.and_eq_true, allBelow_spec,
      decide_eq_true_eq]
    exact ⟨unitsFitLeastBound_of_inBall _ _ _ _ _ taus ball radius nonneg le fits.1, fun e he =>
      ⟨Int.le_trans (roundShift_le_roundShift _ _ _
        (leastColumnBound_le taus ball radius w.router s.width e nonneg le)) (fits.2 e he).1,
      unitsFitLeastBound_of_inBall _ _ _ _ _ taus ball radius nonneg le (fits.2 e he).2⟩⟩

/-! ## 3. The matching numbers -/

/-- The numbers for `leastBoundWorstCaseCheck` that match given `StretchNumbers`: the same five
kinds of number; for an up matrix with scaled columns the SiLU table's largest entry times the up
matrix's number; for a value head's columns their Frobenius norm; any list of taus. -/
def leastBoundNumbersOf (settings : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) (numbers : StretchNumbers) : LeastBoundNumbers where
  taus := taus
  output := numbers.output
  valueHead layer keyValueHead :=
    frobeniusStretchOf
      (fun row coordinate => ((weights.perLayer.entry layer).value.entry row).entry
        (keyValueHead * settings.headDim + coordinate))
      settings.width settings.headDim
  up := numbers.up
  scaledUp layer := largestMagnitude tables.silu.entries * numbers.up layer
  down := numbers.down
  routedUp := numbers.routedUp
  routedScaledUp layer expert :=
    largestMagnitude tables.silu.entries * numbers.routedUp layer expert
  routedDown := numbers.routedDown

/-- **If stretch numbers hold, the matching numbers hold.** -/
theorem leastBoundNumbersOf_hold (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) (numbers : StretchNumbers) (holds : numbers.Hold s weights) :
    (leastBoundNumbersOf s tables weights taus numbers).Hold s tables weights :=
  fun l hl =>
    ⟨(holds l hl).1, fun _ _ => stretchBoundOf_frobenius _ _ _,
      ⟨(holds l hl).2.1, stretch_scaled_columns _ _ _ _ _ _ _ _ (holds l hl).2.1,
        (holds l hl).2.2.1⟩,
      fun mixture e he =>
        ⟨((holds l hl).2.2.2 mixture e he).1,
          stretch_scaled_columns _ _ _ _ _ _ _ _ ((holds l hl).2.2.2 mixture e he).1,
          ((holds l hl).2.2.2 mixture e he).2⟩⟩

/-- No number that the check reads is negative. -/
def StretchNumbers.NonNegative (numbers : StretchNumbers) (settings : Settings) : Prop :=
  ∀ layer, layer < settings.layers →
    0 ≤ numbers.output layer ∧ 0 ≤ numbers.up layer ∧ 0 ≤ numbers.down layer
    ∧ (settings.isMixture layer = true → ∀ expert, expert < settings.experts →
      0 ≤ numbers.routedUp layer expert ∧ 0 ≤ numbers.routedDown layer expert)

/-- Stretch numbers that hold are not negative. -/
theorem nonNegative_of_hold (s : Settings) (weights : Weights) (numbers : StretchNumbers)
    (holds : numbers.Hold s weights) : numbers.NonNegative s :=
  fun l hl =>
    ⟨(holds l hl).1.1, (holds l hl).2.1.1, (holds l hl).2.2.1.1, fun mixture e he =>
      ⟨((holds l hl).2.2.2 mixture e he).1.1, ((holds l hl).2.2.2 mixture e he).2.1⟩⟩

/-! ## 4. The additions' lengths -/

/-- What attention adds: the least-bound check's bound is not negative and at most the length
check's. -/
theorem leastAttentionAdditionLength_le (s : Settings) (p : LayerSettings) (w : LayerWeights)
    (taus : List Int) (ball : Ball) (stretchOf : Nat → Int) (stretch : Int) (nonneg : 0 ≤ stretch) :
    0 ≤ leastAttentionAdditionLength s p w taus ball stretchOf stretch ∧
      leastAttentionAdditionLength s p w taus ball stretchOf stretch ≤
        attentionAdditionLength s p stretch := by
  have box : 0 ≤ mixedLength s := (rootUp_spec _).1
  have heads := (rootUp_spec
    (sumSquaresOver s.queryHeads fun h => headOutLength s p w taus ball stretchOf h)).1
  have mixed : 0 ≤ leastMixedLength s p w taus ball stretchOf ∧
      leastMixedLength s p w taus ball stretchOf ≤ mixedLength s := by
    unfold leastMixedLength
    omega
  have product := mul_le_mul_of_bounds _ _ _ _ nonneg mixed.1 (Int.le_refl _) mixed.2
  exact ⟨roundedLength_nonneg _ _ _ product.1, roundedLength_le _ _ _ _ product.2⟩

/-- The products of one block: the least-bound check's bound, with the matching number for the
scaled columns, is not negative and at most the length check's at a whole radius that is no smaller.
-/
theorem leastHiddenLength_le (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (taus : List Int) (ball : Ball) (stretchUp radius : Int)
    (stretchNonneg : 0 ≤ stretchUp) (radiusNonneg : 0 ≤ ball.radius) (le : ball.radius ≤ radius) :
    0 ≤ leastHiddenLength tables w width hidden gateShift upShift taus ball stretchUp
        (largestMagnitude tables.silu.entries * stretchUp) ∧
      leastHiddenLength tables w width hidden gateShift upShift taus ball stretchUp
        (largestMagnitude tables.silu.entries * stretchUp) ≤
          hiddenLength tables hidden upShift stretchUp radius := by
  have lengthBound := hiddenLength_le tables hidden upShift stretchUp ball.radius
    (largestMagnitude tables.silu.entries) stretchUp radius (Int.le_refl _) stretchNonneg
    (Int.le_refl _) radiusNonneg le
  have same : uniformHiddenLength (largestMagnitude tables.silu.entries) hidden upShift stretchUp
      radius = hiddenLength tables hidden upShift stretchUp radius := rfl
  rw [same] at lengthBound
  have entrywise := (rootUp_spec (sumSquaresOver hidden fun j =>
    siluAt tables w width gateShift taus ball j * upAt w width upShift taus ball j)).1
  have half : (0 : Int) < 2 ^ (upShift - 1) := Int.pow_pos (by decide)
  have rounding := Int.mul_nonneg (Int.le_of_lt half)
    (rootUp_spec (sumSquaresOver hidden (siluAt tables w width gateShift taus ball))).1
  have scaled := Int.mul_nonneg
    (Int.mul_nonneg (largestMagnitude_nonneg tables.silu.entries) stretchNonneg) radiusNonneg
  have stretched : 0 ≤ stretchedHiddenLength (siluAt tables w width gateShift taus ball) hidden
      upShift (largestMagnitude tables.silu.entries * stretchUp) ball.radius :=
    shiftUp_nonneg (by omega) _
  unfold leastHiddenLength
  omega

/-- What a feed-forward block adds: the least-bound check's bound with the matching numbers is not
negative and at most the length check's at a whole radius that is no smaller. -/
theorem leastFeedForwardAdditionLength_le (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) (numbers : StretchNumbers) (l : Nat) (hl : l < s.layers)
    (nonneg : numbers.NonNegative s) (ball : Ball) (radius : Int)
    (radiusNonneg : 0 ≤ ball.radius) (le : ball.radius ≤ radius) :
    0 ≤ leastFeedForwardAdditionLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ball ∧
      leastFeedForwardAdditionLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ball ≤
          feedForwardAdditionLength s tables numbers l radius := by
  obtain ⟨_, up, down, routed⟩ := nonneg l hl
  have block : ∀ (w : GatedWeights) (hidden gateShift upShift : Nat) (stretchUp stretchDown : Int),
      0 ≤ stretchUp → 0 ≤ stretchDown →
      0 ≤ stretchDown * leastHiddenLength tables w s.width hidden gateShift upShift taus ball
          stretchUp (largestMagnitude tables.silu.entries * stretchUp) ∧
        stretchDown * leastHiddenLength tables w s.width hidden gateShift upShift taus ball
          stretchUp (largestMagnitude tables.silu.entries * stretchUp) ≤
            stretchDown * hiddenLength tables hidden upShift stretchUp radius := by
    intro w hidden gateShift upShift stretchUp stretchDown up0 down0
    have hiddenBound := leastHiddenLength_le tables w s.width hidden gateShift upShift taus ball
      stretchUp radius up0 radiusNonneg le
    exact mul_le_mul_of_bounds _ _ _ _ down0 hiddenBound.1 (Int.le_refl _) hiddenBound.2
  unfold leastFeedForwardAdditionLength feedForwardAdditionLength
  simp only [leastBoundNumbersOf]
  cases mixture : s.isMixture l with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have shared := block (weights.perLayer.entry l).shared s.hidden (s.perLayer.entry l).gateShift
      (s.perLayer.entry l).upShift _ _ up down
    exact ⟨roundedLength_nonneg _ _ _ shared.1, roundedLength_le _ _ _ _ shared.2⟩
  | true =>
    simp only [if_true]
    have some_expert := isMixture_experts s l mixture
    have shared := block (weights.perLayer.entry l).shared s.expertHidden
      (s.perLayer.entry l).gateShift (s.perLayer.entry l).upShift _ _ up down
    have each := fun e (he : e ≤ s.experts - 1) =>
      block ((weights.perLayer.entry l).routed.entry e) s.expertHidden
        (s.perLayer.entry l).routedGateShift (s.perLayer.entry l).routedUpShift _ _
        (routed mixture e (by omega)).1 (routed mixture e (by omega)).2
    have first := (maxUpTo_spec (fun e => numbers.routedDown l e *
      leastHiddenLength tables ((weights.perLayer.entry l).routed.entry e) s.width
        s.expertHidden (s.perLayer.entry l).routedGateShift (s.perLayer.entry l).routedUpShift taus
        ball (numbers.routedUp l e)
        (largestMagnitude tables.silu.entries * numbers.routedUp l e)) (s.experts - 1)).1 0
      (by omega)
    have largest := maxUpTo_le (fun e => numbers.routedDown l e *
      leastHiddenLength tables ((weights.perLayer.entry l).routed.entry e) s.width
        s.expertHidden (s.perLayer.entry l).routedGateShift (s.perLayer.entry l).routedUpShift taus
        ball (numbers.routedUp l e)
        (largestMagnitude tables.silu.entries * numbers.routedUp l e)) (s.experts - 1)
      (maxUpTo (fun e => numbers.routedDown l e *
        hiddenLength tables s.expertHidden (s.perLayer.entry l).routedUpShift
          (numbers.routedUp l e) radius) (s.experts - 1))
      fun e he => Int.le_trans (each e he).2
        ((maxUpTo_spec (fun e => numbers.routedDown l e *
          hiddenLength tables s.expertHidden (s.perLayer.entry l).routedUpShift
            (numbers.routedUp l e) radius) (s.experts - 1)).1 e he)
    have zero := (each 0 (by omega)).1
    simp only at first
    exact ⟨roundedLength_nonneg _ _ _ (by omega), roundedLength_le _ _ _ _ (by omega)⟩

/-! ## 5. The stream's length, and the checks -/

/-- A norm's fine ball at a shorter row: its numerator and its radius are not negative, and the
radius is at most `ballRadius` at a longer row. -/
theorem normBall_le (width bits shift : Nat) (eps shorter longer : Int) (nonneg : 0 ≤ shorter)
    (le : shorter ≤ longer) :
    0 ≤ (normBall width bits shift eps shorter).numerator ∧
      0 ≤ (normBall width bits shift eps shorter).radius ∧
      (normBall width bits shift eps shorter).radius ≤ ballRadius width bits shift eps longer :=
  ⟨normBall_numerator_nonneg _ _ _ _ _,
    shiftUp_nonneg (normBall_numerator_nonneg _ _ _ _ _) _,
    Int.le_trans (normBall_radius_le _ _ _ _ _) (ballRadius_le _ _ _ _ _ _ nonneg le).2⟩

/-- The stream after the attention of a layer, if the claim holds of the stream that enters it. -/
theorem leastStreamLengthAfterAttention_le (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) (numbers : StretchNumbers) (nonneg : numbers.NonNegative s) (l : Nat)
    (hl : l < s.layers)
    (entering : 0 ≤ leastStreamLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ∧
      leastStreamLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ≤
          streamLength s tables weights numbers l) :
    0 ≤ leastStreamLengthAfterAttention s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ∧
      leastStreamLengthAfterAttention s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ≤
          streamLengthAfterAttention s tables weights numbers l := by
  have addition := leastAttentionAdditionLength_le s (s.perLayer.entry l) (weights.perLayer.entry l)
    taus (attentionBall s l (leastStreamLength s tables weights
      (leastBoundNumbersOf s tables weights taus numbers) l))
    ((leastBoundNumbersOf s tables weights taus numbers).valueHead l) (numbers.output l)
    (nonneg l hl).1
  unfold leastStreamLengthAfterAttention streamLengthAfterAttention layerAttentionAddition
  simp only [leastBoundNumbersOf] at addition entering ⊢
  omega

/-- **The stream's length.** The least-bound check's bound with the matching numbers is not negative
and at most the length check's. -/
theorem leastStreamLength_le (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) (numbers : StretchNumbers) (nonneg : numbers.NonNegative s)
    (l : Nat) (hl : l ≤ s.layers) :
    0 ≤ leastStreamLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ∧
      leastStreamLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l ≤
          streamLength s tables weights numbers l := by
  induction l with
  | zero => exact ⟨(rootUp_spec _).1, Int.le_refl _⟩
  | succ l ih =>
    have between := leastStreamLengthAfterAttention_le s tables weights taus numbers nonneg l
      (by omega) (ih (by omega))
    have ball := normBall_le s.width (s.perLayer.entry l).feedForwardBits
      (s.perLayer.entry l).feedForwardShift (s.perLayer.entry l).feedForwardEps _ _ between.1
      between.2
    have addition := leastFeedForwardAdditionLength_le s tables weights taus numbers l (by omega)
      nonneg (feedForwardBall s l (leastStreamLengthAfterAttention s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) l))
      (feedForwardRadius s l (streamLengthAfterAttention s tables weights numbers l))
      ball.2.1 ball.2.2
    have left : leastStreamLength s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) (l + 1) =
        leastStreamLengthAfterAttention s tables weights
          (leastBoundNumbersOf s tables weights taus numbers) l
        + leastFeedForwardAdditionLength s tables weights
          (leastBoundNumbersOf s tables weights taus numbers) l
          (feedForwardBall s l (leastStreamLengthAfterAttention s tables weights
            (leastBoundNumbersOf s tables weights taus numbers) l)) := rfl
    have right : streamLength s tables weights numbers (l + 1) =
        streamLengthAfterAttention s tables weights numbers l
        + feedForwardAdditionLength s tables numbers l
          (feedForwardRadius s l (streamLengthAfterAttention s tables weights numbers l)) := rfl
    rw [left, right]
    omega

/-- **Whatever passes the length check passes the least-bound check with the matching numbers**, for
every list of taus, if no stretch number is negative. -/
theorem leastBoundWorstCaseCheck_of_lengthWorstCaseCheck (s : Settings) (tables : Tables)
    (weights : Weights) (taus : List Int) (numbers : StretchNumbers)
    (nonneg : numbers.NonNegative s)
    (passes : lengthWorstCaseCheck s tables weights numbers = true) :
    leastBoundWorstCaseCheck s tables weights
      (leastBoundNumbersOf s tables weights taus numbers) = true := by
  simp only [lengthWorstCaseCheck, Bool.and_eq_true, allBelow_spec] at passes
  simp only [leastBoundWorstCaseCheck, Bool.and_eq_true, allBelow_spec]
  have stream := leastStreamLength_le s tables weights taus numbers nonneg
  refine ⟨⟨passes.1.1, fun l hl => ?_⟩, ?_⟩
  · have fits := passes.1.2 l hl
    simp only [lengthLayerFits, Bool.and_eq_true] at fits
    have entering := stream l (by omega)
    have between :=
      leastStreamLengthAfterAttention_le s tables weights taus numbers nonneg l hl entering
    have first := normBall_le s.width (s.perLayer.entry l).attentionBits
      (s.perLayer.entry l).attentionShift (s.perLayer.entry l).attentionEps _ _ entering.1
      entering.2
    have second := normBall_le s.width (s.perLayer.entry l).feedForwardBits
      (s.perLayer.entry l).feedForwardShift (s.perLayer.entry l).feedForwardEps _ _ between.1
      between.2
    simp only [leastBoundLayerFits, Bool.and_eq_true]
    exact ⟨⟨⟨normFitsLength_of_le _ _ _ _ _ entering.1 entering.2 fits.1.1.1,
      attentionFitsLeastBound_of_inBall s _ tables _ _ _ _ first.1 first.2.2 fits.1.1.2⟩,
      normFitsLength_of_le _ _ _ _ _ between.1 between.2 fits.1.2⟩,
      feedForwardFitsLeastBound_of_inBall s _ _ _ _ _ _ second.1 second.2.2 fits.2⟩
  · exact normFitsLength_of_le _ _ _ _ _ (stream s.layers (Nat.le_refl _)).1
      (stream s.layers (Nat.le_refl _)).2 passes.2

/-- The two together: stretch numbers that hold and pass give matching numbers that hold and pass.
-/
theorem leastBound_of_length (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) (numbers : StretchNumbers) (holds : numbers.Hold s weights)
    (passes : lengthWorstCaseCheck s tables weights numbers = true) :
    (leastBoundNumbersOf s tables weights taus numbers).Hold s tables weights ∧
      leastBoundWorstCaseCheck s tables weights
        (leastBoundNumbersOf s tables weights taus numbers) = true :=
  ⟨leastBoundNumbersOf_hold s tables weights taus numbers holds,
    leastBoundWorstCaseCheck_of_lengthWorstCaseCheck s tables weights taus numbers
      (nonNegative_of_hold s weights numbers holds) passes⟩

/-- The numbers that match the Frobenius stretch numbers are the least-bound check's own Frobenius
numbers. -/
theorem leastBoundNumbersOf_frobenius (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) :
    leastBoundNumbersOf s tables weights taus (frobeniusStretchNumbers s weights) =
      frobeniusLeastBoundNumbers s tables weights taus := rfl

/-- So whatever passes the length check with Frobenius norms passes the least-bound check with
Frobenius norms, for every list of taus. -/
theorem frobeniusLeastBoundCheck_of_frobeniusLengthCheck (s : Settings) (tables : Tables)
    (weights : Weights) (taus : List Int)
    (passes : lengthWorstCaseCheck s tables weights (frobeniusStretchNumbers s weights) = true) :
    leastBoundWorstCaseCheck s tables weights (frobeniusLeastBoundNumbers s tables weights taus) =
      true := by
  rw [← leastBoundNumbersOf_frobenius]
  exact leastBoundWorstCaseCheck_of_lengthWorstCaseCheck s tables weights taus _
    (nonNegative_of_hold s weights _ (frobeniusStretchNumbers_hold s weights)) passes

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.leastBoundNumbersOf_hold
#print axioms IntegerTransformer.Bounds.leastBoundWorstCaseCheck_of_lengthWorstCaseCheck
#print axioms IntegerTransformer.Bounds.frobeniusLeastBoundCheck_of_frobeniusLengthCheck
#print axioms IntegerTransformer.Bounds.leastBound_of_length
