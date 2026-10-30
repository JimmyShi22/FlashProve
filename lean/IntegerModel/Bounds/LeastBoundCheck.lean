-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LeastBoundCheck.lean

A further worst-case check on settings, tables and weights, with given numbers. Definitions only.
`leastBoundWorstCaseCheck settings tables weights numbers` reads no prompt. Like
`lengthWorstCaseCheck` (IntegerModel/Bounds/LengthCheck.lean) it works with the box, with balls and
with lengths: a norm's output lies in a box and in a ball, and the rows of the stream have a bounded
length, which grows by a sum over the layers. At each place it takes the least of several bounds:
- One column's sum of products (`leastColumnBound`, IntegerModel/Bounds/LeastBoundLemmas.lean): the
  box's bound, the ball's bound, and the bound from the two together for each `tau` of the given
  list. The ball's radius is a fraction, and the bounds are rounded down.
- A rotated query or key product (`leastRotatedBound`): `|c| b + |s| b'`, and the root of
  `(c^2 + s^2) * min(b0^2 + b1^2, lambda * B^2)`, with the cosine and sine of the position, the
  ball's radius `B`, and a number `lambda` that the check itself sees to dominate the 2 by 2 Gram
  matrix of the pair of columns.
- A value row of one key-value head (`valueHeadLength`): entry by entry, and by the stretch of the
  head's columns of the value matrix. A head's output is a rounded mean of such rows
  (`headOutLength`), and all heads' outputs together are bounded through them and through the box
  (`leastMixedLength`).
- The activation of a hidden unit (`siluAt`): the SiLU table's largest entry on the keys that the
  unit's gate can reach.
- The products of activation and up projection of one block (`leastHiddenLength`): the bound of
  `lengthWorstCaseCheck`; entry by entry; by the stretch of the up matrix with each column
  multiplied by the bound on its hidden unit's activation; and the same with the table's largest
  entry times the stretch of the up matrix.
How much a matrix can stretch a vector's length is not computed here. The numbers are given in a
record `LeastBoundNumbers`, and `LeastBoundNumbers.Hold` says that they are what they are said to
be. The list `taus` may be any list: each member gives a bound, and a member that is not positive
gives the box's. Alone the test says nothing of the weights: it uses the numbers and does not test
them, nor that they are not negative; with numbers that are too small it can pass at weights at
which the model fails (IntegerModel/Bounds/LeastBoundCheckControl.lean). It counts only together
with `LeastBoundNumbers.Hold`, or with the test `leastBoundNumbersPassScaledGramTest`
(IntegerModel/Bounds/ScaledGramTestOfLeastBoundNumbers.lean), which gives it. It also counts only
beside `wellFormed`: it does not test that the arrays have their sizes, and it passes on empty
arrays.
The names are full words. For the letters of IntegerModel/Model.lean: settings is its s,
layerSettings its p, layerWeights and gatedWeights its w, layer its l, position its t.
Limits: the check is sufficient, not necessary. A root or a division in a length is rounded up to a
whole number; a bound on a whole number is rounded down. The check computes
the same sums many times over, so it is costly to evaluate. `Hold` at a layer speaks of the up
matrix with scaled columns, and the scales depend on the stream's bound, so on the numbers of the
layers below, on this layer's numbers for the output matrix and the value heads, and on the list of
taus. This file says of no weights that they pass, and no file of this folder says that the
converted weights of a real model pass with any numbers. It is this library's own check: nothing
here relates it to a check that any program makes. It imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.LeastBoundLemmas

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- The list of taus, and one number for each matrix, slice of a matrix or matrix with scaled
columns whose stretch the check uses. -/
structure LeastBoundNumbers where
  taus : List Int
  output : Nat → Int                -- by layer: Wo
  valueHead : Nat → Nat → Int       -- by layer and key-value head: the head's columns of Wv
  up : Nat → Int                    -- by layer: Wu of the dense block or the shared expert
  scaledUp : Nat → Int              -- by layer: Wu with scaled columns
  down : Nat → Int                  -- by layer: Wd
  routedUp : Nat → Nat → Int        -- by layer and expert: Wur_e
  routedScaledUp : Nat → Nat → Int  -- by layer and expert: Wur_e with scaled columns
  routedDown : Nat → Nat → Int      -- by layer and expert: Wdr_e

/-! ## Query and key columns -/

/-- The inner product of two columns. -/
def columnInner (matrix : Matrix) (rows first second : Nat) : Int :=
  sumOver rows fun row => (matrix.entry row).entry first * (matrix.entry row).entry second

/-- At or above the larger eigenvalue of the Gram matrix of columns `first` and `first + 1`:
`(n0 + n1 + sqrt((n0 - n1)^2 + 4 p^2)) / 2`, rounded up. -/
def pairStretchSquare (matrix : Matrix) (rows first : Nat) : Int :=
  (columnSquares matrix rows first + columnSquares matrix rows (first + 1)
    + rootUp ((columnSquares matrix rows first - columnSquares matrix rows (first + 1))
        * (columnSquares matrix rows first - columnSquares matrix rows (first + 1))
      + 4 * (columnInner matrix rows first (first + 1)
        * columnInner matrix rows first (first + 1))) + 1) / 2

/-- Bounds `A0^2 + A1^2` for the sums of columns `first` and `first + 1`:
`min(b0^2 + b1^2, lambda * B^2)`. The second is taken only if the number is seen to dominate the
Gram matrix. -/
def pairSquaresBound (taus : List Int) (ball : Ball) (matrix : Matrix) (rows first : Nat) : Int :=
  let entrywise :=
    leastColumnBound taus ball matrix rows first * leastColumnBound taus ball matrix rows first
    + leastColumnBound taus ball matrix rows (first + 1)
      * leastColumnBound taus ball matrix rows (first + 1)
  if columnSquares matrix rows first ≤ pairStretchSquare matrix rows first
      ∧ columnSquares matrix rows (first + 1) ≤ pairStretchSquare matrix rows first
      ∧ columnInner matrix rows first (first + 1) * columnInner matrix rows first (first + 1)
        ≤ (pairStretchSquare matrix rows first - columnSquares matrix rows first)
          * (pairStretchSquare matrix rows first - columnSquares matrix rows (first + 1)) then
    min entrywise (pairStretchSquare matrix rows first * (ball.numerator * ball.numerator)
      / (2 ^ ball.shift * 2 ^ ball.shift))
  else entrywise

/-- Bounds entry `column` of a rotated product: the least of `|c| b + |s| b'` and
`sqrt((c^2 + s^2) * min(b0^2 + b1^2, lambda * B^2))`, with the position's own cosine and sine. -/
def leastRotatedBound (cosine sine : IntegerVector) (headDim : Nat) (taus : List Int) (ball : Ball)
    (matrix : Matrix) (rows column : Nat) : Int :=
  min (rotatedBound cosine sine headDim (leastColumnBound taus ball matrix rows) column)
    (integerSquareRoot ((cosine.entry (column % headDim / 2) * cosine.entry (column % headDim / 2)
                    + sine.entry (column % headDim / 2) * sine.entry (column % headDim / 2))
                  * pairSquaresBound taus ball matrix rows (column - column % 2)).toNat)

/-! ## Conditions 3 to 7 -/

/-- Conditions 3 and 4 of one layer, at every position, for a normed row in the box and the ball. -/
def attentionFitsLeastBound (settings : Settings) (layerSettings : LayerSettings) (tables : Tables)
    (layerWeights : LayerWeights) (taus : List Int) (ball : Ball) : Bool :=
  (allBelow settings.positions fun position =>
    (allBelow settings.queryWidth fun column =>
      roundShift
        (leastRotatedBound (cosineRow settings layerSettings tables position)
          (sineRow settings layerSettings tables position) settings.headDim taus ball
          layerWeights.query settings.width column)
        layerSettings.queryShift ≤ 32767)                                                       -- 3
    && allBelow settings.keyValueWidth fun column =>
      roundShift
        (leastRotatedBound (cosineRow settings layerSettings tables position)
          (sineRow settings layerSettings tables position) settings.headDim taus ball
          layerWeights.key settings.width column)
        layerSettings.keyShift ≤ 32767)                                                         -- 3
  && allBelow settings.keyValueWidth fun column =>
    roundShift (leastColumnBound taus ball layerWeights.value settings.width column)
      layerSettings.valueShift ≤ 32767                                                          -- 4

/-- Conditions 6 and 7 of one gated block. 4,194,175 = 256 * 16,383 + 127. -/
def unitsFitLeastBound (gatedWeights : GatedWeights) (width hidden gateShift upShift : Nat)
    (taus : List Int) (ball : Ball) : Bool :=
  allBelow hidden fun unit =>
    roundShift (leastColumnBound taus ball gatedWeights.gate width unit) gateShift ≤ 4194175    -- 6
    && roundShift (leastColumnBound taus ball gatedWeights.up width unit) upShift ≤ 32767       -- 7

/-- Conditions 5, 6 and 7 of one layer. 262,143 = 8 * 32,767 + 7. -/
def feedForwardFitsLeastBound (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (mixture : Bool) (taus : List Int) (ball : Ball) : Bool :=
  if mixture then
    unitsFitLeastBound layerWeights.shared settings.width settings.expertHidden
      layerSettings.gateShift layerSettings.upShift taus ball
    && (allBelow settings.experts fun expert =>
      roundShift (leastColumnBound taus ball layerWeights.router settings.width expert)
        layerSettings.routerShift ≤ 262143                                                      -- 5
      && unitsFitLeastBound (layerWeights.routed.entry expert) settings.width settings.expertHidden
        layerSettings.routedGateShift layerSettings.routedUpShift taus ball)
  else
    unitsFitLeastBound layerWeights.shared settings.width settings.hidden layerSettings.gateShift
      layerSettings.upShift taus ball

/-! ## The addition after attention

From here on a docstring says "bounds the length of" or "at or above the length of" a vector of the
model. That holds for arguments that fit together (`wellFormed`), numbers that hold
(`LeastBoundNumbers.Hold`) and tables that pass `routedInputFits`: under these premises
IntegerModel/Bounds/LeastBoundNeverFails.lean proves it. -/

/-- Bounds a value entry: `min(2,047, rq(b_j, kv))`. -/
def valueEntryBound (taus : List Int) (ball : Ball) (matrix : Matrix)
    (width valueShift column : Nat) : Int :=
  min activationBound (roundShift (leastColumnBound taus ball matrix width column) valueShift)

/-- Bounds the length of a value row of one key-value head: entry by entry, and
`stretch * B / 2^kv + sqrt(dh) / 2`. -/
def valueHeadLength (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (taus : List Int) (ball : Ball) (stretch : Int)
    (keyValueHead : Nat) : Int :=
  min
    (rootUp (sumSquaresOver settings.headDim fun coordinate =>
      valueEntryBound taus ball layerWeights.value settings.width layerSettings.valueShift
        (keyValueHead * settings.headDim + coordinate)))
    (roundedLength settings.headDim (stretch * ball.radius) layerSettings.valueShift)

/-- Bounds the length of the output of one query head: that of its key-value head's value rows, and
`sqrt(dh) / 2` for the rounding. -/
def headOutLength (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (taus : List Int) (ball : Ball) (stretchOf : Nat → Int)
    (head : Nat) : Int :=
  valueHeadLength settings layerSettings layerWeights taus ball
      (stretchOf (head / (settings.queryHeads / settings.keyValueHeads)))
      (head / (settings.queryHeads / settings.keyValueHeads))
    + (rootUp settings.headDim + 1) / 2

/-- Bounds the length of all heads' outputs side by side: through the box, and through the heads'
own bounds. -/
def leastMixedLength (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (taus : List Int) (ball : Ball) (stretchOf : Nat → Int) : Int :=
  min (mixedLength settings)
    (rootUp (sumSquaresOver settings.queryHeads fun head =>
      headOutLength settings layerSettings layerWeights taus ball stretchOf head))

/-- Bounds the length of what attention adds to a row of the stream: the stretch of the output
matrix times the length of the heads' outputs, over `2^ko`, and `sqrt(d) / 2`. -/
def leastAttentionAdditionLength (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (taus : List Int) (ball : Ball) (stretchOf : Nat → Int)
    (stretchOutput : Int) : Int :=
  roundedLength settings.width
    (stretchOutput * leastMixedLength settings layerSettings layerWeights taus ball stretchOf)
    layerSettings.outputShift

/-! ## The addition after a feed-forward block -/

/-- How far the key of the SiLU table can reach at a hidden unit whose gate's sum is within `bound`.
-/
def gateReach (bound : Int) (gateShift : Nat) : Int := min 32640 (roundShift bound gateShift)

/-- Bounds the activation of one hidden unit. -/
def siluAt (tables : Tables) (gatedWeights : GatedWeights) (width gateShift : Nat) (taus : List Int)
    (ball : Ball) (unit : Nat) : Int :=
  siluBoundWithin tables
    (gateReach (leastColumnBound taus ball gatedWeights.gate width unit) gateShift)

/-- Bounds the up projection of one hidden unit. -/
def upAt (gatedWeights : GatedWeights) (width upShift : Nat) (taus : List Int) (ball : Ball)
    (unit : Nat) : Int :=
  roundShift (leastColumnBound taus ball gatedWeights.up width unit) upShift

/-- `stretch * radius / 2^ku`, and half the length of the activations' bounds for the rounding of
the up projections. -/
def stretchedHiddenLength (silu : Nat → Int) (hidden upShift : Nat) (stretch radius : Int) : Int :=
  shiftUp (stretch * radius + 2 ^ (upShift - 1) * rootUp (sumSquaresOver hidden silu)) upShift

/-- Bounds the length of the vector of the products `s[j] u[j]` of one block: the least of four. -/
def leastHiddenLength (tables : Tables) (gatedWeights : GatedWeights)
    (width hidden gateShift upShift : Nat) (taus : List Int) (ball : Ball)
    (stretchUp stretchScaledUp : Int) : Int :=
  min
    (min (hiddenLength tables hidden upShift stretchUp ball.radius)
      (rootUp (sumSquaresOver hidden fun unit =>
        siluAt tables gatedWeights width gateShift taus ball unit
          * upAt gatedWeights width upShift taus ball unit)))
    (min
      (stretchedHiddenLength (siluAt tables gatedWeights width gateShift taus ball) hidden upShift
        stretchScaledUp ball.radius)
      (stretchedHiddenLength (siluAt tables gatedWeights width gateShift taus ball) hidden upShift
        (largestMagnitude tables.silu.entries * stretchUp) ball.radius))

/-- Bounds the length of what the feed-forward block of a layer adds to a row of the stream: the
down matrix's stretch times the products' length, for the routed part the largest such number over
all experts, over `2^kd`, and `sqrt(d) / 2`. -/
def leastFeedForwardAdditionLength (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (layer : Nat) (ball : Ball) : Int :=
  let layerSettings := settings.perLayer.entry layer
  let layerWeights := weights.perLayer.entry layer
  if settings.isMixture layer then
    roundedLength settings.width
      (numbers.down layer
          * leastHiddenLength tables layerWeights.shared settings.width settings.expertHidden
            layerSettings.gateShift layerSettings.upShift numbers.taus ball (numbers.up layer)
            (numbers.scaledUp layer)
        + maxUpTo
          (fun expert => numbers.routedDown layer expert
            * leastHiddenLength tables (layerWeights.routed.entry expert) settings.width
              settings.expertHidden layerSettings.routedGateShift layerSettings.routedUpShift
              numbers.taus ball (numbers.routedUp layer expert)
              (numbers.routedScaledUp layer expert))
          (settings.experts - 1))
      layerSettings.downShift
  else
    roundedLength settings.width
      (numbers.down layer
        * leastHiddenLength tables layerWeights.shared settings.width settings.hidden
          layerSettings.gateShift layerSettings.upShift numbers.taus ball (numbers.up layer)
          (numbers.scaledUp layer))
      layerSettings.downShift

/-! ## The stream's length -/

/-- The ball after the first norm of a layer, if the row is at most `rowLength` long. -/
def attentionBall (settings : Settings) (layer : Nat) (rowLength : Int) : Ball :=
  normBall settings.width (settings.perLayer.entry layer).attentionBits
    (settings.perLayer.entry layer).attentionShift
    (settings.perLayer.entry layer).attentionEps rowLength

/-- The ball after the second norm of a layer, if the row is at most `rowLength` long. -/
def feedForwardBall (settings : Settings) (layer : Nat) (rowLength : Int) : Ball :=
  normBall settings.width (settings.perLayer.entry layer).feedForwardBits
    (settings.perLayer.entry layer).feedForwardShift
    (settings.perLayer.entry layer).feedForwardEps rowLength

/-- Bounds the length of what the attention of a layer adds, if the rows that enter are at most
`rowLength` long. -/
def layerAttentionAddition (settings : Settings) (weights : Weights) (numbers : LeastBoundNumbers)
    (layer : Nat) (rowLength : Int) : Int :=
  leastAttentionAdditionLength settings (settings.perLayer.entry layer)
    (weights.perLayer.entry layer) numbers.taus (attentionBall settings layer rowLength)
    (numbers.valueHead layer) (numbers.output layer)

/-- At or above the length of every row of the stream that enters a layer. -/
def leastStreamLength (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) : Nat → Int
  | 0 => embeddingLength settings weights
  | layer + 1 =>
    let entering := leastStreamLength settings tables weights numbers layer
    let between := entering + layerAttentionAddition settings weights numbers layer entering
    between + leastFeedForwardAdditionLength settings tables weights numbers layer
      (feedForwardBall settings layer between)

/-- The same after the attention of that layer. -/
def leastStreamLengthAfterAttention (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (layer : Nat) : Int :=
  leastStreamLength settings tables weights numbers layer
    + layerAttentionAddition settings weights numbers layer
      (leastStreamLength settings tables weights numbers layer)

/-! ## What the numbers are said to be -/

/-- The up matrix with scaled columns: each column times the bound on the activation of its hidden
unit. -/
def scaledUpEntries (tables : Tables) (gatedWeights : GatedWeights) (width gateShift : Nat)
    (taus : List Int) (ball : Ball) (row unit : Nat) : Int :=
  siluAt tables gatedWeights width gateShift taus ball unit * (gatedWeights.up.entry row).entry unit

/-- The three numbers of one gated block. -/
def GatedStretchNumbersHold (tables : Tables) (gatedWeights : GatedWeights)
    (width hidden gateShift : Nat) (taus : List Int) (ball : Ball)
    (stretchUp stretchScaledUp stretchDown : Int) : Prop :=
  StretchBound gatedWeights.up width hidden stretchUp
  ∧ StretchBoundOf (scaledUpEntries tables gatedWeights width gateShift taus ball) width hidden
    stretchScaledUp
  ∧ StretchBound gatedWeights.down hidden width stretchDown

/-- The numbers are what they are said to be. A statement on settings, tables, weights and the
numbers alone; no prompt occurs. The scales of the up matrix's columns depend on the stream's bound,
and so on the numbers of the layers below, on this layer's numbers for the output matrix and the
value heads, and on the list of taus. -/
def LeastBoundNumbers.Hold (numbers : LeastBoundNumbers) (settings : Settings) (tables : Tables)
    (weights : Weights) : Prop :=
  ∀ layer, layer < settings.layers →
    StretchBound (weights.perLayer.entry layer).output settings.queryWidth settings.width
      (numbers.output layer)
    ∧ (∀ keyValueHead, keyValueHead < settings.keyValueHeads →
      StretchBoundOf
        (fun row coordinate => ((weights.perLayer.entry layer).value.entry row).entry
          (keyValueHead * settings.headDim + coordinate))
        settings.width settings.headDim (numbers.valueHead layer keyValueHead))
    ∧ GatedStretchNumbersHold tables (weights.perLayer.entry layer).shared settings.width
        (sharedHidden settings layer) (settings.perLayer.entry layer).gateShift numbers.taus
        (feedForwardBall settings layer
          (leastStreamLengthAfterAttention settings tables weights numbers layer))
        (numbers.up layer) (numbers.scaledUp layer) (numbers.down layer)
    ∧ (settings.isMixture layer = true → ∀ expert, expert < settings.experts →
      GatedStretchNumbersHold tables ((weights.perLayer.entry layer).routed.entry expert)
        settings.width settings.expertHidden (settings.perLayer.entry layer).routedGateShift
        numbers.taus
        (feedForwardBall settings layer
          (leastStreamLengthAfterAttention settings tables weights numbers layer))
        (numbers.routedUp layer expert) (numbers.routedScaledUp layer expert)
        (numbers.routedDown layer expert))

/-! ## The check -/

/-- The check of one layer: conditions 1 and 2 at its two norms, and conditions 3 to 7. -/
def leastBoundLayerFits (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (layer : Nat) : Bool :=
  let layerSettings := settings.perLayer.entry layer
  let layerWeights := weights.perLayer.entry layer
  let entering := leastStreamLength settings tables weights numbers layer
  let between := leastStreamLengthAfterAttention settings tables weights numbers layer
  normFitsLength layerSettings.attentionBits layerSettings.attentionShift
      layerSettings.attentionEps entering
  && attentionFitsLeastBound settings layerSettings tables layerWeights numbers.taus
      (attentionBall settings layer entering)
  && normFitsLength layerSettings.feedForwardBits layerSettings.feedForwardShift
      layerSettings.feedForwardEps between
  && feedForwardFitsLeastBound settings layerSettings layerWeights (settings.isMixture layer)
      numbers.taus (feedForwardBall settings layer between)

/-- **The least-bound check.** It reads the settings, the tables, the weights and the numbers, and
no prompt. Alone the test says nothing of the weights: it uses the numbers and does not test them,
nor that they are not negative; with numbers that are too small it can pass at weights at which the
model fails (IntegerModel/Bounds/LeastBoundCheckControl.lean). It counts only together with
`LeastBoundNumbers.Hold`, or with the test `leastBoundNumbersPassScaledGramTest`
(IntegerModel/Bounds/ScaledGramTestOfLeastBoundNumbers.lean), which gives it. It also counts only
beside `wellFormed`: it does not test that the arrays have their sizes, and it passes on empty
arrays. -/
def leastBoundWorstCaseCheck (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) : Bool :=
  routedInputFits tables
  && (allBelow settings.layers fun layer =>
    leastBoundLayerFits settings tables weights numbers layer)
  && normFitsLength settings.finalBits settings.finalShift settings.finalEps
      (leastStreamLength settings tables weights numbers settings.layers)

end IntegerTransformer.Bounds
