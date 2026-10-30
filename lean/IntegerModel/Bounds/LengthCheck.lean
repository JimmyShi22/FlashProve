-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LengthCheck.lean

A worst-case check with lengths, a ball and stretch numbers.

Definitions only. `lengthWorstCaseCheck settings tables weights numbers` is a test that reads no
prompt. Beside the box of IntegerModel/Bounds/Check.lean it uses lengths
(IntegerModel/Bounds/Lengths.lean): a vector is at most `X` long if the sum of its squares is at
most `X * X`.

- A norm's result lies in a ball as well as in the box (`ballRadius`). So a sum of products with one
  column of a weight matrix has two bounds, and the check takes the smaller (`columnBoundInBall`).
- Every row of the stream has a bounded length (`streamLength`). It starts at the longest row of the
  embedding, and each of the two steps of a layer adds a vector of bounded length
  (`attentionAdditionLength`, `feedForwardAdditionLength`).
- By how much a matrix can stretch a vector's length is not computed here. The numbers are given
  (`StretchNumbers`), and `StretchNumbers.Hold` is the statement, on the sizes in the settings and
  on the weights alone, that each is at or above the largest singular value of its matrix.
  `frobeniusStretchNumbers` are stretch numbers in whole numbers that hold at all weights.

Alone the test says nothing of the weights: it uses the stretch numbers and does not test them, nor
that they are not negative; with numbers that are too small it can pass at weights at which the
model fails (IntegerModel/Bounds/LengthCheckControl.lean). It counts only together with
`StretchNumbers.Hold`, or with one of the tests that give it: `stretchNumbersPassGramTest`,
`stretchNumbersPassScaledGramTest`, `stretchNumbersPassSmallerSideGramTest`
(IntegerModel/Bounds/GramTestOfStretchNumbers.lean, ScaledGramTestOfStretchNumbers.lean,
SmallerSideGramTestOfStretchNumbers.lean). It also counts only beside `wellFormed`: it does not test
that the arrays have their sizes, and it passes on empty arrays.

The ball's radius depends on the largest root that the norm can find, and the check takes that root
from its own bound on the row's length. So no bound of this file rests on a range condition.

Where each range condition of part 7 of the model's text is tested, at that text's intervals:
- 1, and through it 8: the first line of `normFitsLength`; 2: its second line;
- 3 and 4: `attentionFitsInBall`; 5: `feedForwardFitsInBall`; 6 and 7: `unitsFitInBall`.

The names are full words. For the letters of IntegerModel/Model.lean: settings is its s,
layerSettings its p, layerWeights and gatedWeights its w, layer its l, position its t.

That weights which pass, with stretch numbers that hold, never fail a range condition is proved in
IntegerModel/Bounds/LengthNeverFails.lean.

Limits. The test is sufficient, not necessary. With the Frobenius stretch numbers it is coarse: a
Frobenius norm can exceed the largest singular value by the root of the matrix's rank.
IntegerModel/Bounds/GramIteration.lean, ScaledGramIteration.lean and StretchOfTranspose.lean have
tests in whole numbers under which a number is a bound on a matrix's stretch, and
GramTestOfStretchNumbers.lean, ScaledGramTestOfStretchNumbers.lean and
SmallerSideGramTestOfStretchNumbers.lean have them for all stretch numbers of a model. No file of
this folder says that the converted weights of a real model pass with any stretch numbers. It is
this library's own check: nothing here relates it to a check that any program makes. The function
can be evaluated at small sizes and small tables. At the model's sizes it cannot in practice, as it
is written: it is written to be read, and computes a column's sums anew wherever it uses them.
-/
import IntegerModel.Bounds.Lengths

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## The stretch numbers -/

/-- `stretch` is at or above the largest singular value of the block of the matrix's first `rows`
rows and first `columns` columns: no vector of whole numbers gets longer by more than this factor
when it is multiplied with that block. A read outside the array gives 0, so with sizes that are not
the matrix's own the statement speaks of another block. A statement on the matrix alone, in whole
numbers. -/
def StretchBound (matrix : Matrix) (rows columns : Nat) (stretch : Int) : Prop :=
  0 ≤ stretch ∧ ∀ vector : Nat → Int,
    sumSquaresOver columns
      (fun column => sumOver rows fun row => vector row * (matrix.entry row).entry column)
      ≤ stretch * stretch * sumSquaresOver rows vector

/-- One number for each matrix that the check treats by lengths. -/
structure StretchNumbers where
  output : Nat → Int            -- by layer: Wo
  up : Nat → Int                -- by layer: Wu of the dense block or the shared expert
  down : Nat → Int              -- by layer: Wd of the dense block or the shared expert
  routedUp : Nat → Nat → Int    -- by layer and expert: Wur_e
  routedDown : Nat → Nat → Int  -- by layer and expert: Wdr_e

/-- The hidden units of the dense block, or of the shared expert, of a layer. -/
def sharedHidden (settings : Settings) (layer : Nat) : Nat :=
  if settings.isMixture layer then settings.expertHidden else settings.hidden

/-- The numbers are what they are said to be: each is at or above the largest singular value of its
matrix. A statement on the sizes in the settings and on the weights alone. -/
def StretchNumbers.Hold (numbers : StretchNumbers) (settings : Settings) (weights : Weights) :
    Prop :=
  ∀ layer, layer < settings.layers →
    StretchBound (weights.perLayer.entry layer).output settings.queryWidth settings.width
      (numbers.output layer)
    ∧ StretchBound (weights.perLayer.entry layer).shared.up settings.width
      (sharedHidden settings layer) (numbers.up layer)
    ∧ StretchBound (weights.perLayer.entry layer).shared.down (sharedHidden settings layer)
      settings.width (numbers.down layer)
    ∧ (settings.isMixture layer = true → ∀ expert, expert < settings.experts →
      StretchBound ((weights.perLayer.entry layer).routed.entry expert).up settings.width
        settings.expertHidden (numbers.routedUp layer expert)
      ∧ StretchBound ((weights.perLayer.entry layer).routed.entry expert).down
        settings.expertHidden settings.width (numbers.routedDown layer expert))

/-! ## The ball after a norm, and the bound on one column's sum -/

/-- The radius of the ball in which a norm's result lies, if the row that it reads is at most
`rowLength` long: `2^(M-K) (1 + 1 / integerSquareRoot eps) + (root + 2) / 2^(K+1) + sqrt(d) / 2`, in whole
numbers, rounded up, with the largest root that such a row can give. -/
def ballRadius (width bits shift : Nat) (eps rowLength : Int) : Int :=
  shiftUp (2 ^ bits + (integerSquareRoot (rowLength * rowLength + eps).toNat : Int) / 2
    + 2 ^ bits / (integerSquareRoot eps.toNat : Int) + 1 + 2 ^ (shift - 1) * rootUp width) shift

/-- The sum of the squares of one column. -/
def columnSquares (matrix : Matrix) (rows column : Nat) : Int :=
  sumSquaresOver rows fun row => (matrix.entry row).entry column

/-- Bounds entry `column` of the product of the matrix with any vector in the ball: Cauchy-Schwarz.
-/
def ballColumnBound (radius : Int) (matrix : Matrix) (rows column : Nat) : Int :=
  integerSquareRoot (radius * radius * columnSquares matrix rows column).toNat

/-- The same for every vector in the box and the ball: the smaller of the two. -/
def columnBoundInBall (radius : Int) (matrix : Matrix) (rows column : Nat) : Int :=
  min (boxColumnBound matrix rows column) (ballColumnBound radius matrix rows column)

/-! ## Conditions 1 to 7: as in IntegerModel/Bounds/Check.lean, with `columnBoundInBall` -/

/-- Conditions 1 and 2 at a norm that reads a row at most `rowLength` long. -/
def normFitsLength (bits shift : Nat) (eps rowLength : Int) : Bool :=
  let rootBound : Int := integerSquareRoot (rowLength * rowLength + eps).toNat
  rowLength * rowLength + eps < 2 ^ 78                                                          -- 1
  && roundShift (2 ^ bits + rootBound / 2) shift ≤ 32767                                        -- 2

/-- Conditions 3 and 4 of one layer, at every position, if the first norm's result lies in the box
and in the ball of this radius. -/
def attentionFitsInBall (settings : Settings) (layerSettings : LayerSettings) (tables : Tables)
    (layerWeights : LayerWeights) (radius : Int) : Bool :=
  (allBelow settings.positions fun position =>
    (allBelow settings.queryWidth fun column =>
      roundShift
        (rotatedBound (cosineRow settings layerSettings tables position)
          (sineRow settings layerSettings tables position) settings.headDim
          (columnBoundInBall radius layerWeights.query settings.width) column)
        layerSettings.queryShift ≤ 32767)                                                       -- 3
    && allBelow settings.keyValueWidth fun column =>
      roundShift
        (rotatedBound (cosineRow settings layerSettings tables position)
          (sineRow settings layerSettings tables position) settings.headDim
          (columnBoundInBall radius layerWeights.key settings.width) column)
        layerSettings.keyShift ≤ 32767)                                                         -- 3
  && allBelow settings.keyValueWidth fun column =>
    roundShift (columnBoundInBall radius layerWeights.value settings.width column)
      layerSettings.valueShift ≤ 32767                                                          -- 4

/-- Conditions 6 and 7 of one gated block whose input lies in the box and in the ball of this
radius. 4,194,175 = 256 * 16,383 + 127. -/
def unitsFitInBall (gatedWeights : GatedWeights) (width hidden gateShift upShift : Nat)
    (radius : Int) : Bool :=
  allBelow hidden fun unit =>
    roundShift (columnBoundInBall radius gatedWeights.gate width unit) gateShift ≤ 4194175      -- 6
    && roundShift (columnBoundInBall radius gatedWeights.up width unit) upShift ≤ 32767         -- 7

/-- Conditions 5, 6 and 7 of one layer, if the second norm's result lies in the box and in the ball
of this radius. 262,143 = 8 * 32,767 + 7. -/
def feedForwardFitsInBall (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (mixture : Bool) (radius : Int) : Bool :=
  if mixture then
    unitsFitInBall layerWeights.shared settings.width settings.expertHidden
      layerSettings.gateShift layerSettings.upShift radius
    && (allBelow settings.experts fun expert =>
      roundShift (columnBoundInBall radius layerWeights.router settings.width expert)
        layerSettings.routerShift ≤ 262143                                                      -- 5
      && unitsFitInBall (layerWeights.routed.entry expert) settings.width settings.expertHidden
        layerSettings.routedGateShift layerSettings.routedUpShift radius)
  else
    unitsFitInBall layerWeights.shared settings.width settings.hidden layerSettings.gateShift
      layerSettings.upShift radius

/-! ## The additions' lengths

In this part and the next a docstring says "at or above the length of" a vector of the model. That
holds for arguments that fit together (`wellFormed`), stretch numbers that hold
(`StretchNumbers.Hold`) and tables that pass `routedInputFits`: under these premises
IntegerModel/Bounds/LengthNeverFails.lean proves it. -/

/-- All heads' outputs side by side lie in the box: 2,047 times the root of their number. -/
def mixedLength (settings : Settings) : Int :=
  rootUp (sumOver settings.queryWidth fun _ => activationBound * activationBound)

/-- At or above the length of what attention adds to a row of the stream: the stretch of the output
matrix times `mixedLength`, divided by `2^ko`, and `sqrt(d) / 2` for the rounding. -/
def attentionAdditionLength (settings : Settings) (layerSettings : LayerSettings)
    (stretchOutput : Int) : Int :=
  roundedLength settings.width (stretchOutput * mixedLength settings) layerSettings.outputShift

/-- At or above the length of the vector of the products `s[j] u[j]` of one block: the SiLU table's
largest entry times the length of the up projections, which is the stretch of the up matrix times
the radius, divided by `2^ku`, and `sqrt(h) / 2` for the rounding. -/
def hiddenLength (tables : Tables) (hidden upShift : Nat) (stretchUp radius : Int) : Int :=
  largestMagnitude tables.silu.entries * roundedLength hidden (stretchUp * radius) upShift

/-- At or above the length of what the feed-forward block of a layer adds to a row of the stream:
each down matrix stretches its block's products; the sum is divided by `2^kd`, and `sqrt(d) / 2` is
for the rounding. The router's choice depends on the prompt: the largest bound over all routed
experts stands for it. -/
def feedForwardAdditionLength (settings : Settings) (tables : Tables) (numbers : StretchNumbers)
    (layer : Nat) (radius : Int) : Int :=
  let layerSettings := settings.perLayer.entry layer
  if settings.isMixture layer then
    roundedLength settings.width
      (numbers.down layer
          * hiddenLength tables settings.expertHidden layerSettings.upShift (numbers.up layer)
            radius
        + maxUpTo
          (fun expert => numbers.routedDown layer expert
            * hiddenLength tables settings.expertHidden layerSettings.routedUpShift
              (numbers.routedUp layer expert) radius)
          (settings.experts - 1))
      layerSettings.downShift
  else
    roundedLength settings.width
      (numbers.down layer
        * hiddenLength tables settings.hidden layerSettings.upShift (numbers.up layer) radius)
      layerSettings.downShift

/-! ## The stream's length -/

/-- At or above the length of every token's embedding. -/
def embeddingLength (settings : Settings) (weights : Weights) : Int :=
  rootUp (maxUpTo
    (fun token => sumSquaresOver settings.width fun coordinate =>
      (weights.embedding.entry token).entry coordinate)
    (settings.vocabulary - 1))

/-- The radius of the ball after the second norm of a layer, if the row that it reads is at most
`rowLength` long. -/
def feedForwardRadius (settings : Settings) (layer : Nat) (rowLength : Int) : Int :=
  ballRadius settings.width (settings.perLayer.entry layer).feedForwardBits
    (settings.perLayer.entry layer).feedForwardShift
    (settings.perLayer.entry layer).feedForwardEps rowLength

/-- At or above the length of every row of the stream that enters a layer. -/
def streamLength (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) : Nat → Int
  | 0 => embeddingLength settings weights
  | layer + 1 =>
    let between := streamLength settings tables weights numbers layer
      + attentionAdditionLength settings (settings.perLayer.entry layer) (numbers.output layer)
    between + feedForwardAdditionLength settings tables numbers layer
      (feedForwardRadius settings layer between)

/-- The same after the attention of that layer. -/
def streamLengthAfterAttention (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (layer : Nat) : Int :=
  streamLength settings tables weights numbers layer
    + attentionAdditionLength settings (settings.perLayer.entry layer) (numbers.output layer)

/-! ## The check -/

/-- The check of one layer. -/
def lengthLayerFits (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (layer : Nat) : Bool :=
  let layerSettings := settings.perLayer.entry layer
  let layerWeights := weights.perLayer.entry layer
  let entering := streamLength settings tables weights numbers layer
  let between := streamLengthAfterAttention settings tables weights numbers layer
  normFitsLength layerSettings.attentionBits layerSettings.attentionShift
      layerSettings.attentionEps entering
  && attentionFitsInBall settings layerSettings tables layerWeights
      (ballRadius settings.width layerSettings.attentionBits layerSettings.attentionShift
        layerSettings.attentionEps entering)
  && normFitsLength layerSettings.feedForwardBits layerSettings.feedForwardShift
      layerSettings.feedForwardEps between
  && feedForwardFitsInBall settings layerSettings layerWeights (settings.isMixture layer)
      (feedForwardRadius settings layer between)

/-- **The length check.** It reads the settings, the tables, the weights and the stretch numbers,
and no prompt. Alone the test says nothing of the weights: it uses the stretch numbers and does not
test them, nor that they are not negative; with numbers that are too small it can pass at weights at
which the model fails (IntegerModel/Bounds/LengthCheckControl.lean). It counts only together with
`StretchNumbers.Hold`, or with one of the tests that give it: `stretchNumbersPassGramTest`,
`stretchNumbersPassScaledGramTest`, `stretchNumbersPassSmallerSideGramTest`
(IntegerModel/Bounds/GramTestOfStretchNumbers.lean, ScaledGramTestOfStretchNumbers.lean,
SmallerSideGramTestOfStretchNumbers.lean). It also counts only beside `wellFormed`: it does not test
that the arrays have their sizes, and it passes on empty arrays. -/
def lengthWorstCaseCheck (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) : Bool :=
  routedInputFits tables
  && (allBelow settings.layers fun layer => lengthLayerFits settings tables weights numbers layer)
  && normFitsLength settings.finalBits settings.finalShift settings.finalEps
      (streamLength settings tables weights numbers settings.layers)

/-! ## Stretch numbers in whole numbers -/

/-- At or above the Frobenius norm: the root of the sum of all squares. -/
def frobeniusStretch (matrix : Matrix) (rows columns : Nat) : Int :=
  rootUp (sumOver columns fun column => columnSquares matrix rows column)

/-- The Frobenius norms as stretch numbers, in whole numbers. They hold at all weights
(`frobeniusStretchNumbers_hold`, IntegerModel/Bounds/LengthNeverFails.lean). -/
def frobeniusStretchNumbers (settings : Settings) (weights : Weights) : StretchNumbers where
  output layer :=
    frobeniusStretch (weights.perLayer.entry layer).output settings.queryWidth settings.width
  up layer :=
    frobeniusStretch (weights.perLayer.entry layer).shared.up settings.width
      (sharedHidden settings layer)
  down layer :=
    frobeniusStretch (weights.perLayer.entry layer).shared.down (sharedHidden settings layer)
      settings.width
  routedUp layer expert :=
    frobeniusStretch ((weights.perLayer.entry layer).routed.entry expert).up settings.width
      settings.expertHidden
  routedDown layer expert :=
    frobeniusStretch ((weights.perLayer.entry layer).routed.entry expert).down
      settings.expertHidden settings.width

end IntegerTransformer.Bounds
