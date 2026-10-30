-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Model

/-!
# A worst-case check on settings, tables and weights

Definitions only; the one import is the model's text. `boxWorstCaseCheck settings tables weights` is
a test that reads no prompt. It follows IntegerModel/Model.lean definition by definition and puts,
in the place of each value, an upper bound on that value's absolute value, meant to hold for every
prompt. It starts from one fact: a norm's result is clamped to -2,047 .. 2,047, whatever the stream
is ("the box"). So every matrix product of a layer has an input with known bounds, what a layer adds
to the stream has a bound that does not depend on the stream, and the stream's bound grows by a sum
over the layers.

Where each range condition of part 7 of the model's text is tested:
- 1, and through it 8: the first line of `normFits`; 2: its second line;
- 3 and 4: `attentionFits`; 5: `feedForwardFits`; 6 and 7: `unitsFit`.
The names are full words. For the letters of IntegerModel/Model.lean: `settings` is its `s`,
`layerSettings` its `p`, `layerWeights` and `gatedWeights` its `w`, `layer` its `l`, `position` its
`t`.
The intervals are those of that text: the intervals in which the model is defined. A program that
stops at narrower limits can stop at weights that pass.

That weights which pass never fail a range condition is proved in
IntegerModel/Bounds/NeverFails.lean.

Limits. The test is sufficient, not necessary: weights can fail it though no prompt fails a range
condition. Its bounds are coarse: the box holds many vectors that no norm returns, and the stream's
bound adds the largest case of every addition, coordinate by coordinate. No file of this folder says
that the converted weights of a real model pass it. It is this library's own check: nothing here
relates it to a check that any program makes. The function is written to be read: it computes a
column's sum, a table's largest entry and the bounds of the layers below anew wherever they are
used. So it can be evaluated at small sizes; at the sizes of VerifiableInference/ModelWeights.lean
it cannot in practice.
-/

namespace IntegerTransformer.Bounds

/-- The absolute value of a whole number. -/
def magnitude (number : Int) : Int := number.natAbs

/-- Does `test` hold of every number below `count`? -/
def allBelow (count : Nat) (test : Nat → Bool) : Bool := (List.range count).all test

/-- The largest absolute value among the entries of a vector (0 for the empty vector). The read at
`vector.size` is outside and gives 0. -/
def largestMagnitude (vector : IntegerVector) : Int :=
  maxUpTo (fun place => magnitude (vector.entry place)) vector.size

/-- Bounds entry `column` of `product input matrix _` for every `input` of `rows` entries with
`|input[row]| ≤ inputBound row`: the sum over `row` of
`inputBound row * |matrix[row][column]|`. -/
def columnBound (inputBound : Nat → Int) (matrix : Matrix) (rows column : Nat) : Int :=
  sumOver rows fun row => inputBound row * magnitude ((matrix.entry row).entry column)

/-- The same for an input in the box: 2,047 times the column's sum of absolute values. -/
def boxColumnBound (matrix : Matrix) (rows column : Nat) : Int :=
  columnBound (fun _ => activationBound) matrix rows column

/-! ## The norm: conditions 1 and 2 (and through 1, condition 8) -/

/-- A test that is enough for conditions 1 and 2 at a norm with `eps ≥ 1` that reads a row of
`width` entries, the entry at `coordinate` at most `bound coordinate` in absolute value. -/
def normFits (bits shift : Nat) (eps : Int) (width : Nat) (bound : Nat → Int) : Bool :=
  let sumSquaresBound := sumOver width fun coordinate => bound coordinate * bound coordinate
  let rootBound : Int := integerSquareRoot (sumSquaresBound + eps).toNat
  -- 1
  sumSquaresBound + eps < 2 ^ 78
  -- 2: |entry| * reciprocal ≤ root * reciprocal ≤ 2^bits + root / 2
  && roundShift (2 ^ bits + rootBound / 2) shift ≤ 32767

/-! ## Attention: conditions 3 and 4 -/

/-- The row of cosines that `projections` uses at a position. -/
def cosineRow (settings : Settings) (layerSettings : LayerSettings) (tables : Tables)
    (position : Nat) : IntegerVector :=
  if layerSettings.rotary then tables.cosine.entry position
  else tabulate (settings.headDim / 2) fun _ => 2 ^ settings.rotaryScale

/-- The row of sines that `projections` uses at a position. -/
def sineRow (settings : Settings) (layerSettings : LayerSettings) (tables : Tables)
    (position : Nat) : IntegerVector :=
  if layerSettings.rotary then tables.sine.entry position
  else tabulate (settings.headDim / 2) fun _ => 0

/-- Bounds entry `column` of `rotate cosine sine headDim products` for all `products` whose entry at
each column is at most `productBound` of that column in absolute value. The rotary step mixes the
columns `2 * pair` and `2 * pair + 1` of a head. -/
def rotatedBound (cosine sine : IntegerVector) (headDim : Nat) (productBound : Nat → Int) (column : Nat) :
    Int :=
  let pair := (column % headDim) / 2
  if column % 2 = 0 then
    magnitude (cosine.entry pair) * productBound column
      + magnitude (sine.entry pair) * productBound (column + 1)
  else
    magnitude (sine.entry pair) * productBound (column - 1)
      + magnitude (cosine.entry pair) * productBound column

/-- A test that is enough for conditions 3 and 4 of one layer, at every position. -/
def attentionFits (settings : Settings) (layerSettings : LayerSettings) (tables : Tables)
    (layerWeights : LayerWeights) : Bool :=
  (allBelow settings.positions fun position =>
    (allBelow settings.queryWidth fun column =>
      roundShift
        (rotatedBound (cosineRow settings layerSettings tables position)
          (sineRow settings layerSettings tables position) settings.headDim
          (boxColumnBound layerWeights.query settings.width) column)
        layerSettings.queryShift ≤ 32767)                                                  -- 3
    && allBelow settings.keyValueWidth fun column =>
      roundShift
        (rotatedBound (cosineRow settings layerSettings tables position)
          (sineRow settings layerSettings tables position) settings.headDim
          (boxColumnBound layerWeights.key settings.width) column)
        layerSettings.keyShift ≤ 32767)                                                    -- 3
  && allBelow settings.keyValueWidth fun column =>
    roundShift (boxColumnBound layerWeights.value settings.width column)
      layerSettings.valueShift ≤ 32767                                                     -- 4

/-- Bounds the entry at `coordinate` of what attention adds to the stream: a head's output is a
rounded mean of values, which are clamped, so it lies in the box too. -/
def attentionAdditionBound (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (coordinate : Nat) : Int :=
  roundShift (boxColumnBound layerWeights.output settings.queryWidth coordinate)
    layerSettings.outputShift

/-! ## Feed-forward: conditions 5, 6 and 7 -/

/-- Bounds the up projection of a hidden unit. -/
def upBound (gatedWeights : GatedWeights) (width upShift unit : Nat) : Int :=
  roundShift (boxColumnBound gatedWeights.up width unit) upShift

/-- A test that is enough for conditions 6 and 7 of one gated block.
4,194,175 = 256 * 16,383 + 127. -/
def unitsFit (gatedWeights : GatedWeights) (width hidden gateShift upShift : Nat) : Bool :=
  allBelow hidden fun unit =>
    roundShift (boxColumnBound gatedWeights.gate width unit) gateShift ≤ 4194175   -- 6
    && upBound gatedWeights width upShift unit ≤ 32767                             -- 7

/-- Bounds `downSum units gatedWeights.down coordinate`: a hidden unit gives at most the SiLU
table's largest entry times its up projection's bound. -/
def downBound (tables : Tables) (gatedWeights : GatedWeights)
    (width hidden upShift coordinate : Nat) : Int :=
  columnBound
    (fun unit => largestMagnitude tables.silu.entries * upBound gatedWeights width upShift unit)
    gatedWeights.down hidden coordinate

/-- A test that is enough for conditions 5, 6 and 7 of one layer. 262,143 = 8 * 32,767 + 7. -/
def feedForwardFits (settings : Settings) (layerSettings : LayerSettings)
    (layerWeights : LayerWeights) (mixture : Bool) : Bool :=
  if mixture then
    unitsFit layerWeights.shared settings.width settings.expertHidden layerSettings.gateShift
      layerSettings.upShift
    && (allBelow settings.experts fun expert =>
      roundShift (boxColumnBound layerWeights.router settings.width expert)
        layerSettings.routerShift ≤ 262143                                                 -- 5
      && unitsFit (layerWeights.routed.entry expert) settings.width settings.expertHidden
        layerSettings.routedGateShift layerSettings.routedUpShift)
  else
    unitsFit layerWeights.shared settings.width settings.hidden layerSettings.gateShift
      layerSettings.upShift

/-- Bounds the entry at `coordinate` of what the feed-forward block adds to the stream. The router's
choice depends on the prompt, so the bound takes the largest bound over all routed experts. -/
def feedForwardAdditionBound (settings : Settings) (layerSettings : LayerSettings)
    (tables : Tables) (layerWeights : LayerWeights) (mixture : Bool) (coordinate : Nat) : Int :=
  if mixture then
    roundShift
      (downBound tables layerWeights.shared settings.width settings.expertHidden
          layerSettings.upShift coordinate
        + maxUpTo
          (fun expert => downBound tables (layerWeights.routed.entry expert) settings.width
            settings.expertHidden layerSettings.routedUpShift coordinate)
          (settings.experts - 1))
      layerSettings.downShift
  else
    roundShift
      (downBound tables layerWeights.shared settings.width settings.hidden layerSettings.upShift
        coordinate)
      layerSettings.downShift

/-! ## The stream -/

/-- Bounds the entry at `coordinate` of every token's embedding. -/
def embeddingBound (settings : Settings) (weights : Weights) (coordinate : Nat) : Int :=
  maxUpTo (fun token => magnitude ((weights.embedding.entry token).entry coordinate))
    (settings.vocabulary - 1)

/-- Bounds the entry at `coordinate` of what a layer adds to the stream in its two steps together.
-/
def layerAdditionBound (settings : Settings) (tables : Tables) (weights : Weights)
    (layer coordinate : Nat) : Int :=
  attentionAdditionBound settings (settings.perLayer.entry layer) (weights.perLayer.entry layer)
      coordinate
    + feedForwardAdditionBound settings (settings.perLayer.entry layer) tables
      (weights.perLayer.entry layer) (settings.isMixture layer) coordinate

/-- Bounds the entry at `coordinate` of the stream that enters a layer; with the number of layers in
the place of `layer`: of the stream that the final norm reads. The additions' bounds do not depend
on the stream, so the bound grows by a sum. -/
def streamBound (settings : Settings) (tables : Tables) (weights : Weights)
    (layer coordinate : Nat) : Int :=
  embeddingBound settings weights coordinate
    + sumOver layer fun below => layerAdditionBound settings tables weights below coordinate

/-- Bounds the entry at `coordinate` of the stream after the attention of a layer. -/
def streamBoundAfterAttention (settings : Settings) (tables : Tables) (weights : Weights)
    (layer coordinate : Nat) : Int :=
  streamBound settings tables weights layer coordinate
    + attentionAdditionBound settings (settings.perLayer.entry layer)
      (weights.perLayer.entry layer) coordinate

/-! ## The check -/

/-- A routed expert's input, the normed row times the sigmoid table's entry, shifted by 16, stays in
the box. -/
def routedInputFits (tables : Tables) : Bool :=
  roundShift (largestMagnitude tables.sigmoid.entries * activationBound) 16 ≤ activationBound

/-- The check of one layer. -/
def layerFits (settings : Settings) (tables : Tables) (weights : Weights) (layer : Nat) : Bool :=
  let layerSettings := settings.perLayer.entry layer
  let layerWeights := weights.perLayer.entry layer
  normFits layerSettings.attentionBits layerSettings.attentionShift layerSettings.attentionEps
      settings.width (streamBound settings tables weights layer)
  && attentionFits settings layerSettings tables layerWeights
  && normFits layerSettings.feedForwardBits layerSettings.feedForwardShift
      layerSettings.feedForwardEps settings.width
      (streamBoundAfterAttention settings tables weights layer)
  && feedForwardFits settings layerSettings layerWeights (settings.isMixture layer)

/-- **The check.** It reads the settings, the tables and the weights, and no prompt. It counts only
beside `wellFormed`: it does not test that the arrays have their sizes, and it passes on empty
arrays. -/
def boxWorstCaseCheck (settings : Settings) (tables : Tables) (weights : Weights) : Bool :=
  routedInputFits tables
  && (allBelow settings.layers fun layer => layerFits settings tables weights layer)
  && normFits settings.finalBits settings.finalShift settings.finalEps settings.width
      (streamBound settings tables weights settings.layers)

end IntegerTransformer.Bounds
