-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ModelWeights.lean

The weights of the model as arrays of integers, and the model function. Definitions only.
`settingsAreValid`: the test on the sizes and quantization parameters.
`weightsAreValid`: the test that says which arrays are weights at given settings.
`ModelWeights settings`: the arrays that pass the test. `modelNextToken`: the next token.
The settings are no part of the weights: they are an argument of the type and of the function.
Limits: whoever makes the weights chooses all numbers. No theorem says that the converted weights of
a real model pass the test, what the five tables contain, or that the function is close in value to
the public model whose sizes it has (`hasModelSizes`); IntegerModel/Model.lean lists the known
differences.
See the comments at `weightsAreValid` and `lookupTables`.
-/
import IntegerModel.Model
import Inst.Model.TablesData

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-! ## 1. The five tables: constants of the system -/

/-- Entry `index` of packed numbers: `bits` bits per entry, 1,024 entries in each number of the
array. -/
def packedEntry (packed : Array Nat) (bits index : Nat) : Nat :=
  (packed.getD (index / 1024) 0 >>> (bits * (index % 1024))) % 2 ^ bits

/-- Intended content: 4,096 times the cosine of the rotary angle of `position` and `pair`. -/
def cosineTable : Matrix :=
  tabulate 1024 fun position => tabulate 64 fun pair =>
    clamp ((packedEntry Inst.Model.Data.cos 14 (64 * position + pair) : Int) - 4096) 4096

/-- Intended content: 4,096 times the sine of the same angle. -/
def sineTable : Matrix :=
  tabulate 1024 fun position => tabulate 64 fun pair =>
    clamp ((packedEntry Inst.Model.Data.sin 14 (64 * position + pair) : Int) - 4096) 4096

/-- Intended content: the exponential of the softmax, as a function of the scaled distance to the
largest score, 4,096 at distance 0. The code only forces every entry into 1 .. 4,096. -/
def exponentialTable : IntegerVector :=
  tabulate 2307 fun distance => max 1 (min (packedEntry Inst.Model.Data.exp 13 distance : Int) 4096)

/-- Intended content: 64 times SiLU of the scaled key, for the keys -32,768 .. 32,767. The packed
numbers cover the keys -16,384 .. 16,383; outside these the table is constant, and every entry is
cut to -4,095 .. 4,095.
So this activation is capped, at about 64, where the true SiLU grows without bound: a difference
from the public model. -/
def siluTable : IntegerVector :=
  tabulate 65536 fun index =>
    clamp ((packedEntry Inst.Model.Data.silu 13
      (min (max ((index : Int) - 32768) (-16384)) 16383 + 16384).toNat : Int) - 4095) 4095

/-- Intended content: 65,536 times the sigmoid of key / 256, for the keys -16,384 .. 16,383. -/
def sigmoidTable : IntegerVector :=
  tabulate 32768 fun index => 16 * min (packedEntry Inst.Model.Data.sigm 13 index : Int) 4096

/-- The five tables of the model. They are the same for all settings and weights.
No theorem says what they contain as a whole: `wellFormed` checks only their sizes, key ranges and
signs. -/
def lookupTables : Tables where
  cosine := cosineTable
  sine := sineTable
  exponential := exponentialTable
  silu := { lowestKey := -32768, entries := siluTable }
  sigmoid := { lowestKey := -16384, entries := sigmoidTable }

/-! ## 2. The test on the settings -/

/-- The sizes. The window of 1,024 positions and the rotary scale 12 (the cosine and sine tables are
scaled by 2^12) are this system's; the other nine sizes are those of Llama 4 Maverick's text model.
Every fourth layer has no rotary step. Which layers are mixtures of experts is fixed in
`Settings.isMixture` (IntegerModel/Model.lean): the odd ones. -/
def hasModelSizes (settings : Settings) : Bool :=
  settings.positions == 1024
  && settings.layers == 48 && settings.width == 5120
  && settings.queryHeads == 40 && settings.keyValueHeads == 8 && settings.headDim == 128
  && settings.hidden == 16384 && settings.expertHidden == 8192 && settings.experts == 128
  && settings.vocabulary == 202048
  && settings.rotaryScale == 12
  && (List.range 48).all fun layer => (settings.perLayer.entry layer).rotary == (layer % 4 != 3)

/-- The three numbers of a norm are in the ranges of a lawful table of scales (`Cm.Scales.Lawful`,
Cm/Rel2.lean; by `Cm.lawful_iff`, Cm/Rel2Proofs.lean, that is `Inst.Model.Lawful`,
Inst/Model/Scales.lean, with the policy of exact match), for which the library's theorems are
stated. `1 ≤ eps` excludes a division by 0; `shift ≤ bits` excludes, among others, norms that return
0 on every input. -/
def normInRange (bits shift : Nat) (eps : Int) : Bool :=
  1 ≤ eps && eps < 2 ^ 48 && 24 ≤ bits && bits ≤ 47 && 17 ≤ shift && shift ≤ 32
  && bits ≤ shift + 14 && shift ≤ bits

/-- The quantization parameters of one layer are in the ranges of a lawful table of scales, but
for the router's shift and the routed expert's two shifts of a dense layer: a lawful table has
numbers in range there, which the model does not read. A dense layer has no router: these three
shifts are 0. -/
def layerSettingsInRange (mixture : Bool) (layer : LayerSettings) : Bool :=
  5 ≤ layer.queryShift && layer.queryShift ≤ 32 && 5 ≤ layer.keyShift && layer.keyShift ≤ 32
  && (layer.queryShift == layer.keyShift || (16 ≤ layer.queryShift && 16 ≤ layer.keyShift))
  && 1 ≤ layer.valueShift && layer.valueShift ≤ 24
  && 1 ≤ layer.outputShift && layer.outputShift ≤ 19
  && 1 ≤ layer.gateShift && layer.gateShift ≤ 24 && 1 ≤ layer.upShift && layer.upShift ≤ 24
  && 10 ≤ layer.downShift && layer.downShift ≤ 19
  && 4 ≤ layer.softmaxShift && layer.softmaxShift ≤ 12
  && normInRange layer.attentionBits layer.attentionShift layer.attentionEps
  && normInRange layer.feedForwardBits layer.feedForwardShift layer.feedForwardEps
  && (if mixture then
      8 ≤ layer.routerShift && layer.routerShift ≤ 24
      && 1 ≤ layer.routedGateShift && layer.routedGateShift ≤ 24
      && 1 ≤ layer.routedUpShift && layer.routedUpShift ≤ 24
    else layer.routerShift == 0 && layer.routedGateShift == 0 && layer.routedUpShift == 0)

/-- All quantization parameters are in range, and each group of four layers has one softmax shift
(the argument system treats four layers as one group). -/
def settingsInRange (settings : Settings) : Bool :=
  normInRange settings.finalBits settings.finalShift settings.finalEps
  && (List.range 48).all fun layer =>
      layerSettingsInRange (settings.isMixture layer) (settings.perLayer.entry layer)
      && (settings.perLayer.entry layer).softmaxShift
          == (settings.perLayer.entry (4 * (layer / 4))).softmaxShift

/-- The test on the settings: the sizes, the ranges of all quantization parameters, and one entry of
parameters for each layer. The settings that pass it are exactly the settings of the library's
lawful tables of scales (`settingsAreValid_iff`, IntegerModel/Arrays/OfIndex.lean). Many tables have
the same settings (an argument, no theorem: IntegerModel/Arrays/OfTensors.lean).
At settings that pass the test there are weights (`nonempty_modelWeights`,
IntegerModel/Arrays/OfIndex.lean). -/
def settingsAreValid (settings : Settings) : Bool :=
  hasModelSizes settings && settingsInRange settings
  && settings.perLayer.size == settings.layers

/-! ## 3. The test on the weights -/

/-- Every entry of the matrix is in `low .. high`. -/
def entriesWithin (low high : Int) (matrix : Matrix) : Bool :=
  matrix.all fun row => row.all fun entry => low ≤ entry && entry ≤ high

/-- The three matrices of a gated block contain weights of 13 bits. -/
def gatedWithin (block : GatedWeights) : Bool :=
  entriesWithin (-4096) 4095 block.gate && entriesWithin (-4096) 4095 block.up
  && entriesWithin (-4096) 4095 block.down

/-- The matrices of one layer contain weights of 13 bits. A dense layer has no router and no routed
experts. -/
def layerWeightsInRange (mixture : Bool) (layer : LayerWeights) : Bool :=
  entriesWithin (-4096) 4095 layer.query && entriesWithin (-4096) 4095 layer.key
  && entriesWithin (-4096) 4095 layer.value && entriesWithin (-4096) 4095 layer.output
  && gatedWithin layer.shared
  && (if mixture then entriesWithin (-4096) 4095 layer.router && layer.routed.all gatedWithin
    else layer.router.size == 0 && layer.routed.size == 0)

/-- All weights are in range: an entry of the embedding is a sum of four signed bytes at 2^0, 2^8,
2^16, 2^24; all other weights have 13 bits. -/
def weightsInRange (settings : Settings) (weights : Weights) : Bool :=
  entriesWithin (-2155905152) 2139062143 weights.embedding
  && entriesWithin (-4096) 4095 weights.head
  && (List.range 48).all fun layer =>
      layerWeightsInRange (settings.isMixture layer) (weights.perLayer.entry layer)

/-- The test: which arrays are weights at the given settings. `wellFormed`
(IntegerModel/Model.lean) checks that every array of weights that the model reads has
exactly its size.
At valid settings the test passes exactly the arrays of the library's well-formed tensors
(`weightsAreValid_arrays`, IntegerModel/Arrays/OfTensors.lean; `wf_weightsTo`, `weights_back`,
IntegerModel/Arrays/ToTensors.lean).
It fixes sizes and ranges, not the model. All-zero matrices pass, and some valid settings make
every layer add nothing (by hand, no theorem: the settings of the table `Cm.sIdle`,
Cm/Rel2Idle.lean). The architecture is fixed by the two tests, the text of
`IntegerTransformer.model` and the five tables together. -/
def weightsAreValid (settings : Settings) (weights : Weights) : Bool :=
  wellFormed settings lookupTables weights && weightsInRange settings weights

/-! ## 4. The weights and the model -/

/-- The weights at the given settings: arrays that pass the test. They are the weights of one model;
its quantization parameters are part of the public settings, and a fitted model's quantization
parameters are made from its weights. At settings that do not pass `settingsAreValid` the type may
be empty or hold arrays of other sizes; the theorems that tie it to the library are stated at valid
settings. -/
def ModelWeights (settings : Settings) : Type :=
  { weights : Weights // weightsAreValid settings weights = true }

/-- The model: the next token after `tokens`, by greedy decoding of the integer program. At valid
settings it is `none` exactly if there is no token or more than 1,024, a token is 202,048 or more,
or a range condition of the program fails at some position (no one theorem says so: it follows by
hand from `IntegerTransformer.model_eq_some`, IntegerModel/Readable/Facts.lean; from
`valid_wellFormed`, IntegerModel/Arrays/ToTensors.lean, since the weights are valid by their type;
and from the sizes in `hasModelSizes`). -/
def modelNextToken (settings : Settings) (weights : ModelWeights settings) (tokens : List Nat) :
    Option Nat :=
  model settings lookupTables weights.val tokens.toArray

end VerifiableInference
