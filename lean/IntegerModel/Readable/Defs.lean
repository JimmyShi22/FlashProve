-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/Defs.lean: what ties the arguments of IntegerTransformer.model
(IntegerModel/Model.lean: settings, tables and weights as arrays) to the library's
(Inst/Model/Program.lean: sizes P, scales κ, nf, tables tbs and weights w as functions).
The clauses on every layer's scales, on tables and on weights speak only of positions inside the
shapes, but for SameTables.rows and Same.emb, which fix a size. (The model's check wellFormed, which
model_eq (IntegerModel/Readable/Main.lean) and Feeds (IntegerModel/Readable/Tie.lean) carry in
addition to these clauses, also requires the exact sizes of the cosine and sine tables and of every
array of weights that the model reads.)
Definitions, and three short lemmas: the sizes do not depend on the scales.
-/
import Inst.Model.Program
import IntegerModel.Model

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model

/-- the ten sizes; Tmax is the most tokens that a prompt can have -/
structure SameSizes (P : Params) (Tmax : ℕ) (s : IntegerTransformer.Settings) : Prop where
  positions : s.positions = Tmax
  layers : s.layers = P.layers
  width : s.width = P.d
  queryHeads : s.queryHeads = P.nq
  keyValueHeads : s.keyValueHeads = P.nkv
  headDim : s.headDim = P.ch
  hidden : s.hidden = P.f
  expertHidden : s.expertHidden = P.fe
  experts : s.experts = P.nexp
  vocabulary : s.vocabulary = P.V

/-- The scales of layer L: p compared with the library's k. The router's shift and the routed
expert's two shifts are required only in a layer with experts. (k.expRows: SameTables.rows.) -/
structure SameScales (L : ℕ) (p : IntegerTransformer.LayerSettings) (k : LayerScale) : Prop where
  M1 : p.attentionBits = k.n1.M
  K1 : p.attentionShift = k.n1.K
  eps1 : p.attentionEps = k.n1.eps
  kq : p.queryShift = k.kq
  kk : p.keyShift = k.kk
  kv : p.valueShift = k.kv
  sh : p.softmaxShift = k.sh
  ko : p.outputShift = k.ko
  M2 : p.feedForwardBits = k.n2.M
  K2 : p.feedForwardShift = k.n2.K
  eps2 : p.feedForwardEps = k.n2.eps
  kg : p.gateShift = k.kg
  ku : p.upShift = k.ku
  kd : p.downShift = k.kd
  kr : hasExperts L → p.routerShift = k.kr
  kgR : hasExperts L → p.routedGateShift = k.kg'
  kuR : hasExperts L → p.routedUpShift = k.ku'

/-- The five tables compared with the library's tables tb of layer L: at positions below Tmax and
angles below ch / 2; at softmax keys below the table's size, which is rows (in Same: the layer's
expRows, the number of rows in use of the table Exp; the model has one table, so all layers have the
same number); at the SiLU keys -32,640 .. 32,639 and the sigmoid keys -16,376 .. 16,383: two
intervals that hold every key that the library's program forms
(IntegerModel/Readable/FeedForward.lean: siluKey_bd, sigmKey_bd) and that the model forms
(IntegerModel/Readable/Reads.lean: gateKeyOf_range, routerLogitOf_range); wellFormed requires the
tables to cover a little more. The library reads both at key + 2^15. Whether layer L has the rotary
step is a setting in the model; in the library it is encoded in C and S. -/
structure SameTables (P : Params) (Tmax : ℕ) (s : IntegerTransformer.Settings)
    (p : IntegerTransformer.LayerSettings) (tables : IntegerTransformer.Tables)
    (tb : Tables) (L : ℕ) (rows : ℤ) : Prop where
  cos : ∀ i < Tmax, ∀ j < P.ch / 2,
    (if p.rotary = true then (tables.cosine.entry i).entry j else 2 ^ s.rotaryScale) = tb.C L i j
  sin : ∀ i < Tmax,
    ∀ j < P.ch / 2, (if p.rotary = true then (tables.sine.entry i).entry j else 0) = tb.S L i j
  rows : (tables.exponential.size : ℤ) = rows
  exp : ∀ u < tables.exponential.size, tables.exponential.entry u = tb.Exp (u : ℤ)
  silu : ∀ key : ℤ, -32640 ≤ key → key ≤ 32639 → tables.silu.read key = tb.SILU (key + 2 ^ 15)
  sigm : ∀ key : ℤ, -16376 ≤ key → key ≤ 16383 → tables.sigmoid.read key = tb.SIGM (key + 2 ^ 15)

/-- The weights of layer L. A dense layer has f hidden units; a layer with experts has fe shared
ones, a router and nexp experts of fe units. -/
structure SameLayer (P : Params) (L : ℕ) (W : IntegerTransformer.LayerWeights) (w : LayerW) :
    Prop where
  Wq : ∀ j < P.d, ∀ c < P.nq * P.ch, (W.query.entry j).entry c = w.Wq j c
  Wk : ∀ j < P.d, ∀ c < P.nkv * P.ch, (W.key.entry j).entry c = w.Wk j c
  Wv : ∀ j < P.d, ∀ c < P.nkv * P.ch, (W.value.entry j).entry c = w.Wv j c
  Wo : ∀ j < P.nq * P.ch, ∀ c < P.d, (W.output.entry j).entry c = w.Wo j c
  Wg : ∀ j < P.d,
    ∀ c < (if hasExperts L then P.fe else P.f), (W.shared.gate.entry j).entry c = w.Wg j c
  Wu : ∀ j < P.d,
    ∀ c < (if hasExperts L then P.fe else P.f), (W.shared.up.entry j).entry c = w.Wu j c
  Wd : ∀ j < (if hasExperts L then P.fe else P.f),
    ∀ c < P.d, (W.shared.down.entry j).entry c = w.Wd j c
  Wr : hasExperts L → ∀ j < P.d, ∀ e < P.nexp, (W.router.entry j).entry e = w.Wr j e
  Eg : hasExperts L →
    ∀ e < P.nexp, ∀ j < P.d, ∀ c < P.fe, ((W.routed.entry e).gate.entry j).entry c = w.Eg e j c
  Eu : hasExperts L →
    ∀ e < P.nexp, ∀ j < P.d, ∀ c < P.fe, ((W.routed.entry e).up.entry j).entry c = w.Eu e j c
  Ed : hasExperts L →
    ∀ e < P.nexp, ∀ j < P.fe, ∀ c < P.d, ((W.routed.entry e).down.entry j).entry c = w.Ed e j c

/-- Three lemmas: the clauses on sizes, tables and weights read only P's sizes. So, if they hold at
P, they hold at P.at k (P with a layer's scales k) for every k. -/
theorem SameSizes.at {P : Params} {Tmax : ℕ} {s : IntegerTransformer.Settings}
    (h : SameSizes P Tmax s) (k : LayerScale) : SameSizes (P.at k) Tmax s :=
  ⟨h.positions, h.layers, h.width, h.queryHeads, h.keyValueHeads, h.headDim, h.hidden,
    h.expertHidden, h.experts, h.vocabulary⟩
theorem SameTables.at {P : Params} {Tmax : ℕ} {s : IntegerTransformer.Settings}
    {p : IntegerTransformer.LayerSettings} {tables : IntegerTransformer.Tables} {tb : Tables}
    {L : ℕ} {rows : ℤ} (h : SameTables P Tmax s p tables tb L rows) (k : LayerScale) :
    SameTables (P.at k) Tmax s p tables tb L rows :=
  ⟨h.cos, h.sin, h.rows, h.exp, h.silu, h.sigm⟩
theorem SameLayer.at {P : Params} {L : ℕ} {W : IntegerTransformer.LayerWeights} {w : LayerW}
    (h : SameLayer P L W w) (k : LayerScale) : SameLayer (P.at k) L W w :=
  ⟨h.Wq, h.Wk, h.Wv, h.Wo, h.Wg, h.Wu, h.Wd, h.Wr, h.Eg, h.Eu, h.Ed⟩

/-- The model's three arguments hold the library's numbers: sizes, every layer's scales, the final
norm's, the tables, every layer's weights, embedding and head. -/
structure Same (P : Params) (Tmax : ℕ) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (w : Weights) (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
    (weights : IntegerTransformer.Weights) : Prop where
  sizes : SameSizes P Tmax s
  scales : ∀ L < P.layers, SameScales L (s.perLayer.entry L) (κ L)
  finalBits : s.finalBits = nf.M
  finalShift : s.finalShift = nf.K
  finalEps : s.finalEps = nf.eps
  tables : ∀ L < P.layers, SameTables P Tmax s (s.perLayer.entry L) tables (tbs L) L (κ L).expRows
  layer : ∀ L < P.layers, SameLayer P L (weights.perLayer.entry L) (w.layer L)
  /-- A token's row of the embedding, as an array, is the stream's row at the token's position
before the first layer; so its length is required too. -/
  emb : ∀ a < P.V, weights.embedding.entry a = (Array.range P.d).map (w.Emb a)
  head : ∀ j < P.d, ∀ v < P.V, (weights.head.entry j).entry v = w.H j v

end IntegerModel.Readable
