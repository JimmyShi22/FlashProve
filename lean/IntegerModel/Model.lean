-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-!
# The text model of Llama 4 Maverick's kind, in whole numbers

This file is written for one function, `model`, defined at its end: settings, tables, weights and
the tokens so far go in, and the next token comes out, or `none` where the model is not defined.
Every operation is an exact operation on whole numbers (`Int`, which has no upper limit and cannot
overflow). No floating-point number occurs.

The architecture: token embedding; then layers, each with a norm, grouped-query causal attention
with rotary position encoding, a residual addition, a second norm, a gated (SiLU) feed-forward block
and a residual addition; then a final norm, the output matrix and the greedy choice. If the settings
have experts, the feed-forward block of every second layer is a mixture of experts: one shared
expert, and the one routed expert that the router ranks first.

It follows sections 1 to 10 of docs/model.md, "The integer model": with the router's and the gate's
clamp (part 5) and with 2^78 in condition 1. In that document's section 10 these are the parameter
lines `rcl 1`, `gcl 1` and `xl 5`. A comment such as `-- Vx` gives the document's symbol, and
"section 6" means a section of it. The letters below are the document's too, and part 2 gives each
beside its field: d, dh, f and fe are sizes, kq, kk and kd are shifts, cs is the scale of the rotary
tables, sh the shift in the softmax.

In this file "prompt" means all the tokens so far. In a statement about a prompt and output tokens,
it is the prompt followed by the output tokens before the one that is asked for. So the bound `T` is
on both together.

## Compared with the public Llama 4 Maverick text model

What differs:
- The norm divides by the root of the sum of squares, not of their mean. The factor sqrt(d) sits in
  the scales and the weights. `eps` is added to the sum, in the stream's units.
- The norms have no gains. The conversion from the model's files multiplies each norm's gains, and
  the constant sqrt(d) / 64, into the matrices that read the norm, and 1 / sqrt(dh) into the query
  matrix.
- Cosine, sine, the softmax's exponential, SiLU and the sigmoid are tables, and the tables are
  arguments. Nothing in this file says what they hold, but for what `wellFormed` tests: their sizes
  and keys, and of their entries only the signs of the softmax table's. Section 4 says how they are
  made.
- The rotary tables are scaled by 2^cs, and the shifts kq and kk take that factor out again. The
  SiLU table is scaled by 64, and the shift kd takes that out.
- In the softmax the distance to the top score is divided by 2^sh and rounded down, the table gives
  0 from its end on, and there is one rounded division, after the weighted sum of the values.
- The shared and the routed expert's down projections are added before one rounding shift.
- Normed rows, queries, keys and values are cut to 12 bits. The router's clamp is not monotone at
  its two ends: a logit of 64 or more can rank below one just under 64. The key of the SiLU table is
  cut as well (part 5), which only saturates if the table is constant beyond. The sigmoid table is
  scaled by 65,536; the fixed shift 16 takes that out, and the routed expert's scaled input is
  rounded there.
- The SiLU table's entries are cut to -smax .. smax (part 2), so the activation is capped where the
  true SiLU grows without bound. At the library's own table the cap is about 64 (`siluTable`,
  VerifiableInference/ModelWeights.lean).
- After every product with a weight matrix but the last, which gives the logits, the sum is divided
  by a power of two and rounded (the shifts of part 2; queries and keys are shifted after the rotary
  step), so each activation is a fixed-point number with its own scale. Limit: how far the result is
  from the floating-point model's is not said here. docs/model.md reports no
  measurement of it and points to docs/limits.md.
- The weights are whole numbers. The conversion makes them of 13 bits; this function takes any.
- Ties, among experts and among tokens, go to the lowest index.
- The function is partial: eight range conditions (part 7).

What is left out:
- The normalization of queries and keys after the rotary step, which is off in Maverick.
- Attention within chunks of 8,192 tokens, and the factor on the queries of the layers without
  rotary step ("temperature tuning"). Both change nothing below 8,192 positions. The number of
  positions T is a setting, so this function has Maverick's form only for T < 8,192.
- The vision part, the tokenizer, any choice but the greedy one, and the cache of keys and values,
  which is a way to compute and not a part of the function.

Which layers have no rotary step is a setting (Maverick: each fourth). Which layers have experts, if
there are any, is a fixed rule: the odd ones (section 2).

Fixed here, settings in the public code, at Maverick's values: one routed expert for each token
(num_experts_per_tok 1), no bias vectors (attention_bias false), an output matrix separate from the
embedding (tie_word_embeddings false), f = 2 fe (16,384 and 8,192). The rotary base 500,000, without
scaling (rope_scaling null), belongs to the generation of the tables.

The same as the public code (transformers 5.17.0, modeling_llama4.py), where one might doubt it: the
rotary step turns neighbouring pairs (its lines 238-241), query head h reads head h / (n_h / n_g)
(253-254), and the sigmoid scales the routed expert's input (169-170). That is by reading, not by a
theorem.

## How to read this file

Part 1 is arithmetic and part 2 the three arguments. Parts 3 to 6 are the transformer: they compute
every named value of docs/model.md at every position and test nothing. Part 7 states the range
conditions on those values, part 8 what the arguments must be like, and part 9 is the function. A
reader in a hurry reads the definitions of parts 3 to 6 and part 9, fifteen definitions in all. The
record before each definition only names its values.

Only Lean's core library is used. Every read at an index goes through one function: `v.entry k` is
entry `k` of `v`, counted from 0. A read outside an array would give 0 (or an empty array, or a
record of such). `model` gives `none` unless the arguments fit together (`wellFormed`) and the
tokens are a prompt (`isPrompt`). Then no read should be outside. A note "Reads:" at each definition
but `KeyedTable.read` says why, and `IntegerModel/Readable/Reads.lean` proves the sizes and bounds
that these notes name. Limit: no theorem says of this file's reads themselves that they are inside.
`IntegerModel/Readable/Checked.lean` proves that the model, written again with checked
reads, gives the same result; its module docstring says what that shows and what it does not.
-/

/-- Entry `k` of an array, counted from 0. Outside the array it is the type's default value: 0 for a
number, an empty array for an array, a record of such for a record. -/
def Array.entry {α : Type} [Inhabited α] (v : Array α) (k : Nat) : α :=
  v.getD k default

namespace IntegerTransformer

/-! ## 1. Arithmetic (section 1)

On `Int`, Lean's `a / b` with `b > 0` rounds down (towards minus infinity), and `a % b` is in
`0 .. b - 1`. -/

example : (-7 : Int) / 2 = -4 ∧ (-7 : Int) % 2 = 1 := by decide

/-- A vector of whole numbers. -/
abbrev IntegerVector := Array Int

/-- A matrix, as the array of its rows. A weight matrix has the input index first,
`(W.entry input).entry output`, as in section 1. A matrix of activations has the position first. -/
abbrev Matrix := Array IntegerVector

/-- The array `f 0, f 1, .., f (n - 1)`. -/
def tabulate {α : Type} (n : Nat) (f : Nat → α) : Array α :=
  Array.ofFn (n := n) fun i => f i.val

/-- The sum `f 0 + f 1 + .. + f (n - 1)`. -/
def sumOver : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumOver n f + f n

/-- The largest of `f 0, .., f i` (the last index is included). -/
def maxUpTo (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | i + 1 => max (maxUpTo f i) (f (i + 1))

/-- The argmax: the least index below `n` at which `f` is largest, so ties go to the lowest index (0
if `n = 0`). -/
def firstArgmax (f : Nat → Int) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let best := firstArgmax f n
    if f best < f n then n else best

/-- `rq(a, k)`: `a` divided by `2^k` and rounded to the nearest whole number, ties towards plus
infinity. It is meant for `k ≥ 1`, and `wellFormed` asks that of every shift that is handed to
`roundShift`. The divisor is a power of two, so it is positive. -/
def roundShift (a : Int) (k : Nat) : Int :=
  (a + 2 ^ (k - 1)) / 2 ^ k

/-- `clamp(a; b)`: `a` cut to the interval `-b .. b`. -/
def clamp (a b : Int) : Int :=
  min (max a (-b)) b

/-- `C_w = 2^11 - 1`: the bound of the 12-bit clamp of normed rows, queries, keys and values. -/
def activationBound : Int := 2047

/-- The balanced low byte of `a`: the number in `-128 .. 127` that differs from `a` by a multiple
of 256. -/
def balancedLowByte (a : Int) : Int :=
  (a + 128) % 256 - 128

/-- `integerSquareRoot(a)`: the largest `r` with `r * r ≤ a` (proved: `isqrt_spec` in
`IntegerModel/Readable/Facts.lean`). It is computed from the root of `a / 4`, which gives all binary
digits of the root but the last. -/
def integerSquareRoot (a : Nat) : Nat :=
  if a = 0 then 0
  else
    let r := 2 * integerSquareRoot (a / 4)
    if (r + 1) * (r + 1) ≤ a then r + 1 else r
termination_by a
decreasing_by omega

/-- The entrywise sum of two vectors of the same length. Reads: `k` is below that length. -/
def addVectors (x y : IntegerVector) : IntegerVector :=
  tabulate x.size fun k => x.entry k + y.entry k

/-- A row vector times a weight matrix: entry `j` is the sum over `k` of `x[k] W[k][j]`. Reads: `W`
has as many rows as `x` has entries, and `outputs` columns. -/
def product (x : IntegerVector) (W : Matrix) (outputs : Nat) : IntegerVector :=
  tabulate outputs fun j => sumOver x.size fun k => x.entry k * (W.entry k).entry j

/-! ## 2. The arguments: settings, tables, weights (sections 2 to 4) -/

/-- The quantization scales of one layer (section 3). A shift `k` divides by `2^k`. docs/model.md
has one `eps1` and one `eps2` for all layers, and a parameter file gives every layer the same pair.
Here each layer has its own pair, as in the library's soundness theorem (the record `LayerScale`,
Inst/Model/Program.lean). -/
structure LayerSettings where
  attentionBits : Nat     -- M1: the two exponents of the norm before attention
  attentionShift : Nat    -- K1
  attentionEps : Int      -- eps1
  queryShift : Nat        -- kq
  keyShift : Nat          -- kk
  valueShift : Nat        -- kv
  rotary : Bool           -- rp: does this layer encode positions?
  softmaxShift : Nat      -- sh
  outputShift : Nat       -- ko
  feedForwardBits : Nat   -- M2: the two exponents of the norm before the feed-forward block
  feedForwardShift : Nat  -- K2
  feedForwardEps : Int    -- eps2
  gateShift : Nat         -- kg
  upShift : Nat           -- ku
  downShift : Nat         -- kd
  routerShift : Nat       -- kr   (these three: mixture-of-experts layers only)
  routedGateShift : Nat   -- kgR
  routedUpShift : Nat     -- kuR
  deriving Inhabited

/-- The model's sizes and every other number that it reads, except the tables, the weights and the
tokens (sections 2 and 3). -/
structure Settings where
  positions : Nat         -- T: the most tokens that a prompt can have
  layers : Nat            -- L
  width : Nat             -- d: the width of the residual stream
  queryHeads : Nat        -- n_h
  keyValueHeads : Nat     -- n_g, which divides n_h
  headDim : Nat           -- dh, even
  hidden : Nat            -- f: the hidden units of a dense feed-forward block
  expertHidden : Nat      -- fe: the hidden units of one expert; f = 2 fe
  experts : Nat           -- NE: the number of routed experts; 0: every layer is dense
  vocabulary : Nat        -- V
  rotaryScale : Nat       -- cs: a layer without position encoding uses cosine 2^cs and sine 0
  finalEps : Int          -- epsF
  finalBits : Nat         -- MF
  finalShift : Nat        -- KF
  perLayer : Array LayerSettings
  deriving Inhabited

/-- `dq`: the width of all query heads together. -/
def Settings.queryWidth (s : Settings) : Nat := s.queryHeads * s.headDim

/-- `dkv`: the width of all key heads together, and of all value heads together. -/
def Settings.keyValueWidth (s : Settings) : Nat := s.keyValueHeads * s.headDim

/-- Is layer `l` a mixture-of-experts layer? If there are experts, the odd layers are (section 2).
-/
def Settings.isMixture (s : Settings) (l : Nat) : Bool :=
  s.experts > 0 && l % 2 == 1

/-- A table that is read with a key that can be negative: `entries[0]` belongs to the key
`lowestKey`. -/
structure KeyedTable where
  lowestKey : Int
  entries : IntegerVector
  deriving Inhabited

/-- The table's entry at a key; 0 at a key that the table does not have. -/
def KeyedTable.read (table : KeyedTable) (key : Int) : Int :=
  if table.lowestKey ≤ key then table.entries.entry (key - table.lowestKey).toNat else 0

/-- The five tables, given by value. The comments say what section 4 puts into them; nothing here
tests it. `expS`, `rx`, `eg` and `smax` are parameters of the tables' generation, which this file
does not read: the scale and the step of the exponential, the step of SiLU's keys, and the bound of
SiLU's values (section 2). -/
structure Tables where
  cosine : Matrix        -- C(t, i), for position t and i < dh / 2: 2^cs times a cosine
  sine : Matrix          -- S(t, i): 2^cs times a sine
  exponential : IntegerVector      -- EX[u] for u < u0, the array's size: 2^expS times exp(-u / 2^rx); beyond, the model takes 0
  silu : KeyedTable      -- Ts[c] for the keys -32,768 .. 32,767: 64 SiLU(c / 2^eg), cut to -smax .. smax
  sigmoid : KeyedTable   -- Sig[c], at least for the keys -16,384 .. 16,383: 65,536 times the sigmoid of c / 256
  deriving Inhabited

/-- The three matrices of a gated feed-forward block with `h` hidden units. -/
structure GatedWeights where
  gate : Matrix  -- Wg or Wgr_e, d x h
  up : Matrix    -- Wu or Wur_e, d x h
  down : Matrix  -- Wd or Wdr_e, h x d
  deriving Inhabited

/-- The weights of one layer (section 3). -/
structure LayerWeights where
  query : Matrix               -- Wq, d x dq
  key : Matrix                 -- Wk, d x dkv
  value : Matrix               -- Wv, d x dkv
  output : Matrix              -- Wo, dq x d
  shared : GatedWeights        -- the dense block (h = f), or the shared expert (h = fe)
  router : Matrix              -- Wr, d x NE (not read in a dense layer)
  routed : Array GatedWeights  -- the NE routed experts, h = fe (not read in a dense layer)
  deriving Inhabited

/-- All weights. There are no bias vectors and no gain vectors (section 3). -/
structure Weights where
  embedding : Matrix           -- Emb, V x d
  perLayer : Array LayerWeights
  head : Matrix                -- Wh, d x V
  deriving Inhabited

/-! ## 3. The norm (section 5) -/

/-- The values of one norm of one stream row. -/
structure Norm where
  sumSquares : Int  -- Vx
  root : Int        -- sigma
  reciprocal : Int  -- Rc
  quotient : IntegerVector    -- w
  out : IntegerVector         -- nr, the result
  deriving Inhabited

/-- `N(x; M, K, eps)`, which takes the place of the root-mean-square norm, without gain: each entry
times a rounded `2^bits / |x|`, then shifted, then clamped. `|x|` is the root of the sum of squares
plus `eps`. There is no mean: the factor sqrt(d) sits in the scales and the weights. The divisor
`root` is at least 1, because `eps` is (`wellFormed`). Reads: `k` is below the size of `x`. -/
def rmsNorm (bits shift : Nat) (eps : Int) (x : IntegerVector) : Norm :=
  let sumSquares := sumOver x.size fun k => x.entry k * x.entry k
  let root : Int := integerSquareRoot (sumSquares + eps).toNat
  let reciprocal := (2 ^ bits + root / 2) / root
  let quotient := x.map fun xk => roundShift (xk * reciprocal) shift
  let out := quotient.map fun wk => clamp wk activationBound
  { sumSquares, root, reciprocal, quotient, out }

/-! ## 4. Attention (section 6) -/

/-- The rotary step on a vector made of heads of `headDim` entries: in each head, entries `2 i` and
`2 i + 1` are turned by the angle number `i`, whose scaled cosine and sine are entries `i` of
`cosine` and `sine`. `j` is even exactly if it is the first of its pair, because `headDim` is even.
The divisor `headDim` is positive (`wellFormed`). Reads: the two rows have `headDim / 2` entries;
the size of `A` is a multiple of `headDim`, which is even, so `j + 1` is inside for an even `j`, and
an odd `j` is at least 1. -/
def rotate (cosine sine : IntegerVector) (headDim : Nat) (A : IntegerVector) : IntegerVector :=
  tabulate A.size fun j =>
    let i := (j % headDim) / 2
    if j % 2 = 0 then cosine.entry i * A.entry j - sine.entry i * A.entry (j + 1)  -- p0 = C A0 - S A1
    else sine.entry i * A.entry (j - 1) + cosine.entry i * A.entry j               -- p1 = S A0 + C A1

/-- The queries, keys and values of one position, with the values on the way to them. -/
structure Projections where
  queryProducts : IntegerVector  -- A[j] for j < dq; entry h dh + c belongs to entry c of query head h
  keyProducts : IntegerVector    -- A[dq + j] for j < dkv
  rotatedQuery : IntegerVector   -- p0 and p1 of the query heads
  rotatedKey : IntegerVector     -- p0 and p1 of the key heads
  wideQuery : IntegerVector      -- the wide values of the query heads
  wideKey : IntegerVector        -- the wide values of the key heads
  query : IntegerVector          -- q
  key : IntegerVector            -- k
  wideValue : IntegerVector      -- vw
  value : IntegerVector          -- v
  deriving Inhabited

/-- Steps 2 and 3 of section 6 for the normed row `a` at position `t`: queries and keys are
projected, rotated, shifted and clamped; values the same without the rotation. Reads: a prompt has
at most `T` tokens, and the rotary tables have `T` rows. -/
def projections (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) :
    Projections :=
  let cosine :=
    if p.rotary then tables.cosine.entry t else tabulate (s.headDim / 2) fun _ => 2 ^ s.rotaryScale
  let sine := if p.rotary then tables.sine.entry t else tabulate (s.headDim / 2) fun _ => 0
  let queryProducts := product a w.query s.queryWidth
  let keyProducts := product a w.key s.keyValueWidth
  let rotatedQuery := rotate cosine sine s.headDim queryProducts
  let rotatedKey := rotate cosine sine s.headDim keyProducts
  let wideQuery := rotatedQuery.map fun e => roundShift e p.queryShift
  let wideKey := rotatedKey.map fun e => roundShift e p.keyShift
  let query := wideQuery.map fun e => clamp e activationBound
  let key := wideKey.map fun e => clamp e activationBound
  let wideValue := (product a w.value s.keyValueWidth).map fun e => roundShift e p.valueShift
  let value := wideValue.map fun e => clamp e activationBound
  { queryProducts, keyProducts, rotatedQuery, rotatedKey, wideQuery, wideKey,
    query, key, wideValue, value }

/-- The values of step 4 for one query head at one position `i`. The arrays over `j` have the
`i + 1` entries `j ≤ i`. -/
structure Head where
  scores : IntegerVector        -- s_ij
  top : Int           -- m_i
  distances : IntegerVector     -- u_ij
  exponentials : IntegerVector  -- e_ij
  total : Int         -- Z_i
  mix : IntegerVector           -- acc_i[c]
  out : IntegerVector           -- o_i[h][c]
  deriving Inhabited

/-- Step 4: causal attention of query head `h` at position `i` over the positions `j ≤ i`, with a
softmax that reads its exponentials from a table, at the distance to the largest score. The divisors
`n_g` and `n_h / n_g` are positive, because `n_g` is, divides `n_h`, and `n_h` is positive
(`wellFormed`; `heads_per_group_positive` in `IntegerModel/Readable/Reads.lean`). The divisor `2^sh`
is a power of two. The divisor `2 total` is positive: the top score has distance 0, the table's
first entry is positive and no entry is negative (`wellFormed`). Reads: `j ≤ i`, and `i` is a
position; `h dh + c < n_h dh`; `g < n_g`, because `n_g` divides `n_h`, so `g dh + c < n_g dh`; a
distance is not negative, because `top` is the largest score, and the table is read only below its
size. -/
def attendHead (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat) :
    Head :=
  let dh := s.headDim
  let g := h / (s.queryHeads / s.keyValueHeads)  -- the key and value head that query head h reads
  let scores := tabulate (i + 1) fun j =>
    sumOver dh fun c =>
      (projected.entry i).query.entry (h * dh + c) * (projected.entry j).key.entry (g * dh + c)
  let top := maxUpTo (fun j => scores.entry j) i
  let distances := scores.map fun sj => (top - sj) / 2 ^ p.softmaxShift
  let exponentials := distances.map fun (u : Int) =>
    if u < tables.exponential.size then tables.exponential.entry u.toNat else 0
  let total := sumOver (i + 1) fun j => exponentials.entry j
  let mix := tabulate dh fun c =>
    sumOver (i + 1) fun j => exponentials.entry j * (projected.entry j).value.entry (g * dh + c)
  let out := mix.map fun acc => (2 * acc + total) / (2 * total)
  { scores, top, distances, exponentials, total, mix, out }

/-- The values of one layer's attention. The first index of every array is the position. -/
structure Attention where
  norm : Array Norm                -- a, and the values on the way to it
  projected : Array Projections
  heads : Array (Array Head)       -- by position, then by query head
  mixed : Matrix                   -- o: the heads' results side by side
  addition : Matrix                -- ad
  out : Matrix                     -- x', the stream after attention
  deriving Inhabited

/-- Attention (section 6): maps the stream `x` that enters the layer, one row for each position, to
the stream after attention. The divisor `dh` is positive (`wellFormed`). Reads: `t` and `i` are
positions; `j < n_h dh`, so `j / dh < n_h` and `j % dh < dh`. -/
def attention (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights) (x : Matrix) :
    Attention :=
  let norm := x.map fun row => rmsNorm p.attentionBits p.attentionShift p.attentionEps row  -- step 1
  let projected := tabulate x.size fun t => projections s p tables w t (norm.entry t).out  -- steps 2, 3
  let heads := tabulate x.size fun i => tabulate s.queryHeads fun h => attendHead s p tables projected i h  -- step 4
  let mixed := tabulate x.size fun i => tabulate s.queryWidth fun j =>
    ((heads.entry i).entry (j / s.headDim)).out.entry (j % s.headDim)
  let addition := mixed.map fun o => (product o w.output s.width).map fun e => roundShift e p.outputShift  -- step 5
  let out := tabulate x.size fun t => addVectors (x.entry t) (addition.entry t)
  { norm, projected, heads, mixed, addition, out }

/-! ## 5. Feed-forward (section 7), at one position -/

/-- The hidden units of one gated block. Entry `j` of every vector belongs to hidden unit `j` of the
block. -/
structure HiddenUnits where
  wideGate : IntegerVector     -- gw
  lowByte : IntegerVector      -- g0
  highPart : IntegerVector     -- gh
  clampedHigh : IntegerVector  -- gc
  key : IntegerVector          -- 256 gc + g0, the key at which the SiLU table is read
  activation : IntegerVector   -- s
  up : IntegerVector           -- u
  deriving Inhabited

/-- The `hidden` units of one block, which reads the vector `z`: SiLU, from the table, of the gate
projection, and with it the up projection. The gate's clamp cuts the key's part above its low byte
to `-127 .. 127`. That only saturates, if the table is constant beyond (section 7). Reads: all
vectors have `hidden` entries. -/
def hiddenUnits (tables : Tables) (w : GatedWeights) (hidden gateShift upShift : Nat) (z : IntegerVector) :
    HiddenUnits :=
  let wideGate := (product z w.gate hidden).map fun e => roundShift e gateShift
  let lowByte := wideGate.map balancedLowByte
  let highPart := tabulate hidden fun j => (wideGate.entry j - lowByte.entry j) / 256
  let clampedHigh := highPart.map fun gh => clamp gh 127
  let key := tabulate hidden fun j => 256 * clampedHigh.entry j + lowByte.entry j
  let activation := key.map tables.silu.read
  let up := (product z w.up hidden).map fun e => roundShift e upShift
  { wideGate, lowByte, highPart, clampedHigh, key, activation, up }

/-- Entry `k` of a block's down projection, before the shift: the sum over its units `j` of
`s[j] u[j] Wd[j][k]`. Reads: the two vectors have the same size, `down` has that many rows, and `k`
is below its number of columns. -/
def downSum (units : HiddenUnits) (down : Matrix) (k : Nat) : Int :=
  sumOver units.up.size fun j =>
    units.activation.entry j * units.up.entry j * (down.entry j).entry k

/-- The router's values, and the hidden units of the expert that it chose. In a dense layer, which
has no router, the record is `noRoute`. -/
structure Routed where
  wide : IntegerVector           -- lw
  high : IntegerVector           -- ly
  low : IntegerVector            -- l3
  logits : IntegerVector         -- lr
  chosen : Nat         -- e*
  scale : Int          -- sc
  input : IntegerVector          -- xr
  units : HiddenUnits  -- the hidden units fe ≤ j < f of section 7
  deriving Inhabited

/-- The router and the routed expert. The router ranks the experts, chooses the first of the best,
and scales that expert's input, the normed row `m`, by the sigmoid, from the table, of its logit.
The router's clamp cuts a logit's part above its three low bits to `-2047 .. 2047`; it is not
monotone at its two ends (section 7). Reads: the four vectors have `NE` entries; `chosen < NE`
(`chosen_index` in `IntegerModel/Readable/Reads.lean`), because a mixture-of-experts layer has
`NE > 0`, and there are `NE` experts. -/
def routedExpert (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights) (m : IntegerVector) :
    Routed :=
  let wide := (product m w.router s.experts).map fun e => roundShift e p.routerShift
  let high := wide.map fun lw => lw / 8
  let low := wide.map fun lw => lw % 8
  let logits := tabulate s.experts fun e => 8 * clamp (high.entry e) 2047 + low.entry e
  let chosen := firstArgmax (fun e => logits.entry e) s.experts
  let scale := tables.sigmoid.read (logits.entry chosen)
  let input := m.map fun mk => roundShift (scale * mk) 16
  let units := hiddenUnits tables (w.routed.entry chosen)
    s.expertHidden p.routedGateShift p.routedUpShift input
  { wide, high, low, logits, chosen, scale, input, units }

/-- What stands for the router's values in a dense layer: every vector is empty, and the two
numbers are 0 and mean nothing. The range conditions hold of it, because they speak of the entries
of empty vectors. -/
def noRoute : Routed :=
  let noUnits : HiddenUnits :=
    { wideGate := #[], lowByte := #[], highPart := #[], clampedHigh := #[], key := #[],
      activation := #[], up := #[] }
  { wide := #[], high := #[], low := #[], logits := #[], chosen := 0, scale := 0,
    input := #[], units := noUnits }

/-- The values of one layer's feed-forward block at one position. -/
structure FeedForward where
  norm : Norm             -- m, and the values on the way to it
  shared : HiddenUnits    -- the dense block's f units, or the shared expert's fe units (the units j < fe of section 7)
  routed : Routed         -- the router and the routed expert; `noRoute` in a dense layer
  addition : IntegerVector          -- ad
  out : IntegerVector               -- x'', the stream that enters the next layer
  deriving Inhabited

/-- Feed-forward (section 7): maps one row `x` of the stream after attention to the row that enters
the next layer. In a mixture-of-experts layer the two down projections are added before the one
shift. Reads: `chosen < NE`, as above. -/
def feedForward (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : IntegerVector) :
    FeedForward :=
  let norm := rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  let m := norm.out
  if mixture then
    let sharedUnits := hiddenUnits tables w.shared s.expertHidden p.gateShift p.upShift m
    let route := routedExpert s p tables w m
    let addition := tabulate s.width fun k =>
      roundShift (downSum sharedUnits w.shared.down k +
          downSum route.units (w.routed.entry route.chosen).down k) p.downShift
    { norm, shared := sharedUnits, routed := route, addition, out := addVectors x addition }
  else
    let sharedUnits := hiddenUnits tables w.shared s.hidden p.gateShift p.upShift m
    let addition :=
      tabulate s.width fun k => roundShift (downSum sharedUnits w.shared.down k) p.downShift
    { norm, shared := sharedUnits, routed := noRoute, addition, out := addVectors x addition }

/-! ## 6. Layers, embedding and head (sections 6 to 8) -/

/-- The values of one layer at all positions. -/
structure Layer where
  input : Matrix                   -- x, the stream that enters the layer
  attention : Attention
  feedForward : Array FeedForward  -- by position
  out : Matrix                     -- x'', the stream that leaves the layer
  deriving Inhabited

/-- Layer `l`: attention, then feed-forward at each position. Reads: `l < L`. -/
def layer (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (x : Matrix) : Layer :=
  let attended := attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) x
  let fed := attended.out.map fun row =>
    feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l) row
  { input := x, attention := attended, feedForward := fed, out := fed.map fun ff => ff.out }

/-- The stream above the layers `below`: the output of the last of them, or the embedded tokens if
there is none. -/
def streamAbove (embedded : Matrix) (below : Array Layer) : Matrix :=
  match below.back? with
  | some top => top.out
  | none => embedded

/-- The first `n` layers, each fed with the stream above the layers below it. -/
def firstLayers (s : Settings) (tables : Tables) (weights : Weights) (embedded : Matrix) :
    Nat → Array Layer
  | 0 => #[]
  | l + 1 =>
    let below := firstLayers s tables weights embedded l
    below.push (layer s tables weights l (streamAbove embedded below))

/-- Every named value of the model on one prompt. -/
structure Trace where
  embedded : Matrix       -- x^0
  layer : Array Layer
  last : Matrix           -- x^L
  finalNorm : Array Norm  -- aF, by position, and the values on the way to it
  logits : Matrix         -- lam
  choices : Array Nat     -- by position: the first arg-max of lam_t
  deriving Inhabited

/-- Evaluates the model at every position of the prompt (section 8). It tests nothing: see `model`.
Reads: a prompt's tokens are below `V`, and `v < V`. -/
def trace (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat) : Trace :=
  let embedded := prompt.map fun token => weights.embedding.entry token
  let layers := firstLayers s tables weights embedded s.layers
  let last := streamAbove embedded layers
  let finalNorm := last.map fun row => rmsNorm s.finalBits s.finalShift s.finalEps row
  let logits := finalNorm.map fun norm => product norm.out weights.head s.vocabulary
  let choices := logits.map fun lam => firstArgmax (fun v => lam.entry v) s.vocabulary
  { embedded, layer := layers, last, finalNorm, logits, choices }

/-! ## 7. The range conditions (section 9)

The model is partial. At eight kinds of places a value must be in a stated interval, at every
position of the prompt. The numbers are those of the table in section 9, and the intervals are those
of its column "defined". Reads in this part: `t` is a position and `l < L`. -/

/-- Does every entry fit 16 bits? -/
def fits16 (v : IntegerVector) : Bool :=
  v.all fun e => -32768 ≤ e && e ≤ 32767

/-- The conditions at one norm. Condition 8, a stream value `|x_k| < 2^39`, has no separate test: it
follows from condition 1 at the norm that reads the row, because `x_k^2 ≤ Vx`
(`stream_bounded_by_condition_1` in `IntegerModel/Readable/Facts.lean`, a theorem about one norm,
for `eps ≥ 0`). That every stream row is read by a norm whose condition 1 is tested can be seen in
`attention`, `feedForward`, `trace` and `allConditionsHold`; no theorem says it of the whole model.
-/
def normOk (eps : Int) (n : Norm) : Bool :=
  n.sumSquares + eps < 2 ^ 78  -- 1: a norm's sum of squares, Vx + eps (and through it 8)
  && fits16 n.quotient         -- 2: a norm's quotient w

/-- The conditions of a layer's attention at position `t`. -/
def attentionOk (p : LayerSettings) (a : Attention) (t : Nat) : Bool :=
  normOk p.attentionEps (a.norm.entry t)
  && fits16 (a.projected.entry t).wideQuery && fits16 (a.projected.entry t).wideKey  -- 3: a wide query or key entry
  && fits16 (a.projected.entry t).wideValue                                          -- 4: a wide value entry vw

/-- The conditions on the hidden units of one block. -/
def unitsOk (units : HiddenUnits) : Bool :=
  (units.highPart.all fun gh => -16384 ≤ gh && gh ≤ 16383)  -- 6: the high part gh of a wide gate key
  && fits16 units.up                                        -- 7: an up projection u

/-- The conditions of a layer's feed-forward block at one position. In a dense layer those on the
routed part hold of empty vectors (`noRoute`). -/
def feedForwardOk (p : LayerSettings) (ff : FeedForward) : Bool :=
  normOk p.feedForwardEps ff.norm && unitsOk ff.shared
  && fits16 ff.routed.high  -- 5: the high part ly of a wide router logit
  && unitsOk ff.routed.units

/-- Do all range conditions hold, at all positions of the prompt, in all layers and at the final
norm? -/
def allConditionsHold (s : Settings) (values : Trace) : Bool :=
  (List.range values.embedded.size).all fun t =>
    ((List.range s.layers).all fun l =>
      attentionOk (s.perLayer.entry l) (values.layer.entry l).attention t
      && feedForwardOk (s.perLayer.entry l) ((values.layer.entry l).feedForward.entry t))
    && normOk s.finalEps (values.finalNorm.entry t)

/-! ## 8. What the arguments must be like -/

/-- Does `W` have the given numbers of rows and columns? -/
def hasSize (rows columns : Nat) (W : Matrix) : Bool :=
  W.size == rows && W.all fun row => row.size == columns

/-- Do the three matrices of a gated block have the sizes for width `d` and `h` hidden units? -/
def GatedWeights.hasSizes (d h : Nat) (w : GatedWeights) : Bool :=
  hasSize d h w.gate && hasSize d h w.up && hasSize h d w.down

/-- Does the table have all keys `low .. high`? -/
def KeyedTable.covers (table : KeyedTable) (low high : Int) : Bool :=
  table.lowestKey ≤ low && high < table.lowestKey + table.entries.size

/-- Does one layer have the sizes of section 3, and are its two `eps` and every shift that it hands
to `roundShift` at least 1? (`softmaxShift` is not tested.) -/
def layerWellFormed (s : Settings) (p : LayerSettings) (w : LayerWeights) (mixture : Bool) : Bool :=
  hasSize s.width s.queryWidth w.query && hasSize s.width s.keyValueWidth w.key
  && hasSize s.width s.keyValueWidth w.value && hasSize s.queryWidth s.width w.output
  && 1 ≤ p.attentionEps && 1 ≤ p.feedForwardEps
  && 1 ≤ p.attentionShift && 1 ≤ p.queryShift && 1 ≤ p.keyShift &&
    1 ≤ p.valueShift && 1 ≤ p.outputShift
  && 1 ≤ p.feedForwardShift && 1 ≤ p.gateShift && 1 ≤ p.upShift && 1 ≤ p.downShift
  && (if mixture then
      w.shared.hasSizes s.width s.expertHidden && hasSize s.width s.experts w.router
      && w.routed.size == s.experts &&
        (w.routed.all fun expert => expert.hasSizes s.width s.expertHidden)
      && 1 ≤ p.routerShift && 1 ≤ p.routedGateShift && 1 ≤ p.routedUpShift
    else w.shared.hasSizes s.width s.hidden)

/-- Do the arguments fit together? The shape obeys the rules of section 2, the arrays have the sizes
that it states, the tables have the keys that are read, the softmax table starts above 0 and has no
negative entry, every shift that is handed to `roundShift` is at least 1 (`softmaxShift` is not
tested), and so is every `eps`. Reads: the softmax table is tested not to be empty before its first
entry is read, and the two arrays of layers are tested to have `L` entries before entry `l < L` is
read.

It does not ask for the intervals that the verifier accepts for the settings (among them 24 ≤ M ≤
47, M - 14 ≤ K, 17 ≤ K ≤ 32, 4 ≤ sh ≤ 12, eps < 2^48, V ≥ 2, T a power of two; those on the scales
are in the library's `Inst.Model.Lawful`, Inst/Model/Scales.lean). They are no part of "defined".
One effect: for settings with M - 14 ≤ K the lower end of condition 2 never decides
(`quotient_lower_end` in `IntegerModel/Readable/Reads.lean`, for `eps ≥ 1`). For larger M it can
decide, for example at M = 47, K = 32 on the row [-548,662,774,766] with eps = 1; that is not proved
here.

It allows `NE = 0`, a model of dense layers only, as section 2 does. Limit: the theorem that ties
this function to the relation of the soundness proof (`model_eq`, IntegerModel/Readable/Main.lean)
is stated for `0 < NE`. -/
def wellFormed (s : Settings) (tables : Tables) (weights : Weights) : Bool :=
  0 < s.keyValueHeads && 0 < s.queryHeads && s.queryHeads % s.keyValueHeads == 0
  && 0 < s.headDim && s.headDim % 2 == 0 && 0 < s.vocabulary
  && (s.experts == 0 || s.hidden == 2 * s.expertHidden)
  && 1 ≤ s.finalEps && 1 ≤ s.finalShift
  && hasSize s.positions (s.headDim / 2) tables.cosine &&
    hasSize s.positions (s.headDim / 2) tables.sine
  && 0 < tables.exponential.size && 0 < tables.exponential.entry 0 &&
    (tables.exponential.all fun e => 0 ≤ e)
  && tables.silu.covers (-32768) 32767 && tables.sigmoid.covers (-16384) 16383
  && hasSize s.vocabulary s.width weights.embedding && hasSize s.width s.vocabulary weights.head
  && s.perLayer.size == s.layers && weights.perLayer.size == s.layers
  && (List.range s.layers).all fun l =>
    layerWellFormed s (s.perLayer.entry l) (weights.perLayer.entry l) (s.isMixture l)

/-- Are these tokens that the model can run on? At least one and at most `T` tokens, each below `V`.
("Prompt": all the tokens so far.) -/
def isPrompt (s : Settings) (prompt : Array Nat) : Bool :=
  0 < prompt.size && prompt.size ≤ s.positions && prompt.all fun token => token < s.vocabulary

/-! ## 9. The model -/

/-- **The model.** The token that follows the prompt: the first arg-max of the logits at the last
position. It is defined (`some`) exactly if the arguments fit together, the tokens are a prompt, and
range conditions 1 to 8 hold at all positions of the prompt (section 9; condition 8 is tested only
through condition 1: see `normOk`).

Prefix and window (section 8): Model of docs/model.md takes exactly `T` tokens and asks for the
conditions at all `T` positions. This function takes `1 ≤ n ≤ T` tokens and asks for them at these
`n` positions, so it can be defined at a prefix of a window at which Model is not. A theorem about
it must say which of the two it means. At `n = T` the two are the same function (docs/model.md also
has `T = 2^lt`, which is not asked here). Limit: for `n < T` the result is meant to be the first
arg-max of `lam_(n-1)` of every window that begins with these tokens; that is not proved here (for
the library's own program it is: IntegerModel/ReplyOnWindow.lean, part 1). What the library's
soundness theorems need of this function, at the library's sizes, tables and lawful scales, is
stated in `isTrueRequest_iff_model` (IntegerModel/TrueRequest.lean); their proofs use its two
halves, `isTrueRequest_iff_isReply` and `Readable.modelOf_eq`.

Reads: a prompt has a last token, and `choices` has one entry for each token. -/
def model (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat) : Option Nat :=
  if wellFormed s tables weights && isPrompt s prompt then
    let values := trace s tables weights prompt
    if allConditionsHold s values then some (values.choices.entry (prompt.size - 1)) else none
  else none

end IntegerTransformer
