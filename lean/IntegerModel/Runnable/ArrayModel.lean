-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-! # The integer model, as one function on arrays

`Model shape tables settings weights tokens` is the list of the model's first choices, one for each
position of `tokens`, or `none` if a range condition fails. Every step is an exact function on
integers. The architecture is that of a decoder-only transformer of the Llama 4 family: RMS norms,
grouped-query causal attention with rotary position encoding in three of every four layers,
SiLU-gated feed-forward blocks, dense in the even layers; in the odd layers a shared expert and one
routed expert (top 1), whose input is scaled by the sigmoid of its router logit. Some of what
differs from the public model is marked [int] at its step; a fuller list, for a sister function: the
opening comment of IntegerModel/Model.lean. This function is a second, runnable writing of the
library's integer program (Inst/Model/Program.lean); IntegerModel/Runnable/Main.lean compares the
two, `next` (ArrayNext.lean) too; at the model's sizes: IntegerModel/Runnable/AtModelSizes.lean. -/

namespace ArrayProgram

/-! ## 1. Shape, settings, tables, weights -/

structure Shape where
  (T V layers d heads kvHeads headDim ffDense ffExpert experts : Nat)

/-- Llama 4 Maverick, at a window of 1,024 tokens (only `next` reads T: the blocks take the number
of positions from their input) -/
def modelShape : Shape := ⟨1024, 202048, 48, 5120, 40, 8, 128, 16384, 8192, 128⟩

/-- [int] a norm's numbers: the reciprocal's scale 2^M, the right shift K, the regularizer -/
structure Norm where
  (M K : Nat) (eps : Int)

/-- [int] the quantization scales of one layer: ten right shifts, two norms, and the shift sh of the
distance to the top score before the look-up in exp -/
structure LayerScales where
  (kq kk kv ko kg ku kd kr kgR kuR : Nat) (norm1 norm2 : Norm) (sh : Nat)

structure Settings where
  layer : Nat → LayerScales
  final : Norm

/-- [int] five look-up tables in the place of SiLU, the sigmoid, exp, cos and sin -/
structure Tables where
  silu : Int → Int
  sigmoid : Int → Int
  exp : Int → Int
  expRows : Int
  cos : Nat → Nat → Int
  sin : Nat → Nat → Int

abbrev Mat := Nat → Nat → Int        -- input index first

structure LayerWeights where
  (Wq Wk Wv Wo Wgate Wup Wdown Wrouter : Mat) (Egate Eup Edown : Nat → Mat)

structure Weights where
  layer : Nat → LayerWeights
  embedding : Mat
  head : Mat

def hasExperts (L : Nat) : Bool := L % 2 == 1
def hasRotary (L : Nat) : Bool := L % 4 != 3

/-! ## 2. Integer helpers

On Int, "/" and "%" are Lean's: for a positive divisor the floor of the quotient and the remainder
in [0, divisor): -7 / 2 = -4, -7 % 2 = 1 (not C's truncation). x / 0 = 0. On Nat, "-" stops at 0.

A read a[i]! outside an array would give 0 (or the empty row). No theorem states that none occurs;
for an even headDim, kvHeads > 0 dividing heads, experts > 0 and tokens below V the results are
proved equal to the library's formulas, which have no arrays (IntegerModel/Runnable/Main.lean, whose
statements have the further hypotheses).
-/

abbrev Row := Array Int

/-- [int] Division by 2^k, rounded to the nearest integer, halves up; for k ≥ 1. (At k = 0 it gives
a + 1; shifts in settings that pass `lawful`, IntegerModel/Runnable/ArrayNext.lean, are at least 1.)
-/
def shiftRound (a : Int) (k : Nat) : Int := (a + 2 ^ (k - 1)) / 2 ^ k
def clamp (c a : Int) : Int := min (max a (-c)) c
def fits16 (a : Int) : Bool := -2 ^ 15 ≤ a && a < 2 ^ 15
def dot (a : Row) (w : Nat → Int) : Int := (List.range a.size).foldl (fun s j => s + a[j]! * w j) 0
def row (n : Nat) (f : Nat → Int) : Row := (Array.range n).map f
/-- entry c of row i -/
def at2 (a : Array Row) (i c : Nat) : Int := (a[i]!)[c]!
/-- the least index of a greatest entry -/
def argmaxFirst (a : Row) : Nat :=
  (List.range a.size).foldl (fun b j => if a[b]! < a[j]! then j else b) 0
/-- the greatest r with r * r ≤ n, bit by bit from the top -/
def isqrt (n : Nat) : Nat :=
  (List.range (n.log2 / 2 + 1)).reverse.foldl
    (fun r b => if (r + 2 ^ b) * (r + 2 ^ b) ≤ n then r + 2 ^ b else r) 0
/-- a product of a row with a matrix, shifted -/
def project (x : Row) (W : Mat) (n k : Nat) : Row := row n fun c => shiftRound (dot x (W · c)) k

/-! ## 3. The RMS norm

It divides by the root of the sum of squares, not of their mean, and has no gain. (A conversion from
a model's files has to multiply the gains into the matrices that read the norm; `Model` takes any
matrices.) sigma ≥ 1 if eps ≥ 1, as in settings that pass `lawful`.
-/

def rmsNorm (n : Norm) (x : Row) : Option Row :=
  let ss := x.foldl (fun s v => s + v ^ 2) 0
  let sigma : Int := isqrt (ss + n.eps).toNat
  let recip := (2 ^ n.M + sigma / 2) / sigma
  let wide := x.map fun v => shiftRound (v * recip) n.K
  if ss + n.eps < 2 ^ 78 && wide.all fits16 then some (wide.map (clamp 2047)) else none

/-! ## 4. Attention -/

/-- rotary position encoding of one row of heads at position i: neighbouring entries form a pair -/
def rotate (S : Shape) (tb : Tables) (L i : Nat) (A : Row) : Row :=
  row A.size fun c =>
    let n := c % S.headDim
    let C := if hasRotary L then tb.cos i (n / 2) else 2 ^ 12
    let Sn := if hasRotary L then tb.sin i (n / 2) else 0
    if n % 2 == 0 then C * A[c]! - Sn * A[c + 1]! else Sn * A[c - 1]! + C * A[c]!

def checked (wide : Row) : Option Row :=
  if wide.all fits16 then some (wide.map (clamp 2047)) else none

def attention (S : Shape) (tb : Tables) (s : LayerScales) (w : LayerWeights)
    (L : Nat) (x : Array Row) : Option (Array Row) := do
  let dq := S.heads * S.headDim
  let dkv := S.kvHeads * S.headDim
  let a ← x.mapM (rmsNorm s.norm1)
  let q ← (Array.range x.size).mapM fun i =>
    checked ((rotate S tb L i (row dq fun c => dot a[i]! (w.Wq · c))).map (shiftRound · s.kq))
  let k ← (Array.range x.size).mapM fun i =>
    checked ((rotate S tb L i (row dkv fun c => dot a[i]! (w.Wk · c))).map (shiftRound · s.kk))
  let v ← a.mapM fun r => checked (project r w.Wv dkv s.kv)
  return (Array.range x.size).map fun i =>
    let out := (Array.range S.heads).flatMap fun h =>
      let g := h / (S.heads / S.kvHeads)                                   -- grouped queries: head h reads key/value head g
      let score := row (i + 1) fun j => (List.range S.headDim).foldl (fun t n => t + at2 q i (S.headDim * h + n) * at2 k j (S.headDim * g + n)) 0   -- causal: j ≤ i
      let top := score.foldl max score[0]!
      let weight := score.map fun t => let u := (top - t) / 2 ^ s.sh; if u < tb.expRows then tb.exp u else 0            -- [int] softmax by table
      let den := weight.foldl (· + ·) 0                                    -- not 0 if expRows > 0, exp 0 > 0 and no entry of exp is negative: the top score has u = 0
      row S.headDim fun n =>
        (2 * dot weight (fun j => at2 v j (S.headDim * g + n)) + den) / (2 * den)
    row S.d fun c => at2 x i c + shiftRound (dot out (w.Wo · c)) s.ko

/-! ## 5. Feed-forward -/

/-- one hidden unit: SiLU(gate) · up -/
def unit (tb : Tables) (z : Row) (wg wu : Nat → Int) (kg ku : Nat) : Option Int :=
  let gate := shiftRound (dot z wg) kg
  let low := (gate + 128) % 256 - 128
  let high := (gate - low) / 256
  let up := shiftRound (dot z wu) ku
  if -2 ^ 14 ≤ high && high < 2 ^ 14 && fits16 up then
    some (tb.silu (256 * clamp 127 high + low + 2 ^ 15) * up)
  else none

def feedForward (S : Shape) (tb : Tables) (s : LayerScales) (w : LayerWeights)
    (L : Nat) (x : Array Row) : Option (Array Row) :=
  x.mapM fun xi => do
    let m ← rmsNorm s.norm2 xi
    if hasExperts L then
      let wide := project m w.Wrouter S.experts s.kr
      if !(wide.all fun l => fits16 ((l - l % 8) / 8)) then none
      let logit := wide.map fun l => 8 * clamp 2047 ((l - l % 8) / 8) + l % 8
      let e := argmaxFirst logit                                              -- top 1
      let scale := tb.sigmoid (logit[e]! + 2 ^ 15)
      let scaled := m.map fun v => shiftRound (scale * v) 16                   -- the router's scale multiplies the expert's input
      let shared ← (Array.range S.ffExpert).mapM fun j =>
        unit tb m (w.Wgate · j) (w.Wup · j) s.kg s.ku
      let routed ← (Array.range S.ffExpert).mapM fun j =>
        unit tb scaled (w.Egate e · j) (w.Eup e · j) s.kgR s.kuR
      return row S.d fun c =>
        xi[c]! + shiftRound (dot shared (w.Wdown · c) + dot routed (w.Edown e · c)) s.kd
    else
      let hidden ← (Array.range S.ffDense).mapM fun j =>
        unit tb m (w.Wgate · j) (w.Wup · j) s.kg s.ku
      return row S.d fun c => xi[c]! + shiftRound (dot hidden (w.Wdown · c)) s.kd

/-! ## 6. The model -/

/-- the residual stream after all layers -/
def stream (S : Shape) (tb : Tables) (st : Settings) (W : Weights) (tokens : Array Nat) :
    Option (Array Row) :=
  (List.range S.layers).foldlM
    (fun x L =>
      attention S tb (st.layer L) (W.layer L) L x >>= feedForward S tb (st.layer L) (W.layer L) L)
    (tokens.map fun t => row S.d (W.embedding t))

/-- the logits at every position -/
def logits (S : Shape) (tb : Tables) (st : Settings) (W : Weights) (tokens : Array Nat) :
    Option (Array Row) := do
  let n ← (← stream S tb st W tokens).mapM (rmsNorm st.final)
  return n.map fun r => row S.V fun v => dot r (W.head · v)

/-- The model at all positions: after each nonempty prefix of `tokens`, the least token of largest
logit.
(The function "a context in, the next token out" is `next`,
IntegerModel/Runnable/ArrayNext.lean.) -/
def Model (S : Shape) (tb : Tables) (st : Settings) (W : Weights) (tokens : Array Nat) :
    Option (Array Nat) :=
  (logits S tb st W tokens).map (·.map argmaxFirst)

end ArrayProgram
