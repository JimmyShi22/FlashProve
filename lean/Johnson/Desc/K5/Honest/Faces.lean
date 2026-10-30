-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Faces.lean: what the files on the honest prover's side of an attention
segment's own rounds share: the reader of cells, the place's public numbers, the row's shape, and
the challenges by number. Definitions with code; no theorem. Tests:
Johnson/Desc/K5/Honest/FacesToy.lean.

The verifier's side of these rounds is Johnson/Desc/First/Att/K5AttentionKind.lean. Its `script` lists the
stages in order; here the same list is folded into the row's parts.

  `K5In`          the segment's cells, by the library's own names of cells
                  (`Inst.Model.AttSeg.Raw`, Inst/Model/Att/Trace.lean)
  `K5In.c`, `ew`, `mx`, `zd`, `ibit`, `rh`, `rhp`, `q`, `o`, `kx`, `v`
                  the values that the rounds speak of: a value of several cells is the sum of its
                  cells under the powers of 256
  `Pub5`          the place's public numbers: the planner's shape and its numbers of these rounds
  `PartShape`, `shapesOf`, `shapes`, `cut`, `firstOf`, `scalars`
                  the row: a masked sumcheck with the scalars at the head of its first message, or
                  one round by itself; how many rounds each part has; the number of a part's first
                  round; how many scalars it sends
  `iSE` .. `iHB`  the parts' numbers in the row, by name
  `Chal`, `Chal.many`, `Chal.one`, `Chal.r`, `powers`
                  the challenges: each lookup call's key point, and the rounds' own so far

The names of parts, scalars and points are those of docs/format/11-3-attention-segment.md.
Pair number b is the layer b / HA and the query head b % HA among those that share a head g of keys
and values.

Limits. A cell beyond the sizes is whatever the reader yields. A challenge that has not been heard
yet reads as nothing or as 0: the callers ask only for what lies in front of them.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GeoOf
import Johnson.Desc.First.Att.LeftP
import Inst.Model.Att.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open VerifiableInference.Desc.First.Att.P (Geo geoOf ofNat Stage script)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open Inst.Model.AttSeg (Raw)

/-! ## The cells -/

/-- **The segment's cells**, by name. -/
structure K5In where
  cell : Raw → E

/-- The sum of f 0, .., f (n - 1). -/
def sumTo (n : Nat) (f : Nat → E) : E := (List.range n).foldl (fun s i => addE s (f i)) zeroE

/-- The sum of w[i] f i over w's entries. -/
def under (w : Array E) (f : Nat → E) : E := sumTo w.size fun i => mulE (w.getD i zeroE) (f i)

/-- A value of n cells: the sum of 256 ^ l times cell l. -/
def limbs (n : Nat) (f : Nat → E) : E := sumTo n fun l => mulE (ofNat (256 ^ l)) (f l)

namespace K5In
variable (w : K5In)

/-- Cell x, below 5, of the pair of positions with the index n in its region: on the diagonal, or
below it. -/
def c (onDiag : Bool) (x b n : Nat) : E := w.cell (.c (if onDiag then .D else .M) x b n)
/-- The pair's softmax weight: (c3 + 128) + 256 c4. -/
def ew (onDiag : Bool) (b n : Nat) : E :=
  addE (addE (w.c onDiag 3 b n) (ofNat 128)) (mulE (ofNat 256) (w.c onDiag 4 b n))
/-- The row's maximum, at token i. -/
def mx (b g i : Nat) : E := limbs 4 fun l => w.cell (.mx l b g i)
/-- The row's denominator. -/
def zd (b g i : Nat) : E := limbs 4 fun l => w.cell (.den l b g i)
/-- Bit k, the lowest first, of the index at which the maximum is attained. -/
def ibit (k b g i : Nat) : E := w.cell (.ib k b g i)
/-- The two cells of the division's remainders, at token i and channel n: each holds the high part
of a remainder LESS 128. The rounds' scalars are values of these cells as they are. -/
def rh (b g i n : Nat) : E := w.cell (.qh b g i n)
def rhp (b g i n : Nat) : E := w.cell (.qh' b g i n)
/-- Queries and outputs, at token i and channel n. -/
def q (b g i n : Nat) : E := limbs 2 fun l => w.cell (.qry l b g i n)
def o (b g i n : Nat) : E := limbs 2 fun l => w.cell (.out l b g i n)
/-- Keys and values of layer lam, at token j and channel n. -/
def kx (lam g j n : Nat) : E := limbs 2 fun l => w.cell (.key l lam g j n)
def v (lam g j n : Nat) : E := limbs 2 fun l => w.cell (.val l lam g j n)

end K5In

/-! ## The place's public numbers and the row's shape -/

/-- **The place's public numbers.** -/
structure Pub5 where
  /-- the planner's shape of the attention sub-proof -/
  S : OnBytes.Attention.Shape
  /-- the planner's numbers of these rounds -/
  x : OnBytes.Params.AttentionRounds

/-- The numbers as the verifier's claims read them. -/
def Pub5.g (P : Pub5) : Geo := geoOf P.S

/-- A part of the row. -/
inductive PartShape where
  /-- a masked sumcheck, with the scalars that are sent at the head of its first message -/
  | sum (k : Call)
  /-- one round by itself, which sends n scalars -/
  | one (n : Nat)

/-- The stages' parts. lead: the scalars that wait. It walks the list as the verifier's `entriesOf`
does. -/
def shapesOf : Nat → List Stage → List PartShape
  | _, [] => []
  | lead, .scalars n :: l => shapesOf (lead + n) l
  | lead, .sum vs e :: l => .sum ⟨lead, vs, some e⟩ :: shapesOf 0 l
  | lead, .batch _ :: l => .one lead :: shapesOf 0 l
  | lead, .point _ :: l => .one lead :: shapesOf 0 l

/-- **The row's parts**, in order. -/
def shapes (x : OnBytes.Params.AttentionRounds) : List PartShape := shapesOf 0 (script x)

/-- A part's number of rounds. -/
def PartShape.rounds : PartShape → Nat
  | .sum k => k.vs.length + 3
  | .one _ => 1

/-- How many scalars a part sends. -/
def PartShape.scalars : PartShape → Nat
  | .sum k => k.lead + VerifiableInference.Desc.Part.MaskedSum.ownSlots k.all +
      (k.ends.map (·.n)).getD 0
  | .one n => n

/-- The rounds of each part. -/
def cut (x : OnBytes.Params.AttentionRounds) : List Nat := (shapes x).map (·.rounds)

/-- The number, among the place's rounds from 0, of the first round of part p. -/
def firstOf (x : OnBytes.Params.AttentionRounds) (p : Nat) : Nat := ((cut x).take p).foldl (· + ·) 0

/-- The parts' numbers. The softmax-table units' sumchecks are the parts 0, 1, ... -/
def iSE (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length
def iGam (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 1
def iVM (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 2
def iVD (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 3
def iZero (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 4
def iM6 (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 5
def iSF (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 6
def iOm4 (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 7
def iSD (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 8
def iOm5 (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 9
def iHB (x : OnBytes.Params.AttentionRounds) : Nat := x.score.length + 10

/-! ## The challenges -/

/-- **The challenges that a part may read.** -/
structure Chal where
  /-- each lookup call's key point -/
  zk : Array (Array E)
  /-- the challenges of the place's own rounds so far, from its first round on: one entry a round,
  also where nothing is drawn -/
  own : List Fmt.Drawn

/-- All elements drawn in the place's round number i; none if it has not been heard. -/
def Chal.many (c : Chal) (i : Nat) : Array E :=
  (((c.own[i]?).map (·.elems)).getD []).toArray.map E.ofTriple

/-- The first element drawn in that round; 0 if there is none. -/
def Chal.one (c : Chal) (i : Nat) : E := (c.many i).getD 0 zeroE

/-- The challenges of the variables' rounds of the masked sumcheck that is part p, in the order of
the rounds: the first is a point's coordinate 0. -/
def Chal.r (x : OnBytes.Params.AttentionRounds) (c : Chal) (p : Nat) : Array E :=
  (Array.range (((cut x).getD p 3) - 3)).map fun l => c.one (firstOf x p + 1 + l)

/-- 1, y, y ^ 2, ..: n entries. -/
def powers (y : E) (n : Nat) : Array E :=
  (VerifiableInference.Desc.Part.MaskedSum.powersFrom y n oneE).toArray

end H2K5.Honest
