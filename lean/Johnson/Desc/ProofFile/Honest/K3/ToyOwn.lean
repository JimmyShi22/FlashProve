-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/ToyOwn.lean: a second writing of the lookup's honest side, for the
test alone: the run's points out of the challenges heard, the row of parts, and the summands of all
stages, each written once more, as plainly as can be. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md.

Why. Honest/K3/Toy.lean plays a lookup's row against the verifier's hearing. It can take any row and
any filling of `LookJobs`. This file gives it one of each that imports, of the honest side,
Honest/K3/Stages.lean and Honest/SumToy.lean alone, so that the test can run by itself, and so that
the kind's own files can be compared with a second text: the sent scalars are to be equal.

What is defined.
  1 `elemsAt`, `oneAt`, `ownPts`, `ownPointsAt`: the points, by the challenges' numbers.
  2 `quiet`, `ownJob`, `ownRow`: the row: `sumPart` (Honest/Sum.lean) at a stage with a call; else a
    round that sends nothing.
  3 `ext`, `sumRound`, `ptOf`, `layer`: a table's extension, a round's polynomial and a product
    tree's levels, each by a sum or a product over all points.
  4 `ownJobs`: the summands of all stages but the parts' step, at one part of keys.
  5 `noJobs`: the filling that says nothing: every list is empty.

Imported. Files directly under Honest/.

Users. Honest/K3/Toy.lean imports this file.

Limits. It is slow by design: a round costs about 4 ^ m steps at m variables. What is not written a
second time: of Stages.lean it takes code, not types alone (`stages`, a stage's call, `firstRound`),
and of the frame `sumPart`, the names of the stretches and the arithmetic on lists (of the library
`layBack` and `orderDefault`): a slip in the stages' order, in a stage's call or in the count of
rounds in front is shared by both writings, and the comparison of the two cannot see it. (The play
of Honest/K3/Toy.lean has the verifier's hearing on its other side, which is the library's text and
reads none of these.) One part of keys alone: the parts' step (several parts of keys) has no summand
here: its lists are empty; and the tie's first step takes part 0's root for the product of all
parts' roots. The table's rows are passed as a function beside the face; nothing here compares it
with the face's `leaf`. Evaluated in part: the test `Fast.rowsFit` (Honest/K3/JobsFast.lean)
compares a table's rows with the face's `leaf`, at one shift and one alpha; Honest/K3/ToyFast.lean,
Honest/K3/ToySecond.lean [not in this library] and Honest/K3/ToyThird.lean [not in this library]
evaluate it at the examples' tables. Nothing here is compared with the verifier's text:
Honest/K3/Toy.lean does that. `inY` of `levelJob` and of `ownJobs` does not reject: a mask entry
beyond the list's end counts as 0. No law on that is shown of these summands: `no_pad_at_part` and
`no_pad_at_job` (Honest/K3/MasksAtPart.lean [not in this library]) speak of `fastJobs` alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages
import Johnson.Desc.ProofFile.Honest.SumToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Toy
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.Part.MaskedSum (Var Call)
open VerifiableInference.Desc.First.ProdV (layBack)
open ProofFile.Honest.SumToy (mulL lin)

/-! ## 1 The points -/

/-- The elements that the challenge number i sampled; none where there is no such challenge. -/
def elemsAt (heard : List Fmt.Drawn) (i : Nat) : List E :=
  ((heard[i]?).map fun d => d.elems.map E.ofTriple).getD []

/-- The first of them; 0 where there is none. -/
def oneAt (heard : List Fmt.Drawn) (i : Nat) : E := (elemsAt heard i).headD zeroE

/-- **The run's points**, by the challenges' numbers. Here base says how many challenges stand in
front of the lookup's first round. The point behind a level is made of that level's own challenges
(its first round samples eps; the next m sample the variables') and of the sample of the round
"LINE" behind it. -/
def ownPts (f : LFace) (base : Nat) (heard : List Fmt.Drawn) : Pts :=
  let no (s : Stage) (k : Nat) : Nat := base + firstRound f s + k
  let behind (s line : Stage) (m : Nat) (o : List Nat) : Array E :=
    #[oneAt heard (no line 0)] ++ layBack m o ((List.range m).map fun l =>
      oneAt heard (no s (1 + l)))
  let rhoT : Array E := (elemsAt heard (no .join 0)).toArray.reverse
  { theta := if f.shifted then oneAt heard (no .shift 0) else zeroE
    alpha := oneAt heard (no .alpha 0)
    rhoT := rhoT
    keyPt := fun i m =>
      match m with
      | 0 => #[]
      | k + 1 => behind (.key i k) (.keyLine i k) k (f.orders i k)
    tabPt := fun l =>
      match l with
      | 0 => rhoT
      | k + 1 => behind (.tab k) (.tabLine k) (f.mu + k) (orderDefault (f.mu + k))
    zeroPt := (elemsAt heard (no .zero 0)).toArray.reverse
    heard := heard }

/-- The coordinate of bit b in a point of m coordinates, the highest bit first. -/
def coord (m : Nat) (z : Array E) (b : Nat) : E := z.getD (m - 1 - b) zeroE

/-- **The points at which a stage's variables are summed**, in the order of the rounds. -/
def ownPointsAt (f : LFace) (s : Stage) (p : Pts) : List E :=
  match s with
  | .key i m => (f.orders i m).map (coord m (p.keyPt i m))
  | .tab l => (orderDefault (f.mu + l)).map (coord (f.mu + l) (p.tabPt l))
  | .leaves => (List.range (f.mu + f.d)).map fun j => (p.tabPt f.d).getD j zeroE
  | .bits => (List.range (f.mu + f.d)).map fun j => p.zeroPt.getD j zeroE
  | _ => []

/-! ## 2 The row -/

variable {V W : Type}

/-- A round that sends nothing, as a part. -/
def quiet : Part V W Unit :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => t.own⟩] }

/-- A stage's job for the masked sumcheck's part. Here pts says how the points are made of the
challenges in front of the part: it is a letter, so that the test can alter it. -/
def ownJob (a : At) (pts : LFace → Nat → List Fmt.Drawn → Pts) (J : LookJobs W) (s : Stage)
    (k : Call) : SumJob W Unit :=
  { shape := k
    points := fun _ fr => ownPointsAt a.face s (pts a.face a.base fr.heard)
    lead := fun _ _ => []
    round := fun w fr rs => (J.job s).round w (pts a.face a.base fr.heard) rs
    inY := fun w fr rs m => (J.job s).inY w (pts a.face a.base fr.heard) rs m
    ends := fun w fr rs => (J.job s).ends w (pts a.face a.base fr.heard) rs }

/-- **The row.** -/
def ownRow (a : At) (pts : LFace → Nat → List Fmt.Drawn → Pts) (J : LookJobs W) :
    List (Part V W Unit) :=
  (stages a.face).zipIdx.map fun x =>
    match x.1.call a.face with
    | some k =>
      sumPart (runName maskRowRun ⟨a.place, x.2⟩ "sum") (runName maskRowRun ⟨a.place, x.2⟩ "ends")
        (ownJob a pts J x.1 k)
    | none => quiet

/-! ## 3 Sums over all points -/

/-- The equality weight of one coordinate: z at the bit 1, 1 - z at the bit 0. -/
def wt (z : E) (bit : Bool) : E := if bit then z else subE oneE z

/-- **A table's extension**: T has 2 ^ m entries; pt: the point, bit by bit. -/
def ext (m : Nat) (T : Nat → E) (pt : Nat → E) : E :=
  (List.range (2 ^ m)).foldl (fun s X =>
    addE s (mulE (T X) ((List.range m).foldl (fun w b => mulE w (wt (pt b) (X.testBit b))) oneE)))
    zeroE

/-- The point behind all rounds: round l fixes the bit o[l]. -/
def ptOf (o : List Nat) (rs : List E) (b : Nat) : E := ((o.zip rs).lookup b).getD zeroE

/-- **A round's polynomial** of the summand kap + A B, A and B tables on m bits: the bits of the
rounds in front stand at their challenges rs; the round's own bit is the variable; each later bit is
summed over 0 and 1 with the equality weight of its coordinate of z. No weight of the round's own
bit or of an earlier one is in it. o: round l fixes the bit o[l]. z: the point, bit by bit. -/
def sumRound (m : Nat) (kap : E) (A B : Nat → E) (o : List Nat) (z : Nat → E) (rs : List E) :
    List E :=
  let cur := o.getD rs.length 0
  let free := o.drop (rs.length + 1)
  (List.range (2 ^ free.length)).foldl (fun acc y =>
    let here : List (Nat × E) :=
      (o.zip rs) ++ free.zipIdx.map fun x => (x.1, if y.testBit x.2 then oneE else zeroE)
    let w := free.zipIdx.foldl (fun w x => mulE w (wt (z x.1) (y.testBit x.2))) oneE
    let pt (t : E) (b : Nat) : E := if b == cur then t else (here.lookup b).getD zeroE
    addL acc (scaleL w (addL [kap]
      (mulL (lin (ext m A (pt zeroE)) (ext m A (pt oneE)))
        (lin (ext m B (pt zeroE)) (ext m B (pt oneE))))))) []

/-- **A product tree's level** with m bits, over leaves on top bits: the entry x is the product of
all leaves whose lowest m bits are x. -/
def layer (top : Nat) (leaf : Nat → E) (m x : Nat) : E :=
  (List.range (2 ^ (top - m))).foldl (fun p y => mulE p (leaf (x + y * 2 ^ m))) oneE

/-- a - b on lists of coefficients. -/
def subL (a b : List E) : List E := addL a (scaleL (subE zeroE oneE) b)

/-! ## 4 The summands -/

/-- A leaf of the key side: alpha - key. -/
def keyLeaf (w : Hidden) (p : Pts) (i x : Nat) : E := subE p.alpha (w.key p.theta i x)

/-- The bits as one table on mu + d bits: the entry u 2 ^ mu + j is plane j's bit of row u's count;
0 at a plane that is not real. -/
def bitTab (f : LFace) (w : Hidden) (x : Nat) : E :=
  if x % 2 ^ f.mu < f.planes then w.bit (x / 2 ^ f.mu) (x % 2 ^ f.mu) else zeroE

/-- alpha - 1 - row, on the same numbers. row: the table's row, of the shift. -/
def gapTab (f : LFace) (row : E → Nat → E) (p : Pts) (x : Nat) : E :=
  subE (subE p.alpha oneE) (row p.theta (x / 2 ^ f.mu))

/-- A leaf of the table side: 1 + bit (alpha - 1 - row). -/
def tabLeaf (f : LFace) (row : E → Nat → E) (w : Hidden) (p : Pts) (x : Nat) : E :=
  addE oneE (mulE (bitTab f w x) (gapTab f row p x))

/-- The root of plane j's tree. -/
def rootG (f : LFace) (row : E → Nat → E) (w : Hidden) (p : Pts) (j : Nat) : E :=
  layer (f.mu + f.d) (tabLeaf f row w p) f.mu j

/-- G_s G_(s+1)^2 G_(s+2)^4 .. up to the last real plane. n: how many planes are still to come. -/
def chain (G : Nat → E) : Nat → Nat → E
  | 0, _ => oneE
  | n + 1, s => mulE (G s) (mulE (chain G n (s + 1)) (chain G n (s + 1)))

/-- A level's job: the level below has the halves A (new bit 0) and B (new bit 1). -/
def levelJob (m : Nat) (below : Hidden → Pts → Nat → E) (o : List Nat)
    (z : Pts → Array E) : StageJob Hidden :=
  let A (w : Hidden) (p : Pts) (x : Nat) : E := below w p x
  let B (w : Hidden) (p : Pts) (x : Nat) : E := below w p (x + 2 ^ m)
  { round := fun w p rs => sumRound m zeroE (A w p) (B w p) o (coord m (z p)) rs
    inY := fun w p rs mk =>
      mulL [ext m (A w p) (ptOf o rs), mk.getD 0 zeroE] [ext m (B w p) (ptOf o rs), mk.getD 1 zeroE]
    ends := fun w p rs => [ext m (A w p) (ptOf o rs), ext m (B w p) (ptOf o rs)] }

/-- The filling that says nothing. -/
def noJob : StageJob Hidden := ⟨fun _ _ _ => [], fun _ _ _ _ => [], fun _ _ _ => []⟩
def noJobs : LookJobs Hidden := ⟨fun _ => noJob⟩

/-- **The summands of all stages**, by sums over all points. row: the table's row, of the shift. -/
def ownJobs (f : LFace) (row : E → Nat → E) : LookJobs Hidden :=
  let n := f.mu + f.d
  let G (w : Hidden) (p : Pts) : Nat → E := rootG f row w p
  let X (w : Hidden) (p : Pts) (s : Nat) : E := chain (G w p) (f.planes - s) s
  let Z (w : Hidden) (p : Pts) : E := layer (f.parts.headD 0) (keyLeaf w p 0) 0 0
  ⟨fun s =>
    match s with
    | .tie 0 =>
      { round := fun _ _ _ => []
        inY := fun w p _ mk =>
          let x := [X w p 1, mk.getD 1 zeroE]
          subL [Z w p, mk.getD 0 zeroE]
            (scaleL (f.factor p.theta p.alpha) (mulL (mulL x x) [G w p 0, mk.getD 2 zeroE]))
        ends := fun w p _ => [Z w p, X w p 1, G w p 0] }
    | .tie (t + 1) =>
      { round := fun _ _ _ => []
        inY := fun w p _ mk =>
          let x := [X w p (t + 2), mk.getD 0 zeroE]
          mulL (mulL x x) [G w p (t + 1), mk.getD 1 zeroE]
        ends := fun w p _ => [X w p (t + 2), G w p (t + 1)] }
    | .key i m =>
      levelJob m (fun w p => layer (f.parts.getD i 0) (keyLeaf w p i) (m + 1)) (f.orders i m)
        fun p => p.keyPt i m
    | .tab l =>
      levelJob (f.mu + l) (fun w p => layer n (tabLeaf f row w p) (f.mu + l + 1))
        (orderDefault (f.mu + l)) fun p => p.tabPt l
    | .leaves =>
      { round := fun w p rs =>
          sumRound n oneE (bitTab f w) (gapTab f row p) (orderDefault n) (coord n (p.tabPt f.d)) rs
        inY := fun _ _ _ _ => []
        ends := fun _ _ _ => [] }
    | .bits =>
      { round := fun w p rs =>
          sumRound n zeroE (bitTab f w) (fun x => subE (bitTab f w x) oneE) (orderDefault n)
            (coord n p.zeroPt) rs
        inY := fun w _ rs mk =>
          let v := [ext n (bitTab f w) (ptOf (orderDefault n) rs), mk.getD 0 zeroE]
          subL (mulL v v) v
        ends := fun w _ rs => [ext n (bitTab f w) (ptOf (orderDefault n) rs)] }
    | _ => noJob⟩

end ProofFile.Honest.K3.Toy
