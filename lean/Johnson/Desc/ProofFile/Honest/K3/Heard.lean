-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Heard.lean: the honest side of the kind "lookup" (K3): the points
of a lookup's run, made of the challenges heard, each found by its round's number. Definitions with
code; five small theorems on these definitions.

Terms. Honest/K3/GLOSSARY.md ("points", "key point", "base", "stage"). In this file: "LKP shift",
"LKP", "JOIN", "LINE" and "ZERO" are the plan's names of rounds of a lookup.

Why. The verifier's text (`messagesV`, Johnson/Desc/First/Look/Via/Rounds.lean) makes the points at
which its sumchecks sum as it hears: of the samples of "LKP shift", "LKP", "JOIN", "LINE", "ZERO"
and of the sumchecks' own challenges. A part of the honest side is handed no state of the
verifier's: it is handed the list of all challenges in front of it, one entry for each round of the
chain, also for a round in which nothing is sampled. So the same points are made here a second time,
of that list.

What is defined.
  1 `elemsAt`, `elemAt`, `drawsAt`, `roundAt`, `varChals`: reading the list by number.
  2 `behind`, `ptsOf`: the point behind a level of a product tree; all points of a run.
  3 `varsAt`, `pointsOfVars`, `pointsAt`: a stage's variables at these points: the verifier's own
    calls, by name; their points in the rounds' order, as `SumJob.points` wants them.
  4 `leavesR`, `bitsR`: the two points that the claims on the planes read.
  5 `KeyPts`, `keyPtsOf`, `keyPtsAt`, `KeyPts.cols`: at a proof file's link: the key tree's last
    point, cut as the verifier program's structure has it (zx, zy, and zk for each call).

Which rounds are read. Write "at s" for base + `firstRound f s` (Honest/K3/Stages.lean).
  theta: the one sample of round at shift; 0 where there is no shift.
  alpha: the one sample of round at alpha.
  rhoT: the mu samples of round at join, in reverse.
  keyPt i 0: no coordinate.
  keyPt i (m + 1): the sample of round at (keyLine i m), then `layBack` of the samples of the m
    rounds from at (key i m) + 1 on: a sumcheck's first round samples eps, which is no coordinate.
    It reads the level right in front alone.
  tabPt 0: rhoT.
  tabPt (l + 1): likewise of tabLine l and tab l, with mu + l variables.
  zeroPt: the mu + d samples of round at zero, in reverse.
  heard: the list itself, as it was passed.
A point's coordinates stand the highest bit first.

What is shown. `behind_eq_stepDown`: `behind` is the point of `stepDown`. `keyPtsOf_toHeard`:
`keyPtsOf` has the three fields as `toHeard` (Johnson/Desc/First/Look/K3LookupGeneral.lean) makes them.
`withPoints_blank`, `blank_levelVars`, `withPoints_key`: laying `pointsOfVars` into blanked
variables (`blank`, a definition beside them) gives the variables back. The theorems say only this.

Hypotheses that remain.
  `ho`: (in `blank_levelVars`, `withPoints_key`) the order has as many members as the level has
    variables.
  `hr`: (in `behind_eq_stepDown`) the level's challenges are `layBack` of the list.
  `hk`, `e`: (in `keyPtsOf_toHeard`) what was heard has one key point; `toHeard` returns.

Users. Honest/K3/HeardLaw.lean proves, and Honest/K3/HeardGuards.lean [not in this library]
evaluates, statements on these definitions. Honest/K3/GoodDraws.lean and Honest/K3/HeardWhole.lean
use them, among others.

Limits. A round that is not yet heard, or samples fewer elements than are read, counts as zeros;
more elements than are read are dropped: nothing rejects. At a stage that does not stand in the row
`firstRound` gives the number of all the lookup's rounds, so `keyPt` beyond a part's levels, `tabPt`
beyond d, or a part that is not there, read rounds that are not theirs: no stage of the row asks for
these. That `base` is the number of the chain's rounds in front of the place is the caller's to
show.
That these points are those of the verifier's hearing on the same rounds is shown by no theorem of
this file. At a lookup with one part of keys it is `pointsAgree_of_hearV` (Honest/K3/HeardLaw.lean):
where the hearing returns: six equations on the fields that it hands back; of the points between the
levels nothing. Honest/K3/HeardGuards.lean [not in this library] tests it by evaluation at three
synthetic faces: at a small one against `hearV` and, level by level, `First.ProdV.run`; at one of
the real form; at one whose table has one row.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.Part.MaskedSum (Var)
open VerifiableInference.Desc.First.ProdV (layBack levelVars stepDown LevelOut)

/-! ## 1 Reading the challenges by number -/

/-- The elements that round number i sampled; none where the list is shorter. -/
def elemsAt (heard : List Fmt.Drawn) (i : Nat) : List E :=
  ((heard[i]?).map fun d => d.elems.map E.ofTriple).getD []

/-- The first element that round number i sampled; 0 where there is none. -/
def elemAt (heard : List Fmt.Drawn) (i : Nat) : E := (elemsAt heard i).headD zeroE

/-- Just n elements of round number i, in the order of sampling; zeros where they lack. -/
def drawsAt (heard : List Fmt.Drawn) (i n : Nat) : List E :=
  (List.range n).map fun j => (elemsAt heard i).getD j zeroE

/-- The number, in the chain, of a stage's first round. -/
def roundAt (f : LFace) (base : Nat) (s : Stage) : Nat := base + firstRound f s

/-- The challenges of the first n variables of the sumcheck at stage s, in the rounds' order. The
sumcheck's first round samples eps: the variables' rounds come behind it. -/
def varChals (f : LFace) (base : Nat) (heard : List Fmt.Drawn) (s : Stage) (n : Nat) : List E :=
  (List.range n).map fun l => elemAt heard (roundAt f base s + 1 + l)

/-! ## 2 The points -/

/-- **The point behind a level with m variables**: the sample of "LINE", the coordinate of the new
highest bit; then the level's challenges, each laid at the bit that its round fixes. -/
def behind (m : Nat) (order : List Nat) (cs : List E) (xi : E) : Array E :=
  #[xi] ++ layBack m order cs

/-- **All points of a lookup's run**, made of the challenges heard. Here base says how many rounds
of the chain stand in front of the lookup, and heard are the chain's challenges from its first round
on, as far as they are sampled. -/
def ptsOf (f : LFace) (base : Nat) (heard : List Fmt.Drawn) : Pts :=
  let rhoT := (drawsAt heard (roundAt f base .join) f.mu).toArray.reverse
  { theta := if f.shifted then elemAt heard (roundAt f base .shift) else zeroE
    alpha := elemAt heard (roundAt f base .alpha)
    rhoT := rhoT
    keyPt := fun i n =>
      match n with
      | 0 => #[]
      | m + 1 =>
        behind m (f.orders i m) (varChals f base heard (.key i m) m)
          (elemAt heard (roundAt f base (.keyLine i m)))
    tabPt := fun n =>
      match n with
      | 0 => rhoT
      | l + 1 =>
        behind (f.mu + l) (orderDefault (f.mu + l)) (varChals f base heard (.tab l) (f.mu + l))
          (elemAt heard (roundAt f base (.tabLine l)))
    zeroPt := (drawsAt heard (roundAt f base .zero) (f.mu + f.d)).toArray.reverse
    heard := heard }

/-! ## 3 A stage's variables at the points -/

/-- **The variables of a stage's sumcheck as the verifier's text makes them**, at the run's points:
`levelVars` at the point in front of the level and the level's order (`First.ProdV.level`);
`leafVars` at the table side's last point; `bitsCall` at the bits' point. None at the tie, at the
parts' step and at a stage that sends nothing. -/
def varsAt (f : LFace) (s : Stage) (p : Pts) : List Var :=
  match s with
  | .key i m => levelVars m (p.keyPt i m) (f.orders i m)
  | .tab l => levelVars (f.mu + l) (p.tabPt l) (orderDefault (f.mu + l))
  | .leaves => VerifiableInference.Desc.K3.leafVars f (p.tabPt f.d)
  | .bits => (VerifiableInference.Desc.K3.bitsCall p.zeroPt.toList).vs
  | _ => []

/-- The points of the variables that are summed at a point, in order. -/
def pointsOfVars : List Var → List E
  | [] => []
  | .plain _ :: vs => pointsOfVars vs
  | .point z _ :: vs => z :: pointsOfVars vs

/-- **The points of a stage's variables, in the rounds' order**: what `SumJob.points` yields. -/
def pointsAt (f : LFace) (s : Stage) (p : Pts) : List E := pointsOfVars (varsAt f s p)

/-! ## 4 The two points that the claims on the planes read -/

/-- The challenges of the leaves' sumcheck, in the rounds' order (`HeardV.zb0`). -/
def leavesR (f : LFace) (base : Nat) (heard : List Fmt.Drawn) : Array E :=
  (varChals f base heard .leaves (f.mu + f.d)).toArray

/-- The challenges of the bits' sumcheck's variables, in the rounds' order (`HeardV.zb1`). -/
def bitsR (f : LFace) (base : Nat) (heard : List Fmt.Drawn) : Array E :=
  (varChals f base heard .bits (f.mu + f.d)).toArray

/-! ## 5 At a proof file's link: the calls' key points -/

/-- The key tree's last point, cut as the verifier program's structure of a lookup has it
(`Model.Forest.Heard`: zx, zy, zk). -/
structure KeyPts where
  /-- the first dT coordinates: a key's place inside its tree -/
  zx : Array E
  /-- the other rK coordinates: the tree's number -/
  zy : Array E
  /-- for each call: the last iota[c] coordinates of zy, then zx -/
  zk : Array (Array E)

/-- **The cut**, to the letter of `toHeard` (Johnson/Desc/First/Look/K3LookupGeneral.lean). Here point is
the key tree's last point, the highest variable first. -/
def keyPtsOf (h : OnBytes.Model.Forest.Shape) (point : Array E) : KeyPts :=
  let zx := point.extract 0 h.dT
  let zy := point.extract h.dT point.size
  { zx := zx, zy := zy
    zk := (Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx }

/-- **The calls' key points of the lookup of shape h, made of the challenges heard.** Here base says
how many rounds of the chain stand in front of that lookup. It reads the rounds of the last key
level and the "LINE" behind it, and no other. -/
def keyPtsAt (h : OnBytes.Model.Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) : KeyPts :=
  keyPtsOf h ((ptsOf (VerifiableInference.Desc.K3.faceOf h) base heard).keyPt 0 h.v)

/-- The first lJ coordinates of call q's key point: those that belong to its columns
(`Model.Head.zjOf`, OnBytes/Model/HeadHeard.lean, at lJ := the call's own and a structure whose zk
is the heard one's: `cols_eq_zjOf`, Honest/K3/Law/TiesSealedLot.lean [not in this library]). -/
def KeyPts.cols (k : KeyPts) (q lJ : Nat) : Array E := (k.zk.getD q #[]).extract 0 lJ

/-! ## Small theorems on these definitions -/

/-- `behind` is the point of the verifier's own step down. -/
theorem behind_eq_stepDown (m : Nat) (order : List Nat) (cs : List E) (o : LevelOut)
    (hr : o.r = layBack m order cs) : behind m order cs o.xi = (stepDown o).1 := by
  simp [behind, stepDown, hr]

/-- `keyPtsOf` has the three fields as `toHeard` makes them. -/
theorem keyPtsOf_toHeard (h : OnBytes.Model.Forest.Shape) (g : VerifiableInference.Desc.K3.HeardG)
    (H : OnBytes.Model.Forest.Heard) (point : Array E) (form : OnBytes.Model.Aff)
    (hk : g.keys = [(point, form)]) (e : VerifiableInference.Desc.K3.toHeard h g = some H) :
    H.zx = (keyPtsOf h point).zx ∧ H.zy = (keyPtsOf h point).zy ∧
      H.zk = (keyPtsOf h point).zk := by
  unfold VerifiableInference.Desc.K3.toHeard at e
  rw [hk] at e
  simp only at e
  split at e
  · cases e
    exact ⟨rfl, rfl, rfl⟩
  · cases e

/-- A variable with its point made the stand-in 0. -/
def blank : Var → Var
  | .plain d => .plain d
  | .point _ d => .point zeroE d

/-- Laying the variables' own points into the blanked variables gives the variables back. -/
theorem withPoints_blank (vs : List Var) :
    withPoints (vs.map blank) (pointsOfVars vs) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases v with
    | plain d => simp [blank, pointsOfVars, withPoints, ih]
    | point z d => simp [blank, pointsOfVars, withPoints, ih]

/-- A level's variables, blanked, are the shape's, where the order has as many members as the level
has variables. -/
theorem blank_levelVars (m : Nat) (z : Array E) (order : List Nat) (ho : order.length = m) :
    (levelVars m z order).map blank = (levelCall m).vs := by
  subst ho
  simp only [levelVars, levelCall, List.map_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [blank]

/-- **At a key level the shape with `pointsAt` laid in is the verifier's own list of variables.**
Conditional on an order with as many members as the level has variables. -/
theorem withPoints_key (f : LFace) (i m : Nat) (p : Pts) (ho : (f.orders i m).length = m) :
    withPoints (levelCall m).vs (pointsAt f (.key i m) p) =
      levelVars m (p.keyPt i m) (f.orders i m) := by
  rw [← blank_levelVars m (p.keyPt i m) (f.orders i m) ho]
  exact withPoints_blank _

#print axioms ProofFile.Honest.K3.behind_eq_stepDown
#print axioms ProofFile.Honest.K3.keyPtsOf_toHeard
#print axioms ProofFile.Honest.K3.withPoints_blank
#print axioms ProofFile.Honest.K3.blank_levelVars
#print axioms ProofFile.Honest.K3.withPoints_key

end ProofFile.Honest.K3
