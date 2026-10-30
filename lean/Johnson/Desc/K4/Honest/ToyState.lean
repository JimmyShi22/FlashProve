-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/ToyState.lean: tools for a trial of the honest prover of the layers' own
rounds (K4) against K4's own verifier text, at a whole plan. Definitions with code, and six tests of
small helpers. No theorem.

WHAT IT DOES NOT SHOW. Nothing here is a property of the protocol. The tools value the verifier's
claims at fixed data; what they yield is an evaluation. THE STATE IN FRONT OF K4 IS LAID BY HAND: no
lookup is run. Of what a lookup leaves, the sampled values are synthetic challenges; its sumcheck
over the leaves is a stand-in with one variable; of its values that K4's claims name the caller lays
three: two hidden values (the end of its key side; the planes' value at the second point) and the
stand-in sumcheck's running claim, which stands under no slot.

WHAT IT DEFINES.
  1  `toyFrontSizes`, `toyLook`, `toyFo`, `toyLedger`, `toyPar`, `toyPart`   what stands in front
     of K4: six synthetic challenges; what the lookup has sampled, of these; what the verifier holds
     of the lookup; the sub-proof's ledger; the place's parameters; K4's part of the carried state
  2  `ToyHeard`, `toyHear`   K4's OWN SUB-PROTOCOL (the structure `Block` that
     Johnson/Desc/First/K4/Block.lean makes) at its own part of the carried state: its step on
     rounds, then its two runs of claims
  3  `toyGroups`, `cutBy`   the claims under the numbers of the format's groups
  4  `toyReads`, `toyHidden`, `toyValues`, `toyBad`   the honest reads, those on the lookup's planes
     by a rule for a matrix with few cells other than 0; a slot's hidden value; each claim's value;
     the claims that are not 0
  5  `toySolve`   the hidden value of one slot at which one claim is 0
  6  `toyNeighbours`, `toyAdded`, `toyFree`   the stand-in form; the state behind the adding; the
     test behind the batching, there
  7  `toyPending`   the row on the committed weights that the merge hands on
  8  `toyTurn`, `toyScalars`   a sent scalar raised by one; where scalars are sent

Slots laid by hand, all in the lookup's range of the mask row: 0 the end of the key side; 1 the
planes' value at the second point; 2, 3, 4 the stand-in sumcheck's hiding coefficients.

WHAT THE SIX TESTS TRY, AND WHAT THEY DO NOT. They are evaluations by Lean's evaluator at the build,
at small made-up lists and numbers, each against a written answer: no proof. They try five helpers
that read no plan: `cutBy` (twice: a list that fits its groups; one that is too long), `toyBad`,
`toyNeighbours`, `toyScalars`, `toyTurn`. NO TEST OF THIS FILE TRIES A TOOL THAT READS A PLAN, A
STATE OR THE VERIFIER's TEXT: `toyFrontSizes`, `toyLook`, `toyFo`, `toyLedger`, `toyPar`, `toyPart`,
`toyHear`, `toyGroups`, `toyReads`, `toyHidden`, `toyValues`, `toySolve`, `toyAdded`, `toyFree` and
`toyPending` are tried, if at all, elsewhere.

Limits. The reads' entries are made by the rule that Johnson/Desc/K4/Honest/Cells.lean types;
nothing here holds that rule against the smallness test, which is what binds the reads to the cells.
The test behind the batching asks every slot of the sub-proof; the slots of the lookup and of the
smallness test get their coefficient from ONE STAND-IN FORM that is added beside K4's claims.
The sub-protocol is the innermost one: the proof file's description lifts it to the whole carried
state, types its claims anew and gives it another name and a list of messages that must stand before
(Johnson/Desc/First/K4/AtS.lean, AtC.lean; Johnson/Desc/ProofFile/Lot/K4.lean); none of that is run.
ONE FUNCTION, `toyLook`, FEEDS BOTH SIDES with what the lookup has sampled: the verifier's state
here and, in a trial, the prover's parts. Which of the lookup's rounds hold these values is seen by
nothing. That the lookup's scalars take the segment's slots from 0 on, so that K4's first slot is
their number, is taken from the format's page. `toyPending` IS TYPED ANEW after the verifier's
`wsPending` (OnBytes/Model/Pending.lean): the equation is that text's; its tests on sizes are not
asked.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Desc.First.K4.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (Aff Fork Psc Forest.Heard WsForkOut wsGammaAdd eqTab ledNO ledNS ledLines)
open OnBytes.Model.Layer (Pub HPlan2 Own Env matIx nEndT)
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S LayOwn)

/-! ## 1 What stands in front -/

/-- How many sampled elements each of the six synthetic challenges in front of K4 holds: the
lookup's shift; its point alpha; the place in a tree; the tree's number; the two points on the
planes. -/
def toyFrontSizes (P : Pub) : List Nat :=
  let h := P.y.fo
  [1, 1, h.dT, h.rK, 5 + h.d, 5 + h.d]

/-- **What the lookup has sampled**, of the six challenges. The calls' weights and points are made
as the lookup's own text makes them (`Forest.pad`, OnBytes/Model/Look.lean). Not laid, since K4
reads neither: the public factor of the two products (`a`); the calls' tables at the leaves' point
(`tT`). -/
def toyLook (P : Pub) (front : List Fmt.Drawn) : Forest.Heard :=
  let h := P.y.fo
  let el (i : Nat) : Array E := ((front[i]?).map elemsOf).getD #[]
  let zx := el 2
  let zy := el 3
  { shape := h, theta := (el 0).getD 0 zeroE, alpha := (el 1).getD 0 zeroE, leaves := {}
    zx := zx, zy := zy, e := (Array.range h.NC).map (Model.Forest.callWeight h zy)
    zb0 := el 4, zb1 := el 5
    zk := (Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx }

/-- **What the verifier holds of the lookup**: what was sampled; and, by hand: the end of the key
side as the hidden value under slot 0; the planes' value under slot 1; a begun sumcheck in one plain
variable whose hiding coefficients take the slots 2 to 4; the three owed claims' numbers. x: any
element, for the stand-in's own numbers. claim: the stand-in sumcheck's running claim. -/
def toyFo (P : Pub) (front : List Fmt.Drawn) (x claim : E) : Forest.Heard :=
  { toyLook P front with
    leaves := { started := true, first := 2, vars := #[OnBytes.Psc.Weight.plain 3], r := #[x],
                eps := x, claim := claim }
    leavesA := x, sBit := 1, cEnd := Aff.slot 0
    owedObjects := 0, owedPlanes := 1, owedJoin := 2 }

/-- **The sub-proof's ledger in front of K4**: the plan's arrays with room for weights; the plan's
slots; the next slot is the first behind the lookup's; three claims are owed; under the slots 0 and
1 the two values as shown, each with the factor 1. -/
def toyLedger (Q : K4Pub) (shown0 shown1 : E) : Option Fork :=
  let F := Q.hp.Fp.fillL.slots Q.hp.ns
  let G : Fork :=
    { F with next := Model.Forest.elems Q.P.y.fo
             owed := #[{ what := "look-up-mask-claims" }, { what := "look-up-plane-claims" },
                       { what := "look-up-join" }] }
  (G.hide 0 shown0 oneE).bind (·.hide 1 shown1 oneE)

/-- The place's parameters. As in the proof file's description the lookup states its own claims, so
that K4's first run begins at the format's group 2. Other than there: a name of its own, and
no message that must stand before. -/
def toyPar (Q : K4Pub) : Par :=
  { name := "K4 in a trial", link := Q.link, piece := Q.piece, before := [], k3Runs := true,
    P := Q.P, hp := Q.hp, g := Q.g }

/-- K4's part of the carried state: the link's own state is a blank, which K4 does not read; the
ledger; what the lookup returned; the plan's entry for the smallness test; nothing is owed; the
request's tokens. -/
def toyPart (Q : K4Pub) (F : Fork) (fo : Forest.Heard) (tokv : Array Nat) : Part :=
  ({ L := { check := { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ } }, F := F,
     fo := some fo, tl := Q.hp.tl }, none, tokv)

/-! ## 2 K4's own sub-protocol -/

/-- What K4's sub-protocol leaves. -/
structure ToyHeard where
  /-- what its decision heard -/
  own : Own
  /-- the ledger behind both runs of claims -/
  F : Fork
  /-- the state behind both runs -/
  s : Part
  /-- the first run's claims (the format's groups 2 to 12); the second's (14 and 15) -/
  front : List Aff
  back : List Aff

/-- **K4's own sub-protocol on rounds as a view shows them**: its step (`Block.step`,
Johnson/Desc/Block.lean: the rounds fit its own; no column is owed; its decision), then its runs
"front" and "back". A rejection bears the step's or the sub-protocol's own name for it. -/
def toyHear (Q : K4Pub) (s : Part) (rs : List Fmt.RoundView) : Except String ToyHeard := do
  let b := block seatOwn (toyPar Q)
  let (s1, _) ← b.step 0 s rs []
  let f ← named "the sub-protocol states no run front" (b.claims.lookup "front")
  let x ← f 0 s1
  let g ← named "the sub-protocol states no run back" (b.claims.lookup "back")
  let y ← g 0 x.2
  let o ← named "nothing was heard" (seatOwn.own y.2)
  pure { own := o, F := seatOwn.fork y.2, s := y.2, front := x.1, back := y.1 }

/-! ## 3 The claims by the format's groups -/

/-- The format's groups of K4's two runs, in the runs' order, each with the number of its claims. -/
def toyGroups (Q : K4Pub) : List (String × Nat) :=
  let y := Q.P.y
  let xl := y.h.xl
  [("2", 3), ("3", 2), ("4", ledNO xl * y.NI), ("5", ledNS xl * y.NI), ("6", ledLines xl * y.NI),
   ("7", nEndT y), ("8", 3), ("9", 3), ("10", y.LamM), ("11", 3)] ++
  (if Q.g == 0 then [("12", 1)] else []) ++ [("14", 3), ("15", 1)]

/-- A list cut into named stretches; what is left over stands under "beyond the groups". -/
def cutBy {α : Type} : List (String × Nat) → List α → List (String × List α)
  | [], [] => []
  | [], l => [("beyond the groups", l)]
  | g :: gs, l => (g.1, l.take g.2) :: cutBy gs (l.drop g.2)

/-! ## 4 Values -/

/-- **The honest reads**, of the verifier's finished list of tables. THE THREE TABLES ON THE
LOOKUP's PLANES ARE MADE BY A RULE FOR A MATRIX WITH FEW CELLS OTHER THAN 0: that matrix has
millions of cells, and a table on it has one entry for each column: the sum over the rows of the
table's weight times the cell. laid: (row, column) of every cell of that matrix that may be other
than 0: these alone are visited, each once, however often it is listed. A cell other than 0 that is
not listed is missed. A listed column that the matrix does not have is not refused: it falls on the
entry of that number behind the table's first, another table's. -/
def toyReads (Q : K4Pub) (o : Own) (cell : Nat → Nat → Nat → F) (laid : List (Nat × Nat)) : Reads :=
  let iB := (matIx Q.P.y).iB
  let n := Q.hp.nU.getD 2 0
  let U := readsOf (matsOf Q) (o.funs.filter (·.mat != iB)) n cell
  let U := (o.funs.filter (·.mat == iB)).foldl
    (fun U f => laid.eraseDups.foldl
      (fun (U : Array E) x => U.modify (f.start + x.2) fun u =>
        maddS u (cell iB x.1 x.2) (f.phi.getD x.1 zeroE))
      U)
    U
  { u3 := fun e => U.getD e zeroE, has := fun e => decide (e < n) }

/-- **The hidden value under a slot**: what was shown less the factor times the mask entry; at a
slot that `laid` names: that value. -/
def toyHidden (F : Fork) (mask : Nat → E) (laid : Nat → Option E) (j : Nat) : E :=
  match laid j with
  | some x => x
  | none => subE (F.vp.getD j zeroE) (mulE (F.mf.getD j zeroE) (mask j))

/-- **Each claim's value**, group by group; nothing for a claim that names an entry of the reads
that is not there, or an entry of another array. -/
def toyValues (Q : K4Pub) (H : ToyHeard) (R : Reads) (hid : Nat → E) :
    List (String × List (Option E)) :=
  cutBy (toyGroups Q) ((H.front ++ H.back).map (valAff? H.own.v R hid))

/-- **The claims that are not 0**: group and number in the group. A claim that cannot be valued
counts as not 0. A claim beyond the groups is held like any other: it is listed, under that name,
only if its value is not 0 or lacks: A CLAIM TOO MANY WHOSE VALUE IS 0 IS NOT SEEN. NOR DOES IT SEE
A LIST THAT IS TOO SHORT: a group with fewer claims than are due yields fewer values; whoever wants
that seen counts the values of each group as well. -/
def toyBad (vs : List (String × List (Option E))) : List (String × Nat) :=
  vs.flatMap fun g => (g.2.zipIdx.filter fun x => x.1 != some zeroE).map fun x => (g.1, x.2)

/-! ## 5 The value of a slot at which a claim is 0 -/

/-- The hidden value of slot j at which the form a is 0, all else as `hid` has it; nothing if the
form cannot be valued or does not name the slot. -/
def toySolve (v : Env) (R : Reads) (hid : Nat → E) (j : Nat) (a : Aff) : Option E :=
  let k := a.slots.foldl (fun s x => if x.1 == j then addE s x.2 else s) zeroE
  if isZeroE k then none
  else (valAff? v R (fun i => if i == j then zeroE else hid i) a).map fun c =>
    negE (mulE c (invE k))

/-! ## 6 Behind the batching -/

/-- The stand-in form: the sum of the hidden values under all slots below `used` that are not K4's
own: below `first`, or from `last` on. -/
def toyNeighbours (used first last : Nat) : Aff :=
  { slots := ((List.range used).filter fun j => decide (j < first) || decide (last ≤ j)).toArray.map
      fun j => (j, oneE) }

/-- **The state behind the adding**: to the ledger the stand-in form and K4's claims have been added
under the powers of theta. drop: the number of a claim, in the two runs' order, that is left out. -/
def toyAdded (Q : K4Pub) (H : ToyHeard) (theta : E) (drop : Option Nat) : Except String Part := do
  let first := Model.Forest.elems Q.P.y.fo
  let fs := ((H.front ++ H.back).zipIdx.filter fun x => some x.2 != drop).map (·.1)
  let F ← named "theta is sampled twice" (H.F.batchBy theta)
  let G ← named "a form cannot be added"
    (addForms (toyNeighbours Q.hp.used first (H.own.wo.sFv + 1) :: fs).toArray F)
  pure (seatOwn.setFork H.s G)

/-- **K4's own test behind the batching**, at the state behind the adding. The answer is the
sub-protocol's, and its rejection bears its name, "K4.free-slot"; a rejection of the adding in front
bears `toyAdded`'s own name and is no answer of the test. -/
def toyFree (Q : K4Pub) (H : ToyHeard) (theta : E) (drop : Option Nat) : Except String Unit := do
  let b := block seatOwn (toyPar Q)
  let s ← toyAdded Q H theta drop
  let t ← named "the sub-protocol states no run free-slot" (b.after.lookup "free-slot")
  let _ ← t s
  pure ()

/-! ## 7 The row that the merge hands on -/

/-- **The row on the committed weights**: the matrix under the weights that the merge leaves on its
rows and the equality weights of its point on the columns, plus its factor times an entry of the
index-mask message, is the end value as it was shown. TYPED ANEW after the verifier's `wsPending`
(OnBytes/Model/Pending.lean), which makes that row as data: the rows' weights by the same call of
`wsGammaAdd`; the point's first coordinate at the highest column bit. Nothing: a weight cannot be
added. -/
def toyPending (Q : K4Pub) (wo : WsForkOut) (w : Nat → Nat → F) (entry : E) : Option Bool :=
  let lay := Q.P.wsLay
  (wo.recs.foldlM (m := Except String) (fun G r => wsGammaAdd G lay r oneE)
    (Array.replicate lay.m0 zeroE)).toOption.map fun G =>
    let q := eqTab wo.rm
    let sum := (List.range lay.m0).foldl
      (fun t y =>
        let gy := G.getD y zeroE
        if isZeroE gy then t
        else addE t (mulE gy ((List.range q.size).foldl
          (fun u c => maddS u (w y c) (q.getD c zeroE)) zeroE)))
      zeroE
    addE sum (mulE wo.beta entry) == wo.fvp

/-! ## 8 Turns -/

/-- Rounds with the first word of scalar number j of round number i raised by one. -/
def toyTurn (rs : List Fmt.RoundView) (i j : Nat) : List Fmt.RoundView :=
  rs.zipIdx.map fun r =>
    if r.2 != i then r.1
    else { r.1 with vals := r.1.vals.zipIdx.map fun v =>
      if v.2 != j then v.1
      else match v.1 with
        | .e x => .e (addF x.1 1, x.2)
        | y => y }

/-- Where scalars are sent: round, number in the round. -/
def toyScalars (rs : List Fmt.RoundView) : List (Nat × Nat) :=
  rs.zipIdx.flatMap fun r => (List.range r.1.vals.length).map fun j => (r.2, j)

#guard cutBy [("a", 2), ("b", 1)] [1, 2, 3] == [("a", [1, 2]), ("b", [3])]
#guard cutBy [("a", 2)] [1, 2, 3] == [("a", [1, 2]), ("beyond the groups", [3])]
#guard toyBad [("2", [some zeroE, some oneE, none]), ("11", [none]), ("14", [some zeroE])] ==
  [("2", 1), ("2", 2), ("11", 0)]
#guard (toyNeighbours 6 2 4).slots.map (·.1) == #[0, 1, 4, 5]
#guard toyScalars [⟨[], ⟨[], [], [], none⟩⟩, ⟨[.e (1, 2, 3), .e (4, 5, 6)], ⟨[], [], [], none⟩⟩] ==
  [(1, 0), (1, 1)]
#guard ((toyTurn [⟨[.e (1, 2, 3), .e (4, 5, 6)], ⟨[], [], [], none⟩⟩] 0 1).map (·.vals)) ==
  [[.e (1, 2, 3), .e (5, 5, 6)]]

end OnBytes.Desc.First.K4.Honest
