-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Parts.lean: the five parts that the proximity test's frame asks for (the batching,
a fold, a new group, a code switch with the batching behind it, the base case) over one plain state.
Definitions only, all computable; nothing is proved here.

What stands beneath, each called and none typed again: the test's frame and its code switch's test
(Johnson/Desc/Test/Frame.lean, `TestParts`; Test/Cs.lean, `csTest`); the batching and the fold
(Johnson/Desc/First/Close/Closing.lean, `bat`, `foldD`); the plain ground and its sending
(Johnson/Desc/Ground/Record.lean and what it imports: `newGroupP`, `beginRunP`, `sendP`); the step
behind a switch's sending (Johnson/Top/H0/Tw/L9/Switch.lean, `switchGuard`, `switchNotices`,
`switchBehind`); the base step (Johnson/Desc/First/Base/Meanwhile.lean and Base.lean, `baseE`,
`spendPlain`, `readPlain`).

The state `PS`. The statement, the book of trees, the roots received and the opened columns not yet
read (the ground's `DState`); the stretch's rounds and entries still to come; the entry of the round
closed last, and whether its count of rows has been compared: what is owed is a function of the two
(`PS.owed`: the negation of the verifier program's `Chan.settled`); the chain's two numbers (answers
to a sample; first tree); for the base step: the stages behind the present one, and the present
stage with its claim.

The guards of this file's own, by the names under which they refuse.
  The stretch has what the part takes:
    (t1) the batching: an entry and a round.  (t2) a fold: 1 + k entries, 1 + k rounds.
    (t3) the switch: two entries, two rounds.  (t4) the base case: two entries, two rounds.
  Nothing is owed, and the count of rows (the verifier program's `Blk.close` and `Blk.requireRows`):
    (o1) in front of "BAT".  (o2) in front of "FOLD epsilon".  (o3) in front of "SEND seed".
    (o4) "SEND seed" counts no rows, so that "CS" finds nothing owed.
    (o5) the count that "CS"'s entry owes is the number of rows batched; refused where nothing is
         owed.
    (o6) in front of "BASE lambda": handed to the base step as `settled`.
  A round's closing:
    (c1) "SEND seed": the entry's name.  (c2) It draws as many elements other than 0 as the largest
         number of answers among the notices.  (c3) The numbers of elements, positions and matrix
         entries drawn are the entry's.
    (c4) "CS": the entry's name.  (c5) The entry draws one element.  (c6) The round draws just one.
  The fit of the texts beneath:
    (f1) the switch serves the form with theta alone. (f2) A stage stands behind the one that has
         run. (f3) The class of leaves is 0. (f4) No stage is behind the last. (f5) `ioppLastRows`
         of the carried stage, row and layout is the frame's record of single rows, by `sameSingle`:
         every field of the record.

Limits. The step behind a switch's sending is the form that was written for a link's "LOC":
`switchE` hands it the round "CS" under the name "LOC", without theta; three of its own guards are
idle by that making, and (c4) to (c6) ask what they stood for. "Plain" is not "written anew": the
texts beneath call the verifier program's pure functions by name. Not here: the codes' lengths; the
test on the schedule as it lies in the record; the end (all used up). `baseE'` serves
`plainParts.base` (the frame of Test/Frame.lean) and the last part of Join.lean's `proximityTestParts`; the
kind's block over `guardedProximityTestParts` (JoinGuarded.lean) has its own last part and reaches neither. The namespace
is H2K, under which the files that stand on this one name it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Test.Frame
import Johnson.Desc.Test.Cs
import Johnson.Desc.First.Close.Closing
import Johnson.Top.H0.Tw.L9.Switch
import Johnson.Desc.First.Base.Meanwhile
import Johnson.Desc.Ground.Record

set_option autoImplicit false
namespace H2K
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Test

/-- The plain state of a test's stretch. -/
structure PS where
  p : GPar
  d : DState Unit
  rounds : List Fmt.RoundView
  entries : List Fmt.Entry
  /-- the entry of the round closed last -/
  last : Option Fmt.Entry
  /-- its count of rows has been compared -/
  asked : Bool
  later : List IoppStage
  cur : Option (IoppStage × GroupRow × GroupLayout)

/-- The rows that the entry of the round closed last counts, while nobody has compared them. -/
def PS.owed (s : PS) : Option Nat :=
  match s.last with
  | some e => if e.rows == 0 || s.asked then none else some e.rows
  | none => none

def need (why : String) (b : Bool) : Except String Unit := if b then .ok () else .error why

def opt {α : Type} (why : String) : Option α → Except String α
  | some a => .ok a
  | none => .error why

/-! ## Two records of single rows are one: field by field (for guard (f5)) -/

def sameTensor (a b : Tensor) : Bool :=
  a.scalar == b.scalar && a.pairs == b.pairs && a.denseVars == b.denseVars &&
    a.values == b.values && a.first == b.first

def sameForm (a b : Form) : Bool :=
  a.tensors.length == b.tensors.length &&
    (a.tensors.zip b.tensors).all (fun p => sameTensor p.1 p.2) && a.entries == b.entries

def sameLayout (a b : GroupLayout) : Bool :=
  a.k == b.k && a.h == b.h && a.logEll == b.logEll && a.logEllZk == b.logEllZk &&
    a.members == b.members && a.kept == b.kept && a.mainFirst == b.mainFirst &&
    a.maskFirst == b.maskFirst

def sameSingle (a b : SingleRows) : Bool :=
  a.code == b.code && a.maskCode == b.maskCode && sameLayout a.layout b.layout &&
    a.gamma == b.gamma && a.masks == b.masks && a.fresh == b.fresh && sameForm a.c b.c &&
    a.kept.size == b.kept.size &&
    (a.kept.zip b.kept).all (fun p => p.1.oracle == p.2.oracle && sameForm p.1.c p.2.c) &&
    a.d == b.d && a.target == b.target && a.keptRows == b.keptRows

/-- The batching. -/
def batE (g : Nat) (s : PS) : Except String ((GroupRow × GroupLayout) × PS) :=
  match s.entries, s.rounds with
  | e :: es, r :: rs => do
    need "bat (o1): a count of rows is owed" s.owed.isNone
    let x ← (First.Close.bat s.d.st g e r).mapError ("bat: " ++ ·)
    pure ((x.1, x.2.1),
      { s with d := { s.d with st := x.2.2 }, entries := es, rounds := rs, last := some e,
               asked := true })
  | _, _ => .error "bat (t1): no entry or no round"

/-- A fold, both arms. -/
def foldE (F : FoldShape) (row : GroupRow) (mask : Option Nat) (s : PS) :
    Except String (SingleRows × PS) := do
  let n := 1 + F.layout.k
  need "fold (o2): a count of rows is owed" s.owed.isNone
  need "fold (t2): the stretch is short"
    (decide (n ≤ s.entries.length) && decide (n ≤ s.rounds.length))
  let x ← (First.Close.foldD s.p.firstTree s.d F row mask (s.entries.take n)
    (s.rounds.take n)).mapError ("fold: " ++ ·)
  pure (x.1, { s with d := x.2, entries := s.entries.drop n, rounds := s.rounds.drop n,
                      last := (s.entries.take n).getLast?, asked := false })

def newGroupE (code maskCode : Nat) (s : PS) : Except String (Nat × PS) :=
  (opt "new group: the ground refuses the new group" (Ground.newGroupP s.d code maskCode)).map
    fun x => (x.1, { s with d := x.2 })

def askOwedE (rows : Nat) (s : PS) : Except String PS :=
  match s.owed with
  | some k =>
    if k == rows then .ok { s with asked := true }
    else .error "cs (o5): the entry counts another number of rows"
  | none => .error "cs (o5): no count is owed"

def fitsE (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
    r.drawn.trits.length == e.trits

/-- The switch inside a test: the guard; the sending; the step behind it. -/
def switchE (old : SingleRows) (T : SwitchTarget) (to : Nat) (others : Array OracleNotice)
    (withTheta : Bool) (s : PS) : Except String ((Switched × E) × PS) :=
  match s.entries, s.rounds with
  | e₁ :: e₂ :: es, r₁ :: r₂ :: rs => do
    let notices := Tw.L9.switchNotices T others
    let nz := notices.foldl (fun a n => max a n.shape.answers) 0
    need "switch (f1): the form without theta is not served" withTheta
    need "switch G0: the old rows, the target and the statement do not fit a switch"
      (Tw.L9.switchGuard s.d.st old T)
    need "switch (o3): a count of rows is owed" s.owed.isNone
    need "switch (c1): the entry is not SEND seed" (e₁.name == "SEND seed")
    need "switch (c2): SEND seed does not draw as many elements other than 0 as the notices ask"
      (e₁.drawNZ == nz)
    need "switch (c3): SEND seed's numbers of draws are not its entry's" (fitsE e₁ r₁)
    need "switch (o4): SEND seed counts rows" (e₁.rows == 0)
    need "switch (c4): the entry is not CS" (e₂.name == "CS")
    need "switch (c5): CS's entry does not draw one element" (e₂.drawE == 1)
    let (ids, _, _, took, d₂) ← opt "switch: the ground refuses the sending"
      (sendP Ground.groundG s.p false s.d notices r₁ r₂)
    let x ← match r₂.drawn.elems with
      | [x] => pure x
      | _ => throw "switch (c6): CS does not draw just one element"
    let i : Tw.L9.SwIn :=
      { st := d₂.st, book := d₂.book, firstTree := s.p.firstTree, opened := d₂.opened, old := old,
        T := T, grp := to, ids := ids, entry := { e₂ with name := "LOC", drawE := 0 },
        settled := true,
        drawn := { r₂.drawn with elems := [] }, itemsLeft := r₂.vals.length - took }
    let o ← (Tw.L9.switchBehind i).mapError ("switch " ++ ·)
    pure ((o.out, E.ofTriple x),
      { s with d := { d₂ with st := o.st, book := o.book, opened := o.opened }, entries := es,
               rounds := rs, last := some e₂, asked := false })
  | _, _ => .error "switch (t3): the stretch is short"

def beginRunE (g : Nat) (s : PS) : Except String (RunInput × PS) :=
  (opt "cs: the ground refuses to begin the group's test" (Ground.beginRunP s.d g)).map fun x =>
    (x.1, { s with d := x.2 })

/-- What csTest (Johnson/Desc/Test/Cs.lean) calls. -/
def csParts : CsParts PS where
  statement := fun s => s.d.st
  switch := fun old T to others th s => (switchE old T to others th s).toOption
  beginRun := fun g s => (beginRunE g s).toOption
  askRows := fun rows s => (askOwedE rows s).toOption

/-- The stage that the switch has entered, with its claim, goes into the state. -/
def enter (x : (Switched × GroupRow × GroupLayout) × PS) :
    Except String ((Switched × GroupRow × GroupLayout) × PS) :=
  match x.2.later with
  | next :: rest => .ok (x.1, { x.2 with later := rest, cur := some (next, x.1.2.1, x.1.2.2) })
  | [] => .error "cs (f2): no stage behind"

/-- The last step. -/
def baseE' (R : SingleRows) (mask : Option Nat) (leafClass : Nat) (s : PS) : Except String PS :=
  match s.cur, s.entries, s.rounds with
  | some (cur, row, L), eL :: eB :: es, rL :: rB :: rs => do
    need "base (f3): the class of leaves is not 0" (leafClass == 0)
    need "base (f4): a stage is behind" s.later.isEmpty
    need "base (f5): the carried stage, row and layout do not give the frame's single rows"
      (((ioppLastRows cur L row).map (sameSingle R)).getD false)
    let (b, took) ← (First.Base.baseE First.Base.spendPlain First.Base.readPlain
        { firstTree := s.p.firstTree, eLam := eL, eBase := eB }
        { st := s.d.st, book := s.d.book, settled := s.owed.isNone, cur := cur, later := [],
          row := row, L := L, mask := mask }
        [rL, rB] s.d.opened).mapError ("base " ++ ·)
    pure { s with d := { s.d with st := b.st, book := b.book, opened := s.d.opened.drop took },
                  entries := es, rounds := rs, last := some eB, asked := false }
  | _, _, _ => .error "base (t4): no stage entered, or the stretch is short"

/-- **The frame's five parts, all plain.** -/
def plainParts : TestParts PS where
  samples := fun s => s.p.samples
  codes := fun s => s.d.st.codes
  group := fun g s => s.d.st.groups[g]?
  bat := fun g s => (batE g s).toOption
  fold := fun F row mask s => (foldE F row mask s).toOption
  newGroup := fun code maskCode s => (newGroupE code maskCode s).toOption
  cs := fun old T to others s =>
    (csTest csParts old T to others s).bind fun x => (enter x).toOption
  base := fun R mask leafClass s => (baseE' R mask leafClass s).toOption

end H2K
