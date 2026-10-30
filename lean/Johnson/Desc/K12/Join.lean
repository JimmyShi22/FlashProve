-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Join.lean: the proximity test (the kind K12): ITS PARTS' DECISIONS,
so that the kind's block (Johnson/Desc/K12/Frame.lean) can run: the record inside the test (`T12`)
and the six parts (`proximityTestParts : Parts T12`): the front: a call of `frontE`
(Johnson/Desc/K12/Front.lean: nineteen named clauses on the schedule as it lies in the record, then
the eight clauses on each claim that lies open on the group); the others: each a call of the kind's
plain function of that part (Johnson/Desc/K12/Parts.lean: batE · foldE with newGroupE ·
switchE · baseE'), and, behind a switch, the last lines of csTest (Johnson/Desc/Test/Cs.lean). No
byte of these files is turned. Definitions with code; no theorem.

How a part decides: it lays the record, its own rounds as the view shows them, its entries (out of
the declared rounds that the frame has cut for it) and its columns (keyed anew from the declared
openings) into that file's state; calls the function; asks that rounds, entries and columns are all
used up; and lays what comes back into the record.
T12: the running record of messages, groups and pending claims;
the book of trees; the count of roots; the number of the group under test; what passes from part to
part (`Passing`: one of four forms); the number of the message that holds the present stage's mask.
GUARDS OF THIS FILE's OWN, none on a value that a prover sends:
  (u) a part finds `Passing` in the form that the part before it leaves;
  (v) rounds, entries and columns are used up;
  (w) in front of the batching: the record's codes at the numbers `P12.idx` are the stages' codes
      (so that `sizesOk`, which reads the stages, speaks of the codes that the parts use);
  (x) behind the batching: the group's two codes have the first stage's numbers;
  on the plan: `idx` has a pair for each stage; no round of the test opens a stored table.
Limits: the functions beneath call the verifier program's pure functions
by name and use its types. "Nothing is owed in front of a round" is not asked: the record holds no
such count; the count of claims behind a switch is asked against that switch's last entry. The
columns' keys are made anew with the place's own `firstTree`, which is also what the functions
beneath hold them against: so these hold nothing new on a key: `Block.step` has asked key, position
and width. How T12 is entered from a chain's record and left again: `Block.inside` with two
functions that are not here. Nothing has run on a proof.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Frame
import Johnson.Desc.K12.Parts
import Johnson.Desc.K12.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Test (CsParts csTest)

/-- What passes from a part to the next. -/
inductive Passing where
  /-- in front of the batching, and behind the base case -/
  | nothing
  /-- behind a batching: the one claim with its layout -/
  | claim (row : GroupRow) (L : GroupLayout)
  /-- behind a fold: the single rows, and the new group's number -/
  | single (rows : SingleRows) (to : Nat)
  /-- behind a switch: what it returned, the element drawn last, and the new group's number -/
  | switched (out : Switched) (theta : E) (to : Nat)

/-- **The record inside a proximity test.** -/
structure T12 where
  st : Statement
  book : TreeBook
  roots : Nat
  /-- the number of the group under test -/
  g : Nat
  pass : Passing
  /-- the number of the message that holds the present stage's mask, if it has come -/
  mask : Option Nat

/-- The columns with their keys: group by group, a key for each tree that the rounds open. -/
def keyed (p : P12) (cut : List Fmt.DeclaredRound) (gs : List (List (Nat × List UInt64))) :
    List (Nat × Nat × List UInt64) :=
  ((cut.flatMap fun r => r.opens.map fun o => o.1.tree - p.nums.firstTree).zip gs).flatMap fun x =>
    x.2.map fun c => (x.1, c.1, c.2)

/-- The record, a part's rounds, entries and columns as the plain state `H2K.PS`. last: the entry
whose count of claims is still to be compared, if any. -/
def lay (p : P12) (cut : List Fmt.DeclaredRound) (last : Option Fmt.Entry) (t : T12)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : H2K.PS :=
  { p := { samples := p.answers, firstTree := p.nums.firstTree }
    d := { st := t.st, book := t.book, roots := t.roots, opened := keyed p cut gs, loc := () }
    rounds := rs, entries := cut.map (·.entry), last := last, asked := false, later := []
    cur := none }

/-- The state laid back, if all is used up: guard (v). -/
def back (t : T12) (s : H2K.PS) (pass : Passing) (mask : Option Nat) : Except String T12 := do
  need "(v): a round, an entry or a column is left over"
    (s.rounds.isEmpty && s.entries.isEmpty && s.d.opened.isEmpty)
  pure { t with st := s.d.st, book := s.d.book, roots := s.d.roots, pass := pass, mask := mask }

/-- Guard (u)'s words. -/
def wrongForm {α : Type} (part : String) : Except String α :=
  .error ("(u): " ++ part ++
    ": what the part before handed on has the wrong form, or the plan has no such stage")

/-- Stage number j in the program's form: its codes by their numbers. -/
def stageAt (p : P12) (j : Nat) (s : Fmt.M1.Stage) : Option IoppStage :=
  (p.idx[j]?).map fun i => { code := i.1, maskCode := i.2, k := s.k, h := s.h }

/-- Guard (w). -/
def codesFit (p : P12) (st : Statement) : Bool :=
  (p.nums.stages.zip p.idx).all fun x =>
    st.codes.base[x.2.1]? == some { logN := x.1.C.a, ell := x.1.C.l, r := x.1.C.r } &&
      st.codes.mask[x.2.2]? == some { logN := x.1.Z.a, ell := x.1.Z.l, r := x.1.Z.r }

/-- No round opens a stored table. -/
def noStored (cut : List Fmt.DeclaredRound) : Bool := cut.all (·.stored.isEmpty)

/-- The front: the schedule as it lies in the record, then every claim that lies open on the group
(Johnson/Desc/K12/Front.lean: `frontE`). It turns nothing. -/
def frontJ (_p : P12) : Part T12 where
  decide := fun t _ _ =>
    match t.pass with
    | .nothing => do
      frontE t.st t.book t.g t.mask
      pure t
    | _ => wrongForm "the front"

def batJ (p : P12) (cut : List Fmt.DeclaredRound) : Part T12 where
  planOk := noStored cut && p.idx.length == p.nums.stages.length
  decide := fun t rs gs =>
    match t.pass, p.idx with
    | .nothing, i :: _ => do
      need "(w): the record's codes are not the stages'" (codesFit p t.st)
      let x ← H2K.batE t.g (lay p cut none t rs gs)
      need "(x): the group's two codes are not the first stage's"
        ((x.2.d.st.groups[t.g]?).any fun G => G.code == i.1 && G.maskCode == i.2)
      back t x.2 (.claim x.1.1 x.1.2) (if p.early then t.mask else none)
    | _, _ => wrongForm "the batching"

def foldJ (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) : Part T12 where
  planOk := noStored cut
  decide := fun t rs gs =>
    match t.pass, stageAt p j cur, p.idx[j + 1]? with
    | .claim row L, some c, some n => do
      let x ← H2K.foldE (ioppFoldShape c L) row t.mask (lay p cut none t rs gs)
      let y ← H2K.newGroupE n.1 n.2 x.2
      back t y.2 (.single x.1 y.1) t.mask
    | _, _, _ => wrongForm "the fold"

def switchJ (p : P12) (j : Nat) (_cur next : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) : Part T12 where
  planOk := noStored cut
  decide := fun t rs gs =>
    match t.pass, stageAt p (j + 1) next with
    | .single rows to, some n => do
      let others : Array OracleNotice :=
        if !p.early then #[]
        else if last then #[baseMaskNotice n.code n.maskCode 1 0]
        else #[foldMaskNotice (ioppFoldShape n {})]
      let x ← H2K.switchE rows (switchTargetStage n.code n.maskCode n.k n.h p.answers) to others
        true (lay p cut none t rs gs)
      back t x.2 (.switched x.1.1 x.1.2 to) t.mask
    | _, _ => wrongForm "the switch"

/-- The last lines of csTest: csTest at parts whose switch only hands on what the switch before has
returned. -/
def behindJ (p : P12) (_j : Nat) (_next : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) : Part T12 where
  decide := fun t rs gs =>
    match t.pass with
    | .switched out theta to => do
      let P : CsParts H2K.PS :=
        { H2K.csParts with switch := fun _ _ _ _ _ s => some ((out, theta), s) }
      let x ← named "the batching behind the switch refuses"
        (csTest P {} (switchTargetStage 0 0 0 0 0) to #[]
          (lay p [] (cut.getLast?.map (·.entry)) t rs gs))
      back t x.2 (.claim x.1.2.1 x.1.2.2) (if p.early then out.others[0]? else none)
    | _ => wrongForm "the batching behind the switch"

def baseJ (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) : Part T12 where
  planOk := noStored cut
  decide := fun t rs gs =>
    match t.pass, stageAt p j cur with
    | .claim row L, some c => do
      let R ← named "the base case: the last stage's claim is not on single rows"
        (ioppLastRows c L row)
      let s ← H2K.baseE' R t.mask 0 { lay p cut none t rs gs with cur := some (c, row, L) }
      back t s .nothing none
    | _, _ => wrongForm "the base case"

/-- **The parts, joined.** -/
def proximityTestParts : Parts T12 where
  front := frontJ
  bat := batJ
  fold := foldJ
  switch := switchJ
  batBehind := behindJ
  base := baseJ
  group := fun t =>
    match t.pass, t.st.groups[t.g]? with
    | .claim _ L, some G =>
      match t.st.codes.base[G.code]?, t.st.codes.mask[G.maskCode]? with
      | some c, some z => some (⟨c.logN, c.ell, c.r⟩, ⟨z.logN, z.ell, z.r⟩, L.k, L.h)
      | _, _ => none
    | _, _ => none
  maskCame := fun t => t.mask.isSome

end VerifiableInference.Desc.K12
