-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Parts.lean: the parts of the state S that the proof file's first chain carries
(State.lean), as lenses and parts (Johnson/Desc/Lens.lean), each with its laws.

  Always there (`Lens`): `stL`, `bookL`, `rootsL`, `outL`, `liveL`.
  `walkCheckP`: the walk's copy of the state of the calls: absent inside a link.
  NO LENS, on purpose: the mark of a failed test (`marks` is the guarded way; State.lean's `S.mark`
    keeps the first), the rows owed (State.lean's `closeOk`, `owe`, `pay`, `closed`), and "here".
  There while the chain stands at one kind of place (`Part`): `layP`, `attP`, `headP`, `finP`,
    `memP`.
  There inside a link of any of the three kinds (`Part`): `forkP`, `linkP`, `tlP`, `lookP`:
    State.lean's four pairs.
  `tlForkP`: the smallness test's record with the sub-proof's state, as one part.
  `liveL`: the live copy of the state of the calls: State.lean's `S.live` and `S.putLive`.
  The sub-proof's list of tables is read alone: State.lean's `S.funs?`.
A step that is typed at a part's state becomes a step at S by `Part.lift` or `Part.liftWith`. At a
state where the part is not there the wrapped step refuses: so a step that is run at the wrong KIND
of place refuses. Inside a link a part that no step has laid yet reads as State.lean's blank.
Limits: definitions and the laws of get and set. No step of the protocol is in this file (`marks`
makes a step of a test that is handed to it).

-/
import Johnson.Desc.Lens
import Johnson.Desc.First.State

set_option autoImplicit false

namespace VerifiableInference.Desc.First

open OnBytes OnBytes.Model VerifiableInference.Desc

/-! ## Always there -/

/-- The statement. -/
def stL : Lens S Statement := ⟨(·.st), fun s x => { s with st := x }⟩

theorem stL_lawful : stL.Lawful := ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The book of trees. -/
def bookL : Lens S TreeBook := ⟨(·.book), fun s x => { s with book := x }⟩

theorem bookL_lawful : bookL.Lawful := ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The number of roots received so far. -/
def rootsL : Lens S Nat := ⟨(·.roots), fun s x => { s with roots := x }⟩

theorem rootsL_lawful : rootsL.Lawful := ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The walk's three. -/
def outL : Lens S Proof.LinksResult := ⟨(·.out), fun s x => { s with out := x }⟩

theorem outL_lawful : outL.Lawful := ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The walk's copy of the state of the calls. Inside a link it is an earlier state, and the link's
last step overwrites it: there this part is absent. Inside a link read `liveL`. -/
def walkCheckP : Part S ChainCheck :=
  ⟨fun s => if s.inLink then none else some s.check,
   fun s c => if s.inLink then s else { s with check := c }⟩

theorem walkCheckP_lawful : walkCheckP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [walkCheckP, S.inLink, S.fork?]

/-- A named test on values that marks and goes on, as a step: where the test says no, the state is
marked by State.lean's `S.mark`, which keeps the first mark; where it cannot be asked, the step
refuses. The mark has no lens: no step can wipe it. -/
def marks (name : String) (b : S → Option Bool) : Step S :=
  Step.quiet fun s => (b s).map fun ok => if ok then s else s.mark name

/-! ## There at one kind of place

"here", and the head's "opened", are turned by State.lean's enter.., openHead and leaveLink alone: a
step that lays one of these five parts back must leave them as they were. -/

/-- What is held inside a layers' link. -/
def layP : Part S LayOwn :=
  ⟨fun s => match s.here with
     | .lay a => some a
     | _ => none,
   fun s a => match s.here with
     | .lay _ => { s with here := .lay a }
     | _ => s⟩

theorem layP_lawful : layP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> simp_all [layP]

/-- What is held inside an attention link. -/
def attP : Part S AttOwn :=
  ⟨fun s => match s.here with
     | .att a => some a
     | _ => none,
   fun s a => match s.here with
     | .att _ => { s with here := .att a }
     | _ => s⟩

theorem attP_lawful : attP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> simp_all [attP]

/-- What is held inside the head's link. -/
def headP : Part S HeadOwn :=
  ⟨fun s => match s.here with
     | .head a => some a
     | _ => none,
   fun s a => match s.here with
     | .head _ => { s with here := .head a }
     | _ => s⟩

theorem headP_lawful : headP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> simp_all [headP]

/-- What is held in the finish. -/
def finP : Part S FinOwn :=
  ⟨fun s => match s.here with
     | .fin a => some a
     | _ => none,
   fun s a => match s.here with
     | .fin _ => { s with here := .fin a }
     | _ => s⟩

theorem finP_lawful : finP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> simp_all [finP]

/-- What is held at the chain's end. -/
def memP : Part S MemOwn :=
  ⟨fun s => match s.here with
     | .mem a => some a
     | _ => none,
   fun s a => match s.here with
     | .mem _ => { s with here := .mem a }
     | _ => s⟩

theorem memP_lawful : memP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> simp_all [memP]

/-! ## There inside a link of any kind -/

/-- The sub-proof's state. -/
def forkP : Part S Fork := ⟨S.fork?, S.putFork⟩

theorem forkP_lawful : forkP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [forkP, S.fork?, S.putFork] <;> (try subst_vars) <;>
    first | rfl | (cases a <;> simp_all)

/-- The link, with the live state of the calls. -/
def linkP : Part S LinkCtx := ⟨S.link?, S.putLink⟩

theorem linkP_lawful : linkP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [linkP, S.link?, S.putLink] <;> (try subst_vars) <;>
    first | rfl | (cases a <;> simp_all)

/-- The smallness test's record. -/
def tlP : Part S HTailF2 := ⟨S.tl?, S.putTl⟩

theorem tlP_lawful : tlP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [tlP, S.tl?, S.putTl] <;> (try subst_vars) <;>
    first | rfl | (cases a <;> simp_all)

/-- What the lookup on the calls returned. At a layers' link this value has a second home: the
program's claims read it in what the own rounds returned (`own.H.fo`): whoever types these claims
reads ONE of the two and names it in its list. -/
def lookP : Part S Forest.Heard := ⟨S.look?, S.putLook⟩

theorem lookP_lawful : lookP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;>
    (try (rename_i a; first
      | (cases hf : a.fo)
      | (cases hf : a.g)
      | (cases hO : a.opened <;> cases hx : a.x <;> cases hl : a.lookHeard))) <;>
    simp_all [lookP, S.look?, S.putLook] <;> (try subst_vars) <;>
    first | rfl | (cases a <;> simp_all)

/-- The smallness test's record and the sub-proof's state do not overlap. -/
theorem tlP_apart_forkP : tlP.Apart forkP := by
  refine ⟨fun s q => ?_, fun s p => ?_, fun s p q => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [tlP, forkP, S.tl?, S.putTl, S.fork?, S.putFork]

/-- The smallness test's record with the sub-proof's state. -/
def tlForkP : Part S (HTailF2 × Fork) := tlP.pair forkP tlP_apart_forkP

theorem tlForkP_lawful : tlForkP.Lawful := by
  refine ⟨fun s p q h => ?_, fun s p h => ?_, fun s p q => ?_, fun s p h => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [tlForkP, Part.pair, tlP, forkP, S.tl?, S.putTl, S.fork?, S.putFork] <;>
    (try subst_vars) <;>
    first | rfl | (cases a <;> simp_all)

/-- The live copy of the state of the calls: the link's own inside a link, else the walk's
(State.lean's `S.live`, `S.putLive`). -/
def liveL : Lens S ChainCheck := ⟨S.live, S.putLive⟩

theorem liveL_lawful : liveL.Lawful := by
  refine ⟨fun s p => ?_, fun s => ?_, fun s p q => ?_⟩ <;>
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here⟩ := s <;>
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [liveL, S.live, S.putLive, S.link?, S.putLink] <;> (try subst_vars) <;>
    first | rfl | (cases a <;> simp_all)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.forkP_lawful
#print axioms VerifiableInference.Desc.First.attP_lawful
#print axioms VerifiableInference.Desc.First.tlForkP_lawful
#print axioms VerifiableInference.Desc.First.liveL_lawful
#print axioms VerifiableInference.Desc.First.walkCheckP_lawful
#print axioms VerifiableInference.Desc.First.tlP_apart_forkP
#print axioms VerifiableInference.Desc.First.layP_lawful
#print axioms VerifiableInference.Desc.First.headP_lawful
#print axioms VerifiableInference.Desc.First.finP_lawful
#print axioms VerifiableInference.Desc.First.memP_lawful
#print axioms VerifiableInference.Desc.First.linkP_lawful
#print axioms VerifiableInference.Desc.First.tlP_lawful
#print axioms VerifiableInference.Desc.First.lookP_lawful
