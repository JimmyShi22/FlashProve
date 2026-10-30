-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecQuiet.lean: a relation for the blocks that write neither the statement nor a
copy of the frame of the links, nor the book of trees nor the count of roots: from it the invariants
of the first chain's record follow at once.

  Quiet s s': s'.st = s.st, every copy of the frame that s' holds is a copy that s holds (framesIn,
    Johnson/Goal/Meaning/RecAll.lean), s'.book = s.book and s'.roots = s.roots; what ctxOf, openOf
    and armOf read stays; where no count of rows waited none waits; a deferred mark (S.failed) that
    stands stays as it is (Quiet.failed, Quiet.mark, Quiet.unmarked). quiet_refl, quiet_trans.
  recRel_of_quiet: then RecAll is handed on (RecRel, Johnson/Goal/Meaning/RecRel.lean).
  grows_of_quiet: then the statement grows (ChainEnd.GrowsBy fun s => s.st): it is the same.
  whole_mono: Keeps.Whole (Johnson/Desc/FoldKeeps.lean) goes up along an implication of relations.
  whole_of_steps: Keeps.Whole from the three forms Steps, RunsStep, AfterStep of
    Johnson/Desc/Sound/FoldSteps.lean, which say the same, so that the rules of
    Johnson/Desc/Sound/StepsThrough.lean on lifted blocks can be called.
  whole_rec, whole_grows: so Whole Quiet b gives Whole (RecRel cs sh) b and Whole (GrowsBy fun s =>
  s.st) b.
Not claimed: that any block is Quiet.
-/
import Johnson.Goal.Meaning.RecRel
import Johnson.Desc.StatementGrows
import Johnson.Desc.Sound.StepsThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole)

/-- What the record holds of the links' layout and of the open link's name: the walk's copy of the
rows' layout; and, where a link's context lies in the record: of which sort it is (0: a layers' or
an attention link; 1: the head's, not yet counted as open; 2: the head's, open), its own copy of the
rows' layout, the link's number, and its arrays' names. -/
def ctxOf (s : S) : ReqRows × Option (Nat × ReqRows × Nat × Array (Nat × String)) :=
  (s.check.rows,
    match s.here with
    | .lay a => some (0, a.L.check.rows, a.L.link, a.L.arrayOf)
    | .att a => some (0, a.L.check.rows, a.L.link, a.L.arrayOf)
    | .head a => some (if a.opened then 2 else 1, a.L.check.rows, a.L.link, a.L.arrayOf)
    | _ => none)

/-- The statement stays, no new copy of the frame comes in, and the book of trees and the count of
roots stay: what a step that ENTERS a link keeps too. -/
def Enters (s s' : S) : Prop :=
  s'.st = s.st ∧ (∀ f ∈ framesIn s', f ∈ framesIn s) ∧ s'.book = s.book ∧ s'.roots = s.roots

/-- The open link's frame's two lists: the messages of the link's own that stand sent, and those
kept from earlier links. -/
def listsOf (s : S) : Option (Array Nat × Array Nat) :=
  s.link?.map fun L => (L.check.frame.own, L.check.frame.keptBefore)

/-- The open link's own state of the calls, whole, and its count of moments. -/
def openOf (s : S) : Option (ChainCheck × Nat) := s.link?.map fun L => (L.check, L.moments)

/-- In which of its six forms the record's own part stands: 0 between the links, 1 a layers' link,
2 an attention link, 3 the head's link (whether it counts as open: ctxOf's mark), 4 the finish, 5
the members' places. -/
def armOf (s : S) : Nat :=
  match s.here with
  | .between => 0
  | .lay _ => 1
  | .att _ => 2
  | .head _ => 3
  | .fin _ => 4
  | .mem _ => 5

/-- What a quiet step leaves beside what Enters says: ctxOf, openOf and armOf. -/
def ctxW (s : S) := (ctxOf s, openOf s, armOf s)

/-- Enters; what the record holds of the layout and of the open link's name, the open link's state
of the calls and count of moments, and the form in which the record's own part stands, stay;
where no count of rows waited none waits; and a deferred mark (S.failed) that stands stays as it
is. -/
def Quiet (s s' : S) : Prop :=
  Enters s s' ∧ ctxW s' = ctxW s ∧ (s.noneWaits = true → s'.noneWaits = true) ∧
    ∀ e, s.failed = some e → s'.failed = some e

/-- Enters, and what the record holds of the layout and of the open link's name stays: what a step
keeps that writes the open link's state of the calls but not its frame. -/
def Still (s s' : S) : Prop := Enters s s' ∧ ctxOf s' = ctxOf s

theorem Quiet.ctx {s s' : S} (q : Quiet s s') : ctxOf s' = ctxOf s := congrArg Prod.fst q.2.1

theorem Quiet.still {s s' : S} (q : Quiet s s') : Still s s' := ⟨q.1, q.ctx⟩

theorem Quiet.open {s s' : S} (q : Quiet s s') : openOf s' = openOf s :=
  congrArg (fun x => x.2.1) q.2.1

theorem Quiet.arm {s s' : S} (q : Quiet s s') : armOf s' = armOf s :=
  congrArg (fun x => x.2.2) q.2.1

theorem Quiet.waits {s s' : S} (q : Quiet s s') (w : s.noneWaits = true) :
    s'.noneWaits = true := q.2.2.1 w

/-- A deferred mark that stands stays as it is. -/
theorem Quiet.failed {s s' : S} (q : Quiet s s') {e : String} (h : s.failed = some e) :
    s'.failed = some e := q.2.2.2 e h

/-- A marked state stays marked. -/
theorem Quiet.mark {s s' : S} (q : Quiet s s') (h : s.failed ≠ none) : s'.failed ≠ none := by
  cases hf : s.failed with
  | none => exact absurd hf h
  | some e => rw [q.failed hf]; exact fun k => nomatch k

/-- Where the state behind bears no mark, the state in front bore none. -/
theorem Quiet.unmarked {s s' : S} (q : Quiet s s') (h : s'.failed = none) : s.failed = none :=
  Classical.byContradiction fun k => q.mark k h

theorem listsOf_open (s : S) :
    listsOf s = (openOf s).map fun x => (x.1.frame.own, x.1.frame.keptBefore) := by
  unfold listsOf openOf
  cases s.link? <;> rfl

theorem Quiet.lists {s s' : S} (q : Quiet s s') : listsOf s' = listsOf s := by
  rw [listsOf_open, listsOf_open, q.open]

theorem enters_refl (s : S) : Enters s s := ⟨rfl, fun _ h => h, rfl, rfl⟩

theorem quiet_refl (s : S) : Quiet s s := ⟨enters_refl s, rfl, id, fun _ h => h⟩

theorem quiet_trans (a b c : S) (h : Quiet a b) (k : Quiet b c) : Quiet a c :=
  ⟨⟨k.1.1.trans h.1.1, fun f hf => h.1.2.1 f (k.1.2.1 f hf), k.1.2.2.1.trans h.1.2.2.1,
    k.1.2.2.2.trans h.1.2.2.2⟩, k.2.1.trans h.2.1, fun w => k.2.2.1 (h.2.2.1 w),
    fun e x => k.2.2.2 e (h.2.2.2 e x)⟩

theorem recRel_of_enters {cs : Codes} {sh : ReqShape} {s s' : S} (q : Enters s s') :
    RecRel cs sh s s' := fun R => same_frames R (congrArg (·.codes) q.1) q.2.1

theorem grows_of_enters {s s' : S} (q : Enters s s') :
    ChainEnd.GrowsBy (fun s : S => s.st) s s' := by
  show Grows s.st s'.st
  rw [q.1]
  exact Grows.refl _

theorem recRel_of_quiet {cs : Codes} {sh : ReqShape} {s s' : S} (q : Quiet s s') :
    RecRel cs sh s s' := recRel_of_enters q.1

theorem grows_of_quiet {s s' : S} (q : Quiet s s') :
    ChainEnd.GrowsBy (fun s : S => s.st) s s' := grows_of_enters q.1

variable {T Cl : Type}

theorem whole_mono {R R' : T → T → Prop} (h : ∀ s s', R s s' → R' s s') {b : Block T Cl}
    (W : Whole R b) : Whole R' b :=
  ⟨fun s rs gs s' e => h _ _ (W.1 s rs gs s' e), fun c hc n s y e => h _ _ (W.2.1 c hc n s y e),
    fun c hc s s' e => h _ _ (W.2.2 c hc s s' e)⟩

theorem whole_of_steps {R : T → T → Prop} {b : Block T Cl} (h1 : b.Steps R) (h2 : b.RunsStep R)
    (h3 : b.AfterStep R) : Whole R b :=
  ⟨h1, fun c hc n s y e => h2 c hc n s y.1 y.2 e, h3⟩

theorem whole_rec {cs : Codes} {sh : ReqShape} {b : Block S Cl} (W : Whole Quiet b) :
    Whole (RecRel cs sh) b := whole_mono (fun _ _ => recRel_of_quiet) W

theorem whole_grows {b : Block S Cl} (W : Whole Quiet b) :
    Whole (ChainEnd.GrowsBy fun s : S => s.st) b := whole_mono (fun _ _ => grows_of_quiet) W

#print axioms recRel_of_quiet
#print axioms grows_of_quiet
#print axioms whole_mono
#print axioms whole_of_steps
#print axioms whole_rec
#print axioms whole_grows

end Meaning.K2
