-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/BatchBuild.lean: HOW A LINK's RunsLaw (BatchFold.lean) IS BUILT OF
THE KINDS' OWN RunLaws ON THEIR BARE RUNS (ClaimShape.lean). General; nothing is evaluated.

What the bridge at the seat (Johnson/AtFull/Shape/BatchAtHead.lean: batch_named) takes is a RunsLaw
of the link's SEATED hearing sub-protocols. What a kind's house has is a RunLaw of a BARE run of its
own sub-protocol. Between them stand: the guard around a seated sub-protocol's runs
(RunGuarded.lean); and the looking up of a run by the member's number and the run's name.

  `RunLaw.idle run`: the law that says nothing (its runG always refuses): for the pairs that an
    order does not name.
  `Slot same bs o`: WHAT IS OWED FOR ONE PAIR o = (member, name): the lot's sub-protocol b' that is
    seated at that member; the bare run that b' states under that name; its RunLaw; and that the
    bare run keeps the seat, and leaves the statement, where it returns.
  `Slot.run`, `Slot.look`: the seated (guarded) run; the looking up.
  `Lawful`: a run with its law. `Slot.lawful`: the seated run with ITS law: the field law (the bare
    run's) carried through the guard: THE BARE RUN's OWN runG AND pre.
  `pick`: the pair's seated run with its law; outside the order a run that refuses, with the idle
    law.
  **`RunsLaw.ofSlots`**: from a slot for each pair of the order to the link's RunsLaw.
  `ofSlots_runG`, `ofSlots_pre`: at a pair of the order its runG and pre ARE the slot's bare law's.
  `ofSlots_still`: at a pair of the order the built run leaves the statement where it returns.

Limits. It builds; it pays nothing: each slot's four fields are its kind's to give. As
ClaimShape.lean's: a RunLaw can be idle in two ways. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.BatchFold
import Johnson.Desc.First.Batch.Shape.RunGuarded
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh)

/-- The law that says nothing. -/
def RunLaw.idle (run : Run) : RunLaw run where
  runG := fun _ _ => .error "no law is laid for this run"
  pre := fun _ _ => True
  carries := fun _ _ _ _ _ _ _ hg => nomatch hg
  returns := fun _ _ _ hg _ => nomatch hg

/-- **What is owed for one pair (member, name).** -/
structure Slot (same : S → S → Bool) (bs : List (Block S Claim)) (o : Nat × String) where
  /-- the lot's sub-protocol that is seated at the member -/
  lot : Block S Claim
  name : String
  place : Place
  seated : bs[o.1]? = some (IM.seatedAs same lot name place)
  /-- the bare run that it states under the name -/
  bare : Run
  states : lot.claims.lookup o.2 = some bare
  law : RunLaw bare
  keeps : ∀ (n : Nat) (s s' : S) (cs : List Claim), bare n s = .ok (cs, s') → same s s' = true
  /-- the bare run leaves the statement where it returns -/
  still : ∀ (n : Nat) (s s' : S) (cs : List Claim), bare n s = .ok (cs, s') → s'.st = s.st

/-- The seated run. -/
def Slot.run {same : S → S → Bool} {bs : List (Block S Claim)} {o : Nat × String}
    (T : Slot same bs o) : Run := guardRun same T.bare

theorem Slot.look {same : S → S → Bool} {bs : List (Block S Claim)} {o : Nat × String}
    (T : Slot same bs o) : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some T.run := by
  rw [T.seated]
  show (IM.seatedAs same T.lot T.name T.place).claims.lookup o.2 = _
  unfold IM.seatedAs
  rw [lookup_guarded]
  show (T.lot.claims.lookup o.2).map (guardRun same) = _
  rw [T.states]
  rfl

/-- A run with its law. -/
structure Lawful where
  run : Run
  law : RunLaw run

/-- The seated run of a slot, with its law: the bare run's own runG and pre. -/
def Slot.lawful {same : S → S → Bool} {bs : List (Block S Claim)} {o : Nat × String}
    (T : Slot same bs o) : Lawful := ⟨T.run, T.law.guarded same T.keeps⟩

/-- The pair's seated run with its law; outside the order: a run that refuses, with the idle law. -/
def pick {same : S → S → Bool} {bs : List (Block S Claim)} {order : List (Nat × String)}
    (T : ∀ o, o ∈ order → Slot same bs o) (o : Nat × String) : Lawful :=
  if h : o ∈ order then (T o h).lawful
  else ⟨fun _ _ => .error "no such run", RunLaw.idle _⟩

/-- **From a slot for each pair of the order to the link's RunsLaw.** -/
def RunsLaw.ofSlots {same : S → S → Bool} {bs : List (Block S Claim)}
    {order : List (Nat × String)} (T : ∀ o, o ∈ order → Slot same bs o) : RunsLaw bs order where
  run := fun o => (pick T o).run
  law := fun o => (pick T o).law
  look := fun o h => by
    unfold pick
    rw [dif_pos h]
    exact (T o h).look

theorem ofSlots_runG {same : S → S → Bool} {bs : List (Block S Claim)}
    {order : List (Nat × String)} (T : ∀ o, o ∈ order → Slot same bs o) (o : Nat × String)
    (h : o ∈ order) : ((RunsLaw.ofSlots T).law o).runG = (T o h).law.runG := by
  show (pick T o).law.runG = _
  unfold pick
  rw [dif_pos h]
  rfl

theorem ofSlots_pre {same : S → S → Bool} {bs : List (Block S Claim)}
    {order : List (Nat × String)} (T : ∀ o, o ∈ order → Slot same bs o) (o : Nat × String)
    (h : o ∈ order) : ((RunsLaw.ofSlots T).law o).pre = (T o h).law.pre := by
  show (pick T o).law.pre = _
  unfold pick
  rw [dif_pos h]
  rfl

/-- At a pair of the order the built run leaves the statement where it returns. -/
theorem ofSlots_still {same : S → S → Bool} {bs : List (Block S Claim)}
    {order : List (Nat × String)} (T : ∀ o, o ∈ order → Slot same bs o) (o : Nat × String)
    (h : o ∈ order) (n : Nat) (s s' : S) (cs : List Claim)
    (hr : (RunsLaw.ofSlots T).run o n s = .ok (cs, s')) : s'.st = s.st := by
  have hr' : (pick T o).run n s = .ok (cs, s') := hr
  unfold pick at hr'
  rw [dif_pos h] at hr'
  have hr'' : guardRun same (T o h).bare n s = .ok (cs, s') := hr'
  exact (T o h).still n s s' cs ((guardRun_iff same (T o h).bare n s (cs, s')).1 hr'').1

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.ofSlots_still
#print axioms VerifiableInference.Desc.K9.Shape.Slot.look
#print axioms VerifiableInference.Desc.K9.Shape.RunsLaw.ofSlots
#print axioms VerifiableInference.Desc.K9.Shape.ofSlots_runG
#print axioms VerifiableInference.Desc.K9.Shape.ofSlots_pre
#print axioms VerifiableInference.Desc.K9.Shape.RunLaw.idle
#print axioms VerifiableInference.Desc.K9.Shape.Slot
#print axioms VerifiableInference.Desc.K9.Shape.Slot.run
#print axioms VerifiableInference.Desc.K9.Shape.Lawful
#print axioms VerifiableInference.Desc.K9.Shape.Slot.lawful
#print axioms VerifiableInference.Desc.K9.Shape.pick
