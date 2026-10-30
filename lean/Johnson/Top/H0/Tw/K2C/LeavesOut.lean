-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/LeavesOut.lean: THE CODE SWITCH's BLOCKS LEAVE S.out, AND SO THE SEAT OF THE
HEARD REPLY, AS IT WAS.
Block.Leaves (Johnson/Desc/Sound/FoldHeard.lean): where the block's decision goes on, the reading h
of the record is as it was. Here at h := S.out whole, and as a corollary at h := the reply's seat
(fun s => s.out.reply), of each block as it stands in a piece:
  k2LeavesOut           the switch's block at a link, at every numbers of a place
  headOpenedLeavesOut   "H.1.quiet" as a block: it READS the seat and writes nothing into S.out
  placeH2LeavesOut      the whole place «H:2»: the switch andThen "H.1.quiet"
  placeF1LeavesOut      the whole place «F:1»: "F.0.front", the switch, "F.0.quiet"
  …LeavesReply          the same four at the reply's seat
  noRuns                none of the four states a run of claims or a run behind the batching: both
  lists are empty, so nothing else of these blocks can write
NOT HERE: "H.0.front" (headFrontQ), which another lot lays in front of the round «REPLY»:
K2C/Reply.lean's headFrontOut says the like of the function.
Leaves IS A FRAME LAW: a decision that says yes to all and turns nothing, and one that says no to
all, both meet it. It says what these texts do not write, not that a yes means a test.
No Mathlib. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.Reply
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)

theorem k2LeavesOut (p : P2) : (codeSwitchKind p : Block S Unit).Leaves (fun s => s.out) := fun s rs gs s' h =>
    by
  have h : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s' := h
  exact (keeps _ _ _ _ _ _ h).2.1

theorem headOpenedLeavesOut (n : String) (pl : VerifiableInference.Desc.Place) (P : HeadPar) :
    (headOpened n pl P : Block S Unit).Leaves (fun s => s.out) := fun s rs gs s' h => by
  have h : headOpenQ P s = .ok s' := h
  obtain ⟨_, _, _, _, _, _, _, ho⟩ := headOpenLays _ _ _ h
  exact ho

/-- Two blocks in a row that both leave h leave h. (Johnson/Desc/Sound/FoldHeardProofs.lean has the
like as leavesAndThen; said again here in three lines, so that this file stands on the definitions
alone.) -/
theorem andThenLeaves {α : Type} (h : S → α) (name : String) (p q : Block S Unit) (hp : p.Leaves h)
    (hq : q.Leaves h) :
    (p.andThen name q).Leaves h := by
  intro s rs gs s' H
  obtain ⟨t, ht, H⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  rw [hq _ _ _ _ H, hp _ _ _ _ ht]

theorem placeH2LeavesOut (p : P2) (n : String) (P : HeadPar) :
    ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).Leaves (fun s => s.out) :=
  andThenLeaves _ _ _ _ (k2LeavesOut p) (headOpenedLeavesOut n p.place P)

theorem placeF1LeavesOut (p : P2) : (finishPlace p : Block S Unit).Leaves (fun s => s.out) :=
  fun s rs gs s' h => placeF1Out p s rs gs s' h

/-- What leaves S.out leaves the reply's seat. -/
theorem leavesReply_of_out {b : Block S Unit} (h : b.Leaves (fun s => s.out)) : b.Leaves (fun s =>
    s.out.reply) :=
  fun s rs gs s' H => congrArg (·.reply) (h s rs gs s' H)

theorem k2LeavesReply (p : P2) : (codeSwitchKind p : Block S Unit).Leaves (fun s => s.out.reply) :=
    leavesReply_of_out (k2LeavesOut p)
theorem headOpenedLeavesReply (n : String) (pl : VerifiableInference.Desc.Place) (P : HeadPar) :
    (headOpened n pl P : Block S Unit).Leaves (fun s => s.out.reply) :=
        leavesReply_of_out (headOpenedLeavesOut n pl P)
theorem placeH2LeavesReply (p : P2) (n : String) (P : HeadPar) :
    ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).Leaves (fun s => s.out.reply) :=
        leavesReply_of_out (placeH2LeavesOut p n P)
theorem placeF1LeavesReply (p : P2) : (finishPlace p : Block S Unit).Leaves (fun s =>
    s.out.reply) := leavesReply_of_out (placeF1LeavesOut p)

/-- None of the four states a run. -/
theorem noRuns (p : P2) (n : String) (P : HeadPar) :
    (codeSwitchKind p : Block S Unit).claims = [] ∧ (codeSwitchKind p : Block S Unit).after = [] ∧
    (headOpened n p.place P : Block S Unit).claims = [] ∧ (headOpened n p.place P : Block S
        Unit).after = [] ∧
    ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).claims = [] ∧ ((codeSwitchKind p : Block S
                    Unit).andThen n (headOpened n p.place P)).after = [] ∧
    (finishPlace p : Block S Unit).claims = [] ∧ (finishPlace p : Block S Unit).after = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.placeH2LeavesReply
#print axioms VerifiableInference.Desc.First.K2.placeF1LeavesReply
#print axioms VerifiableInference.Desc.First.K2.k2LeavesReply
#print axioms VerifiableInference.Desc.First.K2.noRuns
