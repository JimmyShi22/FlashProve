-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ConditionWork.lean (kind K9; beside row K09_condition): THEOREMS: NO
WORK AT K9's DECLARED ROUND: Law/Condition.lean's no_work carried along Law/ConditionAt.lean's two
steps:
  no_work_decl   writtenOf file D = .ok R, R.1 one of the two written lists, k9Decl p ∈ D.1: then
                 p.work = 0.
  no_work_desc   the same at a file's description F: a block of the first chain's flat list has K9's
                 declared round among its rounds.
  all_at_desc    at_desc's three sentences and this one together.
WHAT IT DOES NOT SAY: as in Law/ConditionAt.lean: above all: that writtenOf … F.roundsDeclaredByBlocks returns a
written list is a PREMISE here (a whole list's equation), paid by nobody in this folder: the test
seatPinnedProof's yes at the full size's key gives it: seat_yes (Ok/PlanWritten/Seat.lean).

-/
import Johnson.Desc.First.Batch.Law.ConditionAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Flat OnBytes.Maker
open OnBytes.Params (Rounds)
open Johnson.G Johnson.G.OfPlan
open VerifiableInference.Desc (Block FileDescription)
open _root_.Run (ckP)
open _root_.Iop (Err)

theorem no_work_decl {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) (hR : R.1 = dryProofFull.1 ∨ R.1 = dryProofSmall.1)
    (p : K9.Where) (hp : k9Decl p ∈ D.1) : p.work = 0 := by
  obtain ⟨x, hx, hm⟩ := first_of_written h (k9Decl p) hp
  rw [k9Decl_round] at hx
  rw [← Option.some.inj hx] at hm
  refine no_work p (k9Decl p).stored (List.mem_append.2 ?_)
  rcases hR with e | e
  · exact Or.inl (e ▸ hm)
  · exact Or.inr (e ▸ hm)

theorem no_work_desc {Xi : Type} (F : FileDescription Xi) {file : String} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file F.roundsDeclaredByBlocks = .ok R) (hR : R.1 = dryProofFull.1 ∨ R.1 = dryProofSmall.1)
    (b : Block F.S₁ F.Cl) (hb : b ∈ F.first.blocksInOrder) (p : K9.Where) (hp : k9Decl p ∈ b.rounds) :
    p.work = 0 :=
  no_work_decl h hR p (List.mem_flatMap.2 ⟨b, hb, hp⟩)

/-- **All four at a file's description.** -/
theorem all_at_desc {Xi : Type} (F : FileDescription Xi) {file : String} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file F.roundsDeclaredByBlocks = .ok R) (hR : R.1 = dryProofFull.1 ∨ R.1 = dryProofSmall.1)
    (b : Block F.S₁ F.Cl) (hb : b ∈ F.first.blocksInOrder) (p : K9.Where) (hp : k9Decl p ∈ b.rounds) :
    1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 ∧ p.work = 0 ∧
      Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
        (Err.cap 128 (uLT (ckP .two) [k9Round p])) :=
  have a := at_desc F h hR b hb p hp
  ⟨a.1, a.2.1, no_work_desc F h hR b hb p hp, a.2.2⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.no_work_decl
#print axioms VerifiableInference.Desc.K9L.no_work_desc
#print axioms VerifiableInference.Desc.K9L.all_at_desc
