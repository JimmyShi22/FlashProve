-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/SeatLeaves.lean: the proximity test (the kind K12) at the first chain's finish:
WHAT OF THE CHAIN's STATE IT LEAVES AS IT WAS (`Block.Leaves`, Johnson/Desc/Sound/FoldHeard.lean).
Theorems; no code.

  atFinish_leaves   every reading of the chain's state that does not hang on the running record, the
                    book of trees or the count of roots is, behind a yes of the test, as it was in
                    front: by the closure law on a block whose record is born and dies inside it
                    (`leavesInside`) and `leaveFinish`'s one line.
  atFinish_leaves_out · _check · _here · _rowsOwed · _failed · _req   the six other fields of the
                    state, each by name. `out` holds the
                    reply that was heard: so the test turns no word of it.
It holds whatever the parts are: nothing of the kind's block is looked at. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (S)

/-- **What the test at the finish leaves.** -/
theorem atFinish_leaves {α : Type} (h : S → α)
    (hh : ∀ (s : S) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (roots : Nat),
      h { s with st := st, book := book, roots := roots } = h s) (p : P12) :
    (atFinish p).Leaves h :=
  leavesInside S T12 Unit α h enterFinish (proximityTestKind guardedProximityTestParts p) leaveFinish fun s t s' H => by
    rw [(leaveFinish_ok s s' t).1 H]
    exact hh s t.st t.book t.roots

theorem atFinish_leaves_out (p : P12) : (atFinish p).Leaves (·.out) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

theorem atFinish_leaves_check (p : P12) : (atFinish p).Leaves (·.check) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

theorem atFinish_leaves_here (p : P12) : (atFinish p).Leaves (·.here) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

theorem atFinish_leaves_rowsOwed (p : P12) : (atFinish p).Leaves (·.rowsOwed) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

theorem atFinish_leaves_failed (p : P12) : (atFinish p).Leaves (·.failed) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

theorem atFinish_leaves_req (p : P12) : (atFinish p).Leaves (·.req) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

end VerifiableInference.Desc.K12.Seat
