-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Over Block.lean, State.lean and the seats that go with them (Stored/HeadSeatAt.lean,
Stored/ReplySeatAt.lean).

Johnson/Desc/Kinds/Law/CoveredSeat.lean: AT THE FIRST CHAIN's RECORD THE HEAD's READS' ENTRIES LIE
ON ONE ARRAY: the array number iU3
(the vector of reads called U3), AND ON NO OTHER.
`seat_entry`: wherever the seat of
Johnson/Stored/HeadSeatAt.lean lays the reads' places, each `entry r i` of the head's five reads is
the one-entry form Aff.ent iU3 (pos / cols) (pos % cols), with pos = a base that hangs on r alone,
plus i. With Covered.lean: every entry that the head's eleven forms name has the array number iU3.
OVER HeadSeatAt.lean. WHAT IT DOES NOT SAY: what the bases are.
-/
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Aff)
open VerifiableInference.Desc.First (S)

theorem seat_entry (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S)
    (x : FinalNorm.Reads × Reads) (hx : (seatAt h iU3).reads s = some x) :
    ∃ (cols : Nat) (base : Read → Nat), ∀ r i,
      x.2.entry r i = Aff.ent iU3 ((base r + i) / cols) ((base r + i) % cols) := by
  unfold seatAt at hx
  dsimp only at hx
  split at hx
  · rename_i o F _ _
    cases ht : o.t with
    | none => rw [ht] at hx; simp at hx
    | some tt =>
      rw [ht] at hx
      cases htr : F.trees[iU3]? with
      | none => rw [htr] at hx; simp at hx
      | some tr =>
      rw [htr] at hx
      simp only [Option.bind_some] at hx
      split at hx
      · cases hx
      simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨tr.K, fun r =>
        ((tt.tab.find? fun e => e.1 == (match r with
          | .wideAtKeys => "hf@Z" | .wideAtCosts => "hf@phiZ" | .actAtLogits => "hd@r_H"
          | .rowAtCosts => "hr@phiC" | .rowCount => "hr@rhoC")).map (·.2.1)).getD 0, ?_⟩
      intro r i
      rfl
  · cases hx

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.seat_entry
