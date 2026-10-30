-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No member of K3Lot.hear Z is shown to accept at any state of the verifier.
Johnson/Desc/First/Look/K3LotLeaves.lean: The kind "lookup" (K3): EVERY SUB-PROTOCOL THAT THE KIND's
LOT MAKES (K3Lot.hear Z, Johnson/Desc/ProofFile/Lot/K3.lean) LEAVES, WHERE ITS DECISION ACCEPTS, THE
CHAIN's STATEMENT AND ALL THAT WAS PUT OUT AS THEY WERE. A statement and its proof. A tie of texts:
no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: the members of K3Lot.hear Z: the values of K3.theStated at the lot's addresses.
Used by RoomKeepK3.lean (Johnson/P1L20R/).
LETTERS: Z, b', s, s', rs, gs free.
Compiled with the whole library.

Main names:
  k3_lot_same: s'.st = s.st and s'.out = s.out. By stated_reads
    (Johnson/Desc/First/Look/K3DigitsSig.lean) at the two readers (·.st) and (·.out), which do not
    turn where the state's fields "here" and "failed" are laid.

Limits. From an accept of the decision alone. Nothing on the runs of claims.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.Desc.First.Look.K3DigitsSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- **An accepting decision of a sub-protocol of the kind's lot leaves the statement and all that
was put out.** -/
theorem k3_lot_same (Z : ProofFile.Pub) {b' : Desc.Block Desc.First.S Desc.Claim}
    (hm : b' ∈ K3Lot.hear Z) {s s' : Desc.First.S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : b'.decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out := by
  unfold K3Lot.hear at hm
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hm
  exact ⟨stated_reads (fun t : Desc.First.S => t.st) (fun _ _ _ => rfl) _ _ _ _ _ _ b' hx s s' rs
      gs h,
    stated_reads (fun t : Desc.First.S => t.out) (fun _ _ _ => rfl) _ _ _ _ _ _ b' hx s s' rs gs h⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lot_same
