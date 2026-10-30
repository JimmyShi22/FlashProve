-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/KeyBookClear.lean: the shared "sending" (the kind K1) IN THE KEY FILE's PROTOCOL: THE BOOK's
SIDE AT ITS THREE SENDERS ON THE FIRST CHAIN (the index-mask message, the multiplicities, W): at the key
file's book of coins keyBook K (E2E/KeyBook.lean) at the written sizes of the full size (fullPub,
E2E/KeyBookAtWritten.lean), at the written numbers and rides keyParsW
(Johnson/SendSim/Seat/KeyReadsAtWritten.lean) and at the written description's order of places, the wider
condition on the book BookClearAny (Johnson/SendSim/At/BookWide.lean) holds at each of the three. Public
data alone. No definition; three theorems.

  key_fast       ONE EVALUATION IN LEAN's KERNEL: fastOkB (Johnson/SendSim/At/FastBook.lean) accepts at the
                 three senders
  key_fast_no    the test can fail: the book's first entry laid once more behind the others
  key_clear      BookClearAny at the three senders, at every K that fullPub returns

Limits. The written letters alone: that a source's keyPars, its description's order and the book that the
offline prover is run with are these is not shown here. The full size alone. Sufficient, not necessary.
In the side library, because it imports files of it. No property of the protocol is claimed.
-/
import E2E.KeyBookAtWritten
import Johnson.SendSim.Seat.KeyReadsAtWritten
import Johnson.SendSim.At.FastBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile.Honest
open AtPublicFiles.KeyBook (keyBook fullPub atFull KeyPub)
open Johnson.KB4 (WK)
open OnBytes.SendSim.At OnBytes.SendSim.Seat

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The fast test accepts at the key file's three senders of the kind K1.** -/
theorem key_fast :
    atFull (fun K => keyParsW.all fun x =>
      fastOkB x.1 x.2 (keyBook K) (ProofFile.Honest.orderOf WK) ⟨x.1.place, 0⟩) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail: the book's first entry laid once more behind the others. -/
theorem key_fast_no :
    atFull (fun K => keyParsW.all fun x =>
      fastOkB x.1 x.2 { keyBook K with ahead := (keyBook K).ahead ++ (keyBook K).ahead.take 1 }
        (ProofFile.Honest.orderOf WK) ⟨x.1.place, 0⟩) = false := by
  decide +kernel

/-- **BookClearAny at the three senders.** -/
theorem key_clear {K : KeyPub} (hK : fullPub = some K) :
    ∀ x ∈ keyParsW, BookClearAny x.1 x.2 (keyBook K) (ProofFile.Honest.orderOf WK) ⟨x.1.place, 0⟩ := by
  intro x hx
  have h := key_fast
  unfold atFull at h
  rw [hK] at h
  exact clearAny_of_fast (List.all_eq_true.1 h x hx)

end AtFullSide.K1

#print axioms AtFullSide.K1.key_fast
#print axioms AtFullSide.K1.key_fast_no
#print axioms AtFullSide.K1.key_clear
