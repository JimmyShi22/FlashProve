-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeatIs.lean: WHAT onlineDescription RETURNS IS fieldF AT seatN Z N: so that the
ledger's
end in the field shared_joint_count's own text (ledger_whole_fills_field,
Johnson/Desc/K14/Law/LedgerByMakeTop.lean),
which is stated at fieldF … (the proof file's description, the IOP as written in Lean, by the
maker's own
text at any seat of the shared chain whose state is St and whose chain is the seated chain), speaks
of
the description that the verifier runs.
  fieldF_seatN     ProofFile.fileDescBy o mk Z (seatN Z N) B' get start c IS fieldF … at the seat's own
  fields,
                   ch := Z.p.chains · Q := p14Of Z.p.chains (beforePointOf N) · tests := tests N:
                   rfl
  fieldF_of_pure   ProofFile.onlineDescription o pol lay KL = .ok F ⊢ F is that fieldF (shared_seat_of_pure,
                   Johnson/Desc/K14/Law/K14Sits.lean, called)
What is not claimed. Anything on another road's description than onlineDescription's. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerByMakeTop
import Johnson.Desc.K14.Law.K14Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K12.Seat (tests last)

theorem fieldF_seatN {σ₁ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (B' : ProofFile.SecondSeat) (getS : σ₁ → VerifiableInference.Desc.First.S)
    (startS : ProofFile.InstPub → σ₁) (c : Chain σ₁ ProofFile.Cl) :
    ProofFile.fileDescBy o mk Z (seatN Z N) B' getS startS c =
      fieldF o mk Z (seatN Z N).lot (seatN Z N).start (seatN Z N).ended (seatN Z N).okInst
        (seatN Z N).fileOk (seatN Z N).standIns B' getS startS c Z.p.chains
        (p14Of Z.p.chains (beforePointOf N)) (tests N) := rfl

theorem fieldF_of_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
      (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = fieldF o ProofFile.pureRoad.links Z (seatN Z N).lot (seatN Z N).start (seatN Z N).ended
        (seatN Z N).okInst (seatN Z N).fileOk (seatN Z N).standIns B' (fun s => s) (ProofFile.startS Z) c
        Z.p.chains (p14Of Z.p.chains (beforePointOf N)) (tests N) := by
  obtain ⟨Z, N, B', c, hZ, hN, hF⟩ := shared_seat_of_pure h
  exact ⟨Z, N, B', c, hZ, hN, hF.trans (fieldF_seatN _ _ Z N B' _ _ c)⟩

end Desc.K14.Law
