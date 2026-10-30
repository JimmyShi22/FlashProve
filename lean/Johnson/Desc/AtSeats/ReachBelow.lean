-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/ReachBelow.lean: THE FOLD's FACTS OF Johnson/Desc/AtSeats/FoldFactsPaid.lean AT
THE WRAPPED LIST: by reach_raw (Johnson/Top/H0/Walk/Reach.lean: what is reached by
the wrapped sub-protocols' steps is reached by their own).


  ledgers_paid_below, within_paid_below   the two facts at the wrapped list.

What is not claimed. Nothing on soundness.
-/
import Johnson.Desc.AtSeats.FoldFactsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (LedgersFit WithinFact)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

theorem ledgers_paid_below {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k a →
          LedgersFit a.2.st := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := ledgers_paid h hF
  exact ⟨Z, A, B, c, hZ, e, fun n a hr => k n a (reach_raw hr)⟩

theorem within_paid_below {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k a →
          WithinFact a.2 := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := within_paid h hF
  exact ⟨Z, A, B, c, hZ, e, fun n a hr => k n a (reach_raw hr)⟩

end Meaning.K2
