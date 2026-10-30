-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/TidyStart.lean: THE FIELD "TIDY" OF THE STRUCTURE OF
FACTS ALONG THE FOLD, AT THE PROOF FILE's SEAT. NEW, typed by hand.
  blank_lengths (by the kernel) · startS_tidy   the first state, in both arms of ProofFile.startS
  descPure_reach_tidy   **ProofFile.onlineDescription … = ok F ⊢ F is fileDescBy … c, and at every state that the
  fold over c.blocksInOrder reaches from ProofFile.startS Z the statement is tidy**
LEFT, THREE: hK2 : ∀ p : K2.P2, p.firstTree = 0 → Fits (By TidyStay ·.st) (K2.codeSwitchKind p) (that
the rows which K2's sampleLoop makes are on the message) · every sub-protocol of
c.blocksInOrder passes its own test on the list of rounds · Z.first.codes.lengthsOk = true.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.Fit.TidyTop
import Johnson.IMR.RecRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Means (Tidy)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Fits)
open VerifiableInference.Desc.Ground (By TidyStay)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Pub)

/-- The public part's first state is the literal "nothing has happened yet" (as in
Johnson/Desc/AtSeats/StatementSeat.lean: typed here once more, so that this file hangs on no ledger's law). -/
theorem s0_firstT {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    Z.s₀ = S.firstRecord Z.first.codes Z.first.shape Z.first.layout := by
  have k := pub_start h
  unfold S.startP at k
  split at k
  · exact (Option.some.inj k).symm
  · cases k

theorem blank_lengths : (S.blank).st.codes.lengthsOk = true := by decide +kernel

/-- **The first chain's first state, at every public part of an instance**: its statement is tidy;
its code table is the public part's, or the blank state's. -/
theorem startS_tidy {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hl : Z.first.codes.lengthsOk = true)
    (p : ProofFile.InstPub) :
    Tidy (ProofFile.startS Z p).st ∧ (ProofFile.startS Z p).st.codes.lengthsOk = true := by
  unfold ProofFile.startS
  dsimp only
  split
  · rw [s0_firstT h]
    exact ⟨Tidy.start _, hl⟩
  · exact ⟨Tidy.start _, blank_lengths⟩

/-- **THE FIELD "TIDY", AT THE PROOF FILE's SEAT.** -/
theorem descPure_reach_tidy
    (hK2 : ∀ p : K2.P2, p.firstTree = 0 →
      Fits (By TidyStay fun s : S => s.st) (K2.codeSwitchKind p : Block S Unit))
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ((∀ b ∈ c.blocksInOrder, b.planOk = true) → Z.first.codes.lengthsOk = true →
          ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → Tidy a.2.st) := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := descPure_tidyL hK2 h
  exact ⟨Z, A, B, c, hZ, e, fun hp hl _ _ hr => (reach_tidyL (startS_tidy hZ hl) k hp hr).1⟩

end Meaning.K2
