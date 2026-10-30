-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LaterSeated.lean: THE KIND K1's DIGITS' MEMBER ALONE (a
segment's later moment by itself, K1.laterAt, Johnson/Desc/K1/Places.lean), AS A CHAIN SEATS IT: its
decision returns, under four premises. One statement: calls.

  later_seated_yes: the seated member's decision returns, at a seat whose place is not of the kind
    K7, at any groups of columns, on rounds that fit the kind's rounds, at a state without a mark at
    whose shape the commitment's step returns. By two_of_fit (Johnson/RunOne/KeyMsgOne.lean),
    later_yes_of_shape (Johnson/Prover/Send/LaterYes.lean), k1_commit_keeps
    (Johnson/Desc/ProofFile/Honest/K1/Law/Keeps.lean: the mark and the reply are as they were),
    same_of_reply (Johnson/Desc/Reads/GuardOff.lean) and IM.yes_alone (Johnson/IMR/SeatForm.lean).

Limits. ONE OF THE KIND's FOUR SORTS OF MEMBER: nothing on the reads' member (a step without a round
is joined behind the commitment), on the first segment's opening or on W's sending. THE WEIGHT LIES
IN THE PREMISE ON THE SHAPE (commitG, Johnson/Desc/First/Shape/Commit.lean): that the commitment's
step on the shape returns at any state is shown nowhere. The decision, not the step. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Send.LaterYes
import Johnson.Desc.ProofFile.Honest.K1.Law.Keeps
import Johnson.Desc.Reads.GuardOff
import Johnson.RunOne.KeyMsgOne
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place KindName roundsFit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (commitG chainSh ChainSh)

variable {q : Params.First} {gp : _root_.Desc.Plain.GPar} {link piece moment : Nat}
  {arrays : Option (List Nat)} {b : Block S ProofFile.Cl} {name : String} {a : Place}

/-- **The seated member's decision returns**, at a seat whose place is not of the kind K7, on rounds
that fit, at a state without a mark at whose shape the commitment's step returns. -/
theorem later_seated_yes
    (hla : IM.LaidAlone ProofFile.sameReply b
      (VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays : Block S Unit).retype
      name a)
    (hk : a.kind ≠ KindName.K7) {s : S} {R : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {t : ChainSh} (h0 : s.failed = none)
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds
      (VerifiableInference.Desc.K1.parLater q gp link piece moment)) R = true)
    (hg : commitG (VerifiableInference.Desc.K1.parLater q gp link piece moment) link moment arrays
      (chainSh s) = some t) : ∃ s', b.decide s R gs = .ok s' := by
  obtain ⟨r₁, r₂, rfl⟩ := Johnson.RunOne.KeyMsg.two_of_fit _ _ R hfit
  obtain ⟨m, hm, -⟩ := Johnson.Prover.Send.later_yes_of_shape (gs := gs) hfit hg
  have k := (k1_commit_keeps hm).1
  exact ⟨m, (IM.yes_alone hla hk s m _ gs).2 ⟨hm, k.1.trans h0,
    VerifiableInference.Reads.Pass.same_of_reply (congrArg (·.reply) k.2.1)⟩⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.later_seated_yes
