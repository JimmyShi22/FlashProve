-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptShared.lean: the closing of a segment (K10): the two ties on the thread's script that the closing's
exchange asks at a message which the shared sending (the kind K1) has sent (the premises hm and hp of `tab_of_shared`,
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieShared.lean), PAID AT THE FIRST CHAIN's SCRIPT OF THE BASE PROVER (`firstScriptAt`,
AtFullSide/K1/FirstScript.lean), in that lemma's own forms, sender by sender.

  **`ties_of_opening`**   the first segment's sending (member number 2 of the first chain): each message n of its job: `OwnMsgs` at
                        the job's text of the message, `OwnPads` at its text of the pad. The first segment's fresh mask is one of
                        these messages
  **`ties_of_later`**     a segment's sending of a later moment (member number `K1.noL l d`, l < 25; d: the digits' or the reads'):
                        the like

The letters at which `tab_of_shared` is met: wit := `witB I A.Z`; J := the member's job; own₀ := (); N and front := the number of
rounds in front of the member; (j, t) := `seatAtMember cF.blocksInOrder b J.P n`; num := `P5J.At.arr A.Z j t`.

By: `tie_k1_first` (AtFullSide/K1/FirstScript.lean), at the two sorts of member (`mem_k1MembersW`, `mem_k1Members`).

Limits. Where a text answers nothing a tie says nothing. That the state's book seats a member of a closing's group at the seat
named is not said here. The hypothesis and the maker's return are premises. The full size and the older hash alone. No
property is claimed.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstScriptAt witB jobTwoAt jobLaterAt jobWAt tie_k1_first LocB k1MembersW mem_k1MembersW
  mem_k1Members seatAtMember msgTxt padTxt SendJob PlaceIn)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIRST SEGMENT's SENDING.** -/
theorem ties_of_opening (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) {n : Nat} (hn : n < (jobTwoAt S A.Z A.G).P.sent.size) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd (0 + roundsTo cF.blocksInOrder 2)
        (P5J.At.arr A.Z (seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n).1
          (seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n).2)
        (0 + roundsTo cF.blocksInOrder 2) (msgTxt 0 (witB I A.Z) (jobTwoAt S A.Z A.G) () n) ∧
      OwnPads (firstScriptAt I S Op A cF) Vd (seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n).1
        (seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n).2 (fun k _ => padTxt 0 (jobTwoAt S A.Z A.G) n k) := by
  have hy : ((2, jobTwoAt S A.Z A.G) : Nat × SendJob (PlaceIn ProofFile.Inst) Unit) ∈
      k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G) :=
    mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inl rfl)))
  obtain ⟨t1, t2⟩ := tie_k1_first h hA Vd hy
  exact ⟨t1 n hn, t2 n hn⟩

/-- **A SEGMENT's SENDING OF A LATER MOMENT.** -/
theorem ties_of_later (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) {l : Nat} (hl : l < 25) (d : Bool) {n : Nat}
    (hn : n < (jobLaterAt S A.Z A.G l d).P.sent.size) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd (0 + roundsTo cF.blocksInOrder (VerifiableInference.Desc.K1.noL l d))
        (P5J.At.arr A.Z (seatAtMember cF.blocksInOrder (VerifiableInference.Desc.K1.noL l d) (jobLaterAt S A.Z A.G l d).P n).1
          (seatAtMember cF.blocksInOrder (VerifiableInference.Desc.K1.noL l d) (jobLaterAt S A.Z A.G l d).P n).2)
        (0 + roundsTo cF.blocksInOrder (VerifiableInference.Desc.K1.noL l d)) (msgTxt 0 (witB I A.Z) (jobLaterAt S A.Z A.G l d) () n) ∧
      OwnPads (firstScriptAt I S Op A cF) Vd (seatAtMember cF.blocksInOrder (VerifiableInference.Desc.K1.noL l d) (jobLaterAt S A.Z A.G l d).P n).1
        (seatAtMember cF.blocksInOrder (VerifiableInference.Desc.K1.noL l d) (jobLaterAt S A.Z A.G l d).P n).2
        (fun k _ => padTxt 0 (jobLaterAt S A.Z A.G l d) n k) := by
  have hy : ((VerifiableInference.Desc.K1.noL l d, jobLaterAt S A.Z A.G l d) : Nat × SendJob (PlaceIn ProofFile.Inst) Unit) ∈
      k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G) :=
    mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inr ⟨l, hl, d, rfl⟩)))
  obtain ⟨t1, t2⟩ := tie_k1_first h hA Vd hy
  exact ⟨t1 n hn, t2 n hn⟩

end AtFullSide.K10

#print axioms AtFullSide.K10.ties_of_opening
#print axioms AtFullSide.K10.ties_of_later
