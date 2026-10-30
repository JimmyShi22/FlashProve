-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptCopies.lean: the closing of a segment (K10): EVERY MESSAGE OF EVERY CODE SWITCH, KEPT COPIES TOO, IS, IN THE WITNESS OF
THE FIRST CHAIN's SCRIPT OF THE BASE PROVER (`firstScriptAt`, AtFullSide/K1/FirstScript.lean), THAT SWITCH's OWN TEXT OFF THE PAD: the tie hm of
`tab_of_switch` (Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieSwitch.lean), in the letters of `msgs_of_switch` (AtFullSide/K10/ScriptSwitch.lean),
without that theorem's premise "the switch is the message's first sender".

  **`msgs_of_switch_all`**  at each place p of the code switch and each message n of its sending, q the plan's seat of that message:
                         `OwnMsgs` at the number `P5J.At.arr A.Z q.j q.t` and `switchMsgOff`, from the rounds in front of the switch on

By. The law itself is the code switch's authors': `msgs_at_lot_data` (AtFullSide/K2/MsgsAtLotData.lean). Its premises, each by a name of this
folder or of its authors: the script is the joined script at their list of jobs, that list is fit and holds the switches' share, and the
sender's reader hands on the input's instance and readers: `script_is_joinQ`, `fit_at_byNo`, `share_in_byNo`, `witB_x`, `witB_R`
(AtFullSide/K10/ScriptCopyScript.lean); the book: `book_at_lot` (ScriptCopyBook.lean); the public test on the data: `publicOk_of_okStart`
(Johnson/HonestTrace/Joint/ReadsLightPaid.lean); the data of a segment in front read no more challenges than the switch has heard:
`heard_at_switches` (AtFullSide/K2/HeardAtSwitches.lean). The two numberings of a seat are joined by `share_seat`
(Johnson/Desc/ProofFile/Honest/K2/Law/TieAtJoin.lean); the member's number and the count of messages by `bridge_no`, `bridge_size`
(ScriptCopyBridges.lean).

Limits. AT THE SIZES `Sz.ref` ALONE, and at inputs whose public instance passes the description's test on the instance (hVd). Where a text
answers nothing the tie says nothing. A tie to a script: what is written where, at each run's coins. The hypothesis and the maker's
return are premises. The full size and the older hash alone. No property is claimed.
-/
import AtFullSide.K2.MsgsAtLotData
import AtFullSide.K2.HeardAtSwitches
import AtFullSide.K10.ScriptCopyScript
import AtFullSide.K10.ScriptCopyBook
import AtFullSide.K10.ScriptCopyBridges
import Johnson.Desc.ProofFile.Honest.K2.Law.TieAtJoin
import Johnson.HonestTrace.Joint.ReadsLightPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstScriptAt readersB cellsB tokB LocB lotNo)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchSent switchSeatIn switchMsgOff lotClosingAt segmentsOf)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **EVERY MESSAGE OF EVERY SWITCH, KEPT COPIES TOO**, off its pad, under the plan's number of its seat. -/
theorem msgs_of_switch_all (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (Vd : LocB W₀ → Prop) (hVd : ∀ w, Vd w → (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).okStart w.x = true)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {n : Nat} (hn : n < (switchSent p.sizes p.others).size)
    {q : P5T.PSeat} (hq : switchSeatIn (P5J.At.pseatsAll A.Z) p.link n = some q) :
    OwnMsgs (firstScriptAt I Sz.ref Op A cF) Vd (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
      (P5J.At.arr A.Z q.j q.t) (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
      (switchMsgOff 0 (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
        (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p n) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hp' : p ∈ switchPlaces A.Z Bs.G₀ := by
    rw [← eG]
    exact hp
  obtain ⟨q', e1, e2, -⟩ := K2.Law.share_seat h O hp' hn
  obtain rfl : q' = q := Option.some.inj (e1.symm.trans hq)
  have M := AtFullSide.K2.msgs_at_lot_data h O (book_at_lot h hA) Sz.ref (lotNo OnBytes.secondHashFunction A.Z)
    (K13.wDataAt Op.pile) (fit_at_byNo h O hA) (share_in_byNo h O hA) (cellsB I A.Z) tokB Vd
    (fun p₁ h₁ w hw => OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart h O (hVd w hw) p₁ h₁)
    (fun p₀ h₀ p₁ h₁ _ w _ s m a hs ha => AtFullSide.K2.heard_at_switches h O Sz.ref p₀ h₀ p₁ h₁ w.x s m a hs ha)
    (fun w _ => witB_x I A.Z w) (fun w _ => witB_R I A.Z w) p hp' n (by rw [bridge_size]; exact hn)
  rw [← script_is_joinQ h O hA, ← e2, bridge_no h p] at M
  rw [eG]
  exact M

end AtFullSide.K10

#print axioms AtFullSide.K10.msgs_of_switch_all
