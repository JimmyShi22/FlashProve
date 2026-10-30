-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/SignsAtSwitches.lean: CONDITIONAL: on the head, the maker's return, hClose and that the
inputs spoken of pass okStart. THE FULL SIZE ALONE.

What is here. THE SIGN THAT THE COLUMN hX AT K4's MEMBERS ASKS OF THE MASK ROW AT THE ELEVEN LATER
GROUPS, AT THE BASE PROVER's SCRIPT `firstScriptAt`: the message is number 2 of the code switch at the
link 2 g, and the row holds K4's coins of group g. hClose, the code switch's closing returns at zeros
at each place, is a named premise: `closing_returns_at_base` (AtFullSide/K4/ClosingAtBase.lean) pays it.
Beneath `closing_at_head` lie 25 closed facts by Lean's kernel, replayed by no independent checker; in
these writers' rides the code switch's seven files on the closing lay compiled and were built in none.

  `own_mask_row_switch`   **the form at `firstScriptAt`, at every Vd that implies the first clause of
      `ReadyInput`, and every N.**

Not shown here. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`: NOT AT THE ONLINE MAKER's RETURN
(`onlineFilling`, E2E/TheHonestProver.lean, is this filling read through `OnlineProverParts.through`): the crossing
is not shown here. An identity of two readings of a run's coins: nothing on how an element is drawn,
on who else reads or spends it, or that it stands at no other entry. That any input is valid. The
laws called (K2's, K5's, part 5's `ownMsgs_switch_first`) are no part of laws.14. Nothing on
soundness, on completeness or on any other property.
No property is claimed.
-/
import AtFullSide.K4.TiesAtSwitches
import AtFullSide.K5.SwitchesLendAtMakerClosed
import AtFullSide.K4.SignsLetters
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkPaid
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskCovers
import Johnson.Desc.ProofFile.Honest.K4.Law.HgAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest ProofFile.Honest.K4 ProofFile.Honest.K4.W
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn OwnMsgs MsgLot ownMsgs_of_covers)
open ProofFile.Honest.K1 (ownMsgs_switch_first readersB closingB cellsB tokB LocB)
open ProofFile.Honest.K2 (switchMsgTxt switchNum switchPlaces)
open ProofFile.Honest.K4.Lot (k4PubG k4MaskLotG)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open AtFullSide.K1 (maskReads_room)
open AtFullSide.K4 (rowLaterW rowLater_at_head later_seam)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL on h, hA, hClose, hVd, h0, hg and hPG. (2b) **THE MASK ROW OF SEGMENT 2 g, 0 < g, HOLDS
K4's COINS OF GROUP g, AT THE BASE PROVER's SCRIPT.** -/
theorem own_mask_row_switch (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (hClose : ∀ p ∈ switchPlaces A.Z A.G,
      ProofFile.Honest.K2.closingOk ProofFile.Honest.K2.freshTable
        ((ProofFile.Honest.K2.segmentsOf A.Z A.G).take p.link) p = true)
    (Vd : LocB FullSizeMatrix → Prop) (hVd : ∀ v, Vd v → h.description.okStart v.x = true) (N : ℕ)
    {g : ℕ} (h0 : 0 < g) (hg : g < 12) {Qp : K4Pub} (hPG : k4PubG A.Z g = some Qp) :
    OwnMsgsForm (theScript h) Vd N (maskNumAt A.Z (2 * g)) 0
      (k4MaskTxt Unit id (matrixInput.weights A.Z) k4Tokens k4LookAt Qp
        (Forest.elems (P5J.At.X A.Z).y.fo)) := by
  obtain ⟨Bs, base₀, Op⟩ := h.head.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.head.laid Op.blank hA
  obtain ⟨p, hp, hl, hnum, ho, hb, hsz, hfs, hr1, hlen⟩ := later_seam h.head Op h0 hg
  have hp' : p ∈ switchPlaces A.Z A.G := by
    rw [eG]
    exact hp
  obtain ⟨-, -, row', idx, hr', -, J, -⟩ := k4Book_at_atPure h.head hA (Rc := IndexCommitterCoins) (X := Unit) id
    (matrixInput.weights A.Z) k4Tokens (k4LookAt Qp) g hg Qp hPG
  obtain rfl : row' = rowLaterW g :=
    Option.some.inj (hr'.symm.trans (rowLater_at_head h.head h0 hg))
  rw [ho, hb] at J
  have OS := ownMsgs_switch_first (I := matrixInput) (S := Sz.ref) (Op := openHonest) h.head hA Vd N
    hp' (Nat.lt_of_succ_lt hsz) hfs
  let Ls : MsgLot A.B (LocB FullSizeMatrix) :=
    ⟨switchNum A.Z p 2, 0 + roundsTo h.firstChain.blocksInOrder (borderNo h.firstChain.blocksInOrder p.place),
      switchMsgTxt 0 (widerRows Sz.ref A.Z A.G) (readersB matrixInput A.Z) (closingB A.Z A.G) p 2⟩
  have C := k4Mask_covers (X := Unit) (cells := id) (weights := matrixInput.weights A.Z)
      (tokens := k4Tokens) (look := k4LookAt) (Vq := Vd) (N := N) hPG J Ls hnum
      (fun k w hd ν hw _ _ _ => by
        obtain ⟨y, hy⟩ := ProofFile.Honest.K2.Law.msgTxt_answers 0 (widerRows Sz.ref A.Z A.G)
          (readersB matrixInput A.Z) A.G.first.layout (ProofFile.Honest.K2.segmentsOf A.Z A.G) p
          (hClose p hp') 2 k w (hd.take (0 + roundsTo h.firstChain.blocksInOrder
            (borderNo h.firstChain.blocksInOrder p.place))) true 0 ν
          (AtFullSide.K5.switch_handed_at_maker_closed h.head hA p hp' k)
          (ProofFile.Honest.K2.Law.serves_at_head h.head.toAtMg Op p hp)
          (ProofFile.Honest.K2.Law.roomy_at_head h.head.toAtMg Op p hp)
          (ProofFile.Honest.K5.publicOk_at_head h.head (atPure_ground h.head hA) (hVd w hw) p hp')
          (ProofFile.Honest.K2.Law.fits_at_head h.head.toAtMg Op p hp)
        exact Option.isSome_iff_exists.2 ⟨y, hy⟩) (L := 8192)
      (fun k w hd ν y' hν hy => ProofFile.Honest.K4.W.switchTxt_look_one 0 _ _ _ p hsz hr1
        (by rw [hlen]; exact hν) k w hd y' hy)
      (Nat.le_succ_of_le (maskReads_room h.head Op hg hPG))
  have OW := ownMsgs_of_covers C OS
  intro k w hd hv hN mask row place y hy
  refine OW k w hd hv hN mask row place y ?_
  show ((k4PubG A.Z g).bind fun Qp => Lot.k4MaskTextG Unit id (matrixInput.weights A.Z) k4Tokens
    k4LookAt Qp (Forest.elems (P5J.At.X A.Z).y.fo) k w (hd.take 0) mask row place) = some y
  rw [hPG]
  exact hy

end AtFullSide.K4.Signs

#print axioms AtFullSide.K4.Signs.own_mask_row_switch
