-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/SignsAtOpening.lean: CONDITIONAL: on the head and the maker's return. THE FULL SIZE
ALONE.

What is here. TWO OF THE SIGNS THAT THE COLUMN hX OF THE FRAME's GATHERING AT THE MEMBERS OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4; `k4_exchange_all_items`,
Honest/K4/Law/W/ExchangeAllItems.lean) ASKS OF THE SCRIPT's MESSAGES, where the message is of the
opening of the shared sending (K1): first at the joined Script `joinQ` at letters, then AT THE BASE
PROVER's SCRIPT `firstScriptAt` (AtFullSide/K1/FirstScript.lean) under the head at the return and
the return alone.

  `k4MaskOwn_at_opening`   at `joinQ`: the mask row of segment 0 holds K4's coins of group 0. After
     the proofs of `k4MaskTie_at_joinQ_k1` (Honest/K4/Law/W/MaskTieAtJoin.lean) and
     `k4MaskTie_at_opening` (AtFullSide/K4/TiesAtOpening.lean), which go on to the tie.
  `k4IndexOwn_at_opening`   at `joinQ`: the index masks' message holds K4's end coin of group g.
     `k4IndexOwn_at_join` (AtFullSide/K4/IndexTieAtJoin.lean) with its hypotheses paid as in
     `k4IndexTie_at_opening`.
  `own_mask_row_opening`, `own_index_mask`   **the two at `firstScriptAt`.**

Not shown here. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`: NOT AT THE ONLINE MAKER's RETURN
(`onlineFilling`, E2E/TheHonestProver.lean, is this filling read through `OnlineProverParts.through`): the
crossing is not here. IDENTITIES OF TWO READINGS OF A RUN's COINS: nothing on how an element
is drawn, on who else reads or spends it, or that it stands at no other entry. That the prover's
side of K1 plays the Script's text. The head and the return are hypotheses. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import AtFullSide.K4.TiesAtOpening
import AtFullSide.K4.SignsLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Others joinQ joinMl joinPl joinTl MsgsAgree MsgLot OwnMsgs)
open ProofFile.Honest.K1 (SendJob PlaceIn msgTxt placeJob firstFold index_two hasCoins_two_at_book
  seatAtMember mem_k1MsgLots msgTxt_answers)
open ProofFile.Honest.K4.Lot (k4IndexRow k4IndexPlace k4IndexTakes k4IndexLotG k4MaskLotG k4PubG)
open AtFullSide.K14 (rawIdxW)
open AtFullSide.K1 (rowZeroW rowZeroW_written openingNos_head maskNum_zero maskReads_below
  opening_look_row_at opening_look_idx_at)
open AtFullSide.K4 (rowOwner_at_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {W₀ Rc Tr X' Xi Xj : Type} {Wa Rca Tra Xa₀ Xa : Type}
  {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (front : ℕ)
  (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xi)
  (own₀ : Xj) (jobs : List (ℕ × SendJob (PlaceIn Xi) Xj))
  (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))

include h

/-- CONDITIONAL on h, hAP, hm, hx and hP. **AT THE JOINED SCRIPT: `OwnMsgs` AT K4's TEXT FOR THE
MASK ROW OF SEGMENT 0**, which is in no list: the lot in the list is that of K1's opening's message
0. -/
theorem k4MaskOwn_at_opening (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O)) (first : ℕ)
    (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub} (hP : k4PubG Zp 0 = some Qp) :
    OwnMsgs (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) (fun _ => True) 0
      (k4MaskLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp 0).n
      (k4MaskLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp 0).fx
      (k4MaskLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp 0).txt := by
  have hE : ∀ (k : Coins A.B) w hd ν y',
      ν < (shapeAt (firstPar A.G.first (gpOf A.Z)) 0).maskRows *
        ((firstPar A.G.first (gpOf A.Z)).codes.mask.getD
          (shapeAt (firstPar A.G.first (gpOf A.Z)) 0).maskCode default).ell →
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 0
        k w hd true 0 ν = some y' →
      (k.look 0 rowZeroW.owner).2.eAt (rowZeroW.base.e + ν) = .ok y' :=
    opening_look_row_at h hAP wit own₀ first Dd rfl
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  have hC := hasCoins_two_at_book h hAP first Dd (Y := Xj) rfl
  rw [eZ, eG] at hx hE hC
  obtain ⟨-, -, row', idx, hr', -, J, -⟩ := k4Book_at_atPure h hAP (Rc := Rc) (X := X') cells
    weights tokens (look Qp) 0 (by omega) Qp hP
  obtain rfl : row' = rowZeroW := Option.some.inj (hr'.symm.trans
    (rowOwner_at_head h (0, rowZeroW) (List.mem_of_mem_head? rowZeroW_written)))
  have hLs := (List.mem_append.2 (Or.inl (mem_k1MsgLots hx
      (List.mem_map.2 ⟨0, List.mem_range.2 (openingNos_head h Op).1, rfl⟩))) :
    (⟨P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) 0).1
      (seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) 0).2, front + roundsTo cF.blocksInOrder 2,
      msgTxt 0 wit (placeJob (firstPar Bs.G₀.first (gpOf Zp)) first (firstFold Bs.G₀.first) Dd)
        own₀ 0⟩ : MsgLot A.B (Local W₀ Rc ProofFile.Inst Tr)) ∈
      joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O)
  exact k4MaskOwn_ofLots (X := X') (cells := cells) (weights := weights) (tokens := tokens)
    (look := look) cF.blocksInOrder front cellsQ tok (joinPl cF.blocksInOrder jobs O) (joinTl wit own₀ jobs O)
    (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O) hLs (hm _ hLs) hP J
    (maskNum_zero h Op) (Vq := fun _ => True) (N := 0)
    (fun k w hd ν _ _ _ _ => by
      obtain ⟨v, hv⟩ := msgTxt_answers hC wit own₀ 0 k w
        (hd.take (front + roundsTo cF.blocksInOrder 2)) true 0 ν
      exact Option.isSome_iff_exists.2 ⟨v, hv⟩)
    hE (maskReads_below h Op hP)

/-- CONDITIONAL on h, hAP, hm, hx, hg and hP. **AT THE JOINED SCRIPT: `OwnMsgs` AT K4's TEXT FOR ITS
ENTRY OF THE INDEX MASKS' MESSAGE**, at K1's opening's message 4, at each group. -/
theorem k4IndexOwn_at_opening (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O)) (first : ℕ)
    (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    {g : ℕ} (hg : g < 12) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : ProofFile.Inst → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) :
    OwnMsgs (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) (fun _ => True) 0
      (k4IndexLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp g).n
      (k4IndexLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp g).fx
      (k4IndexLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp g).txt := by
  have hE : ∀ (c : Coins A.B) w hd y',
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 4
        c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y' :=
    opening_look_idx_at h hAP wit own₀ first Dd rfl hg
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  have hC := hasCoins_two_at_book h hAP first Dd (Y := Xj) rfl
  rw [eZ, eG] at hx hE hC
  have e : (P5J.At.N Zp cF).index = (1, 0) :=
    VerifiableInference.Desc.K1.index_atAll h Op (VerifiableInference.Desc.K1.pin1_atAll h)
  exact (k4IndexOwn_at_join h hAP (X' := X') front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O hm hx
    (openingNos_head h Op).2
    (congrArg (fun s : ℕ × ℕ => P5J.At.arr Zp s.1 s.2) ((index_two h Op).trans e)) hC hg cells
    weights tokens look hP hE).2

end ProofFile.Honest.K4.W

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest ProofFile.Honest.K4 ProofFile.Honest.K4.W
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn OwnMsgs)
open ProofFile.Honest.K1 (joinFit_first mem_k1MembersW mem_k1Members cellsB tokB witB otherSendersAt
  jobTwoAt jobLaterAt jobWAt k1MembersW lotNo lotData)
open ProofFile.Honest.K4.Lot (k4PubG k4IndexLotG)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.HonestTrace (Sz)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- K1's opening's job lies in the list of the Script's jobs. -/
theorem opening_in_jobs (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) :
    ((2, jobTwoAt Sz.ref A.Z A.G) : ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) Unit) ∈
      k1MembersW (jobTwoAt Sz.ref A.Z A.G) (jobLaterAt Sz.ref A.Z A.G)
        (jobWAt openHonest A.Z A.G) :=
  mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inl rfl)))

/-- CONDITIONAL: on h, hA and hPG. (2a) **THE MASK ROW OF SEGMENT 0 HOLDS K4's COINS OF GROUP 0, AT
THE BASE PROVER's SCRIPT**, at every input and every list of challenges. -/
theorem own_mask_row_opening (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (Vd : K1.LocB FullSizeMatrix → Prop) (N : ℕ) {Qp : K4Pub} (hPG : k4PubG A.Z 0 = some Qp) :
    OwnMsgsForm (theScript h) Vd N (maskNumAt A.Z (2 * 0)) 0
      (k4MaskTxt Unit id (matrixInput.weights A.Z) k4Tokens k4LookAt Qp
        (Forest.elems (P5J.At.X A.Z).y.fo)) := by
  have OW := k4MaskOwn_at_opening (X' := Unit) h.head 0 (cellsB matrixInput A.Z) tokB
    (witB matrixInput A.Z) ()
    (k1MembersW (jobTwoAt Sz.ref A.Z A.G) (jobLaterAt Sz.ref A.Z A.G) (jobWAt openHonest A.Z A.G))
    (otherSendersAt matrixInput Sz.ref A h.firstChain) hA (joinFit_first h.head hA).msgs
    (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (lotData Sz.ref A.Z A.G) (opening_in_jobs A) id
    (matrixInput.weights A.Z) k4Tokens k4LookAt hPG
  intro k w hd _ _ mask row place y hy
  refine OW k w hd trivial (Nat.zero_le _) mask row place y ?_
  show ((k4PubG A.Z 0).bind fun Qp => Lot.k4MaskTextG Unit id (matrixInput.weights A.Z) k4Tokens
    k4LookAt Qp (Forest.elems (P5J.At.X A.Z).y.fo) k w (hd.take 0) mask row place) = some y
  rw [hPG]
  exact hy

/-- CONDITIONAL: on h, hA, hg and hPG. (3) **THE INDEX MASKS' MESSAGE HOLDS K4's END COIN OF EACH
GROUP, AT THE BASE PROVER's SCRIPT**, at every input and every list of challenges. -/
theorem own_index_mask (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (Vd : K1.LocB FullSizeMatrix → Prop) (N : ℕ) {g : ℕ} (hg : g < 12) {Qp : K4Pub}
    (hPG : k4PubG A.Z g = some Qp) :
    OwnMsgs (theScript h) Vd N
      (k4IndexLotG (Bk := A.B) (Rc := IndexCommitterCoins) Unit id (matrixInput.weights A.Z) k4Tokens k4LookAt
        A.Z g).n
      (k4IndexLotG (Bk := A.B) (Rc := IndexCommitterCoins) Unit id (matrixInput.weights A.Z) k4Tokens k4LookAt
        A.Z g).fx
      (k4IndexLotG (Bk := A.B) (Rc := IndexCommitterCoins) Unit id (matrixInput.weights A.Z) k4Tokens k4LookAt
        A.Z g).txt := by
  have OW := k4IndexOwn_at_opening (X' := Unit) h.head 0 (cellsB matrixInput A.Z) tokB
    (witB matrixInput A.Z) ()
    (k1MembersW (jobTwoAt Sz.ref A.Z A.G) (jobLaterAt Sz.ref A.Z A.G) (jobWAt openHonest A.Z A.G))
    (otherSendersAt matrixInput Sz.ref A h.firstChain) hA (joinFit_first h.head hA).msgs
    (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (lotData Sz.ref A.Z A.G) (opening_in_jobs A) hg
    id (matrixInput.weights A.Z) k4Tokens k4LookAt hPG
  intro k w hd _ _
  exact OW k w hd trivial (Nat.zero_le _)

end AtFullSide.K4.Signs

#print axioms ProofFile.Honest.K4.W.k4MaskOwn_at_opening
#print axioms ProofFile.Honest.K4.W.k4IndexOwn_at_opening
#print axioms AtFullSide.K4.Signs.own_mask_row_opening
#print axioms AtFullSide.K4.Signs.own_index_mask
