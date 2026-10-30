-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/AcceptedAtAnyK3.lean: kind K13, the members' batching: THE KIND's
SUB-PROTOCOL AT NUMBER 355 OF THE FIRST CHAIN IS ACCEPTED WHERE THE SENDER FOUND AT ITS PLACE IS THE
KIND's HALF AT THE WRITTEN FILLER OF THE PILE (`pileAnyK3`, PileOfAnySize.lean of this folder); AND
THAT SENDER IS FOUND THERE IN THE PROVER WHICH THE MAKER RETURNS AT ANY FILLING THAT HOLDS THE
KIND's LOT AND NO OTHER LOT WITH A SIDE OF THE KIND. Statements with their proofs: calls; no
definition. THE FULL SIZE ALONE, AT THE FORMAT's SECOND HASH FUNCTION ALONE: all under the library's
one
hypothesis h (`P5J.AtMgA`).

The premises of the statements beneath. `k13_accepted_at_head` (GuardsAtHead.lean) gives
`AcceptedS` at 355 from four premises: hb (the thread's clause on the reply has begun) · hH (which
sender is found) · hW (the filler's rows are tied to the state's pile) · hfill (a test at the
filler's rows).
`k13_accepted_at_head_text` (ClaimsText.lean) exchanges the last two for two ties along the
verifier's fold, at the filler over the claims' written text. Here that filler is the written
one (`pileOfAnySize_at`, PileOfAnySizeAt.lean), and both ties are proved by theorems of the kinds
in front: `htie_head` (Honest/K3/Law/Thread/LayersTieHead.lean) · `headClaimIsOfKeysBare`
(Honest/K11/ThreeTiesBare.lean) at `head_keys_tie` (Honest/K3/Law/Thread/HeadCallsTie.lean).
Main names:
  `k13_accepted_at_anyK3`: **`AcceptedS` at 355, at every Said and every fall**, from h, a base
    (hB), hb and hH at `pileAnyK3`.
  `k13_half_of_lots`: **hH at the maker's return**: under h and hA (`onlineProverFromPublicFiles` returns A at a filling
    P): where a lot L of P has the halves of `k13Lot weights pile`, and every lot of P has either no
    side at a place of the kind K13 or L's halves: the sender found in A.H.first at the place of
    number 355 is `proverSideOfClaimCombination weights (pile Zp A.G) h.𝔇.P13`.
  `k13_accepted_of_lots`: **the two joined**: `AcceptedS` at 355 at the thread over A.H, from h, hA,
    the two premises on P's lots at `pileAnyK3`, and hb. P, the index's type, the type of the stored
    randomness and the index's reader are variables.

What `AcceptedS` says (Honest/Thread/PaysS.lean): IF the thread and Said stand in front of the
member, the challenges fit, no part stops, `fall` is silent and the prover has moved, THEN the
member's own step returns. Where the thread stands nowhere it speaks of nothing. HOW FAR THAT
REACHES AT THIS MEMBER: its step tests the shape of the verifier's state and the sizes of what was
sent (`Psc.run`, OnBytes/Iop/Psc.lean; `K13Guards`, Debts.lean of this folder): no sent VALUE is
tested here; the step lays a claim, and whether that claim is true of what was sent is the matter of
`ExchangeS` at this border and of the members behind.

What is not claimed. That h holds at any public files; that the maker returns. The other four
statements at this border (that the prover plays; what stands behind; the items owed; the items that
ride past). Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PileIsAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySizeAt
import Johnson.Desc.ProofFile.Honest.K13.Found355
import Johnson.Desc.ProofFile.Honest.FirstFindKind
import Johnson.Desc.ProofFile.Honest.AtBaseGround
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open ProofFile.Honest.K11 (headFourOfK6 headClaimIsOfKeysBare)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 headKeysOfK3 head_keys_tie htie_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}

/-- **K13's SUB-PROTOCOL AT 355 IS ACCEPTED, AT THE WRITTEN FILLER OF THE PILE.** Bs: the maker's
base: under h there is one (`base_at_head`). -/
theorem k13_accepted_at_anyK3 (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} (hb : b₀ ≤ 355) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights (pileAnyK3 Zp Bs.G₀) h.𝔇.P13))
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 := by
  have e : pileAnyK3 Zp Bs.G₀ = _ := pileOfAnySize_at h q0Idle Bs
  rw [e] at hH
  exact k13_accepted_at_head_text h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb
    (lookOfK3 Zp cF) _ _ hH (htie_head h)
    (headClaimIsOfKeysBare (headKeysOfK3 cF) Z D r Zp Np cF x Bs 24
      (fun _ => headArmOf (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp Bs) h hB
      (fun _ _ => rfl) (head_keys_tie h Bs.G₀))
    fall

variable {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)

include hA in
/-- **WHICH SENDER IS FOUND AT THE PLACE OF NUMBER 355, IN THE PROVER THAT THE MAKER RETURNS.** L: a
lot of the filling with the halves of the kind's lot. ho: no other lot lays a side at a place of the
kind. -/
theorem k13_half_of_lots (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst)
    {L : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X} (hL : L ∈ P.lots)
    (hLh : L.halves A.Z A.G = (k13Lot weights pile).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots,
      (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K13) ∨
        M.halves A.Z A.G = L.halves A.Z A.G) :
    ∀ blk, cF.blocksInOrder[355]? = some blk →
      (A.H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights (pile Zp A.G) h.𝔇.P13) := by
  intro blk hblk
  obtain ⟨hZ, -⟩ := atPure_at_laid h.laid hA
  have hk : blk.place.kind = KindName.K13 := by rw [m3_member_place h hblk]
  refine atPure_first_find_kind hA hL (fun M hM => ?_) ?_
  · rw [hk]
    exact ho M hM
  · rw [hLh, hZ]
    exact k13_found_355 h weights pile A.G blk hblk

include hA in
/-- **K13's SUB-PROTOCOL AT 355 IS ACCEPTED AT THE THREAD OVER THE PROVER THAT THE MAKER RETURNS**,
at every filling that holds the kind's lot at the written filler of the pile and no other lot with a
side of the kind. -/
theorem k13_accepted_of_lots (weights : W₀ → Weights)
    {L : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X} (hL : L ∈ P.lots)
    (hLh : L.halves A.Z A.G = (k13Lot weights pileAnyK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots,
      (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K13) ∨
        M.halves A.Z A.G = L.halves A.Z A.G)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (hb : b₀ ≤ 355)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 := by
  obtain ⟨Bs, hB⟩ := base_at_head h
  obtain ⟨hZ, -⟩ := atPure_at_laid h.laid hA
  have hG : Bs.G₀ = A.G := base_ground_atPure hB hA hZ
  refine k13_accepted_at_anyK3 h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (weights := weights) hb Bs hB ?_ fall
  rw [hG]
  exact k13_half_of_lots h hA weights pileAnyK3 hL hLh ho

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_accepted_at_anyK3
#print axioms ProofFile.Honest.K13.k13_half_of_lots
#print axioms ProofFile.Honest.K13.k13_accepted_of_lots
