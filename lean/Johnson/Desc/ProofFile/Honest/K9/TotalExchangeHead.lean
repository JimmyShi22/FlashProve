-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalExchangeHead.lean: FOR THE FRAME's DEBT AT THE ITEM "totalB" (`ExchangeAtS` at
`SaidOk`), AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD: ONE CLOSED FACT ON THE WRITTEN LIST OF THE 25 SEGMENTS'
SORTS. The implication to the debt stands in Honest/K9/TotalExchangeFree.lean (`exchange_totalB_head_seat`, under Sd,
hd, hG), whose proof calls this fact. One statement and its proof; no definition is made; no prover is in this file; no
goal is stated.
  `links_sub`: the written list's sorts are the library's own reading of a segment's number: by decide
Called by Honest/K9/TotalExchangeFree.lean alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 585 files, this one among them: reading copies, all but ours.

-/
import Johnson.Desc.ProofFile.Honest.K9.FrontLaid
import Johnson.Desc.ProofFile.Honest.K9.TotalExchangeSeat
import Johnson.Desc.ProofFile.Honest.Thread.HeadMeans
import Johnson.Desc.ProofFile.Honest.K8.WorthTwoOfOpen
import Johnson.LPFK9R.FactsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

/-- The written list's sorts are the library's own reading of a segment's number. -/
theorem links_sub : ∀ l < 25, P5J.At.links[l]? = some (IM.subAt l) := by decide

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.links_sub
