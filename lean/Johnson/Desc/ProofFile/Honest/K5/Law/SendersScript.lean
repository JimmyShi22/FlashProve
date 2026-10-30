-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersScript.lean: CONDITIONAL: K5's PREMISE ON THE SCRIPT
(K5ScriptQ, ScriptQ.lean in this folder) AT A SCRIPT THAT IS LAID FROM A LIST IN WHICH SOME LOT
COVERS K5's TRIPLE: NO LOT OF K5's NEED LIE IN THE LIST. The list is a letter: nothing here says
whose lots it holds. Where LotsK5.lean in this folder asks that K5's lot lie in the list and agree
with the others, this file asks that SOME lot of the list agree with the others and COVER K5's
triple: answer the same element wherever K5's text answers (Covers, Covers.lean in this folder). IT
PAYS NOTHING OF THE SCRIPT BY ITSELF. Under the library's head on the public input (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean). No filling is named, and no thread. Three statements with their proofs.

What it is for. A laying of the senders' lots of whole messages, with no spender's lot: what a
spender wants of the Script is an equation at its entries (OwnMsgs, Honest/Thread/ScriptLots.lean),
not a membership in the list.

  k5ScriptQ_of_senders   **K5ScriptQ at the laying**: the statement of k5ScriptQ_ofLots
                      (LotsK5.lean) with three premises turned: SM, SF0, SF1: there is a lot Ls in
                      ml that agrees with the other lots of its message and covers maskLot … |
                      fillLot …: these two stay as names of a triple (number, challenges heard,
                      text): they stand in no list
  k5ScriptQ_ofLots_by_senders k5ScriptQ_ofLots is the case where the covering lot is the lot itself
                      (covers_self): the statement of k5ScriptQ_ofLots, to the sign: so two theorems
                      have one statement: this one is kept as the proof that k5ScriptQ_ofLots is a
                      case of the wider
  hQ_of_senders       the joined law's premise on the Script, for all plans and places of group g

The premises. On the list of lots: SM, SF0, SF1; in k5ScriptQ_ofLots_by_senders the elder law's: hM,
aM, F0, F1. On public data: hSz (planesAtRef S = Sz.ref, SizesOffPlanes.lean in this folder), hg,
Pl, hx, hm (with the bound hk in its type), hZ, hS, hL, and the form's reach at the two segments
(R0, R1). On the book: hc; in hQ_of_senders hLent. On the trace: hSm, hqa. On the readers: hrd. Of
bs, front, cq, tok, pl, tl nothing.

How. k5ScriptQ_of_forms (LotsK5.lean) at the laying; each OwnMsgs by ofLots_ownMsgs_of_covers
(Covers.lean); the plan's facts: k5_member (Member.lean); the message with the mask row: masks_head
(ReaderReadsK5.lean) with masksUpTo_yes; the count: coinsFew_of_lent (CoinsFewOf.lean).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. SM, SF0 AND SF1 ARE PREMISES HERE: THIS FILE PAYS NONE. COVERING AT THE MASK
BEARS THE WEIGHT: wherever K5's text answers member number j of the list coins5 Bk k Z, the sender's
text answers the same element, at every run's letter k. That the sender's lot agrees with the other
lots of the list is a premise on that list. No list with such lots is laid in this file or beneath
it. At the earlier hash OnBytes.secondHashFunction, a fixed function. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Covers
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyOfK3
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsK5
import Johnson.Desc.ProofFile.Honest.SharedChainProverSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

section
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg slotsOf script)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot LotsAgree Covers covers_self
  ofLots_ownMsgs_of_covers)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x} {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- SM, SF0, SF1 ARE PAID BY NOBODY. **K5's PREMISE ON THE SCRIPT AT A SCRIPT LAID FROM THE SENDERS'
LOTS.** CONDITIONAL: every premise stands, by kind, in the heads of this file and of LotsK5.lean. -/
theorem k5ScriptQ_of_senders {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
    (cq : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (pl : List (PadLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (tl : ℕ → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr))
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))) {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {g : ℕ} (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {Z5 : Seat5} (hZ : Z5.P.x = a.own)
    (hc : CoinsFew Bk Z5 (slotsOf (script Z5.P.x))) {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {cells : Tr → Cells} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)} {heard₀ heard₁ : MsgAddr → ℕ} (hS : Z5.P.S = a.S)
    (hL : Z5.link = 2 * g + 1) (hrd : ∀ v, (rd v).cells = cells v.trace)
    (hqa : ∀ v, Vd v → ∀ r c,
      (cells v.trace).cell (2 * g) "qa" r c = (cells v.trace).cell (2 * g + 1) "qa" r c)
    (hSm : CellsSmallQ Vd a cells Z5)
    (SM : ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd N Ls (maskLot h x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs)))
    (R0 : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g]? = some As → A ∈ As → offPlanes (2 * g) A.name = true →
      ((cellsVals Sz.ref).size (2 * g) A.name).isSome = true → ∃ Ad : MsgAddr,
      seat₀ Ad = some (2 * g, A.message) ∧ heard₀ Ad ≤ N)
    (SF0 : ∀ (Ad : MsgAddr) (m : ℕ), seat₀ Ad = some (2 * g, m) → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd N Ls (fillLot h S rd seat₀ heard₀ Ad (2 * g) m))
    (R1 : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g + 1]? = some As → A ∈ As → offPlanes (2 * g + 1) A.name = true →
      ((cellsVals Sz.ref).size (2 * g + 1) A.name).isSome = true → ∃ Ad : MsgAddr,
      seat₁ Ad = some (2 * g + 1, A.message) ∧ heard₁ Ad ≤ N)
    (SF1 : ∀ (Ad : MsgAddr) (m : ℕ), seat₁ Ad = some (2 * g + 1, m) → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd N Ls (fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m)) :
    K5ScriptQ h (Script.ofLots bs front cq tok pl tl ml) Vd N x₁ a cells Z5
      (OnBytes.Model.Forest.elems a.fs) := by
  obtain ⟨Lm, hLm, aLm, Cm⟩ := SM
  exact k5ScriptQ_of_forms hSz hg Pl hx hm hZ hc hS hL hrd hqa hSm
    (ofLots_ownMsgs_of_covers bs front cq tok pl tl ml hLm aLm Cm)
    ⟨R0, fun Ad m hAd => by
      obtain ⟨Ls, h1, h2, C⟩ := SF0 Ad m hAd
      exact ofLots_ownMsgs_of_covers bs front cq tok pl tl ml h1 h2 C⟩
    ⟨R1, fun Ad m hAd => by
      obtain ⟨Ls, h1, h2, C⟩ := SF1 Ad m hAd
      exact ofLots_ownMsgs_of_covers bs front cq tok pl tl ml h1 h2 C⟩

/-- **THE ELDER LAW IS THE CASE WHERE THE COVERING LOT IS THE LOT ITSELF**: the statement of
`k5ScriptQ_ofLots` (LotsK5.lean), to the sign, from `k5ScriptQ_of_senders` and `covers_self`. -/
theorem k5ScriptQ_ofLots_by_senders {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
    (cq : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (pl : List (PadLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (tl : ℕ → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr))
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    {S : Sz} (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {Z5 : Seat5} (hZ : Z5.P.x = a.own)
    (hc : CoinsFew Bk Z5 (slotsOf (script Z5.P.x))) {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {cells : Tr → Cells} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)} {heard₀ heard₁ : MsgAddr → ℕ} (hS : Z5.P.S = a.S)
    (hL : Z5.link = 2 * g + 1) (hrd : ∀ v, (rd v).cells = cells v.trace)
    (hqa : ∀ v, Vd v → ∀ r c, (cells v.trace).cell (2 * g) "qa" r c = (cells v.trace).cell
        (2 * g + 1) "qa" r c)
    (hSm : CellsSmallQ Vd a cells Z5)
    (hM : maskLot h x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs) ∈ ml)
    (aM : LotsAgree ml (maskLot h x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs)))
    (R0 : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g]? = some As → A ∈ As → offPlanes (2 * g) A.name = true →
      ((cellsVals Sz.ref).size (2 * g) A.name).isSome = true →
      ∃ Ad : MsgAddr, seat₀ Ad = some (2 * g, A.message) ∧ heard₀ Ad ≤ N)
    (F0 : ∀ (Ad : MsgAddr) (m : ℕ), seat₀ Ad = some (2 * g, m) →
      fillLot h S rd seat₀ heard₀ Ad (2 * g) m ∈ ml ∧
        LotsAgree ml (fillLot h S rd seat₀ heard₀ Ad (2 * g) m))
    (R1 : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g + 1]? = some As → A ∈ As → offPlanes (2 * g + 1) A.name = true →
      ((cellsVals Sz.ref).size (2 * g + 1) A.name).isSome = true →
      ∃ Ad : MsgAddr, seat₁ Ad = some (2 * g + 1, A.message) ∧ heard₁ Ad ≤ N)
    (F1 : ∀ (Ad : MsgAddr) (m : ℕ), seat₁ Ad = some (2 * g + 1, m) →
      fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m ∈ ml ∧
        LotsAgree ml (fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m)) :
    K5ScriptQ h (Script.ofLots bs front cq tok pl tl ml) Vd N x₁ a cells Z5
      (OnBytes.Model.Forest.elems a.fs) :=
  k5ScriptQ_of_senders bs front cq tok pl tl ml hSz hg Pl hx hm hZ hc hS hL hrd hqa hSm
    ⟨_, hM, aM, covers_self Vd N _⟩ R0
    (fun Ad m hAd => ⟨_, (F0 Ad m hAd).1, (F0 Ad m hAd).2, covers_self Vd N _⟩) R1
    (fun Ad m hAd => ⟨_, (F1 Ad m hAd).1, (F1 Ad m hAd).2, covers_self Vd N _⟩)

end

section
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg masksUpTo_yes)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot LotsAgree Covers)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ : Type} {S : OnBytes.HonestTrace.Sz} {Bk : ProverCoinCounts}
  (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)

/-- SM, SF0, SF1 ARE PAID BY NOBODY. **THE JOINED LAW's PREMISE ON THE SCRIPT, AT A SCRIPT LAID FROM
THE SENDERS' LOTS.** CONDITIONAL: every premise stands, by name, in the file's head. -/
theorem hQ_of_senders {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {g : ℕ} (hg : g < 12) (G : Ground) {Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop}
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp G cF g a))
    {rd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)}
    {heard₀ heard₁ : MsgAddr → ℕ} (hrd : ∀ v, (rd v).cells = id v.trace)
    (hqa : ∀ v, Vd v → ∀ r c,
      (id v.trace : Cells).cell (2 * g) "qa" r c = (id v.trace : Cells).cell (2 * g + 1) "qa" r c)
    (hSm : ∀ a, (P5J.At.X Zp).A[g]? = some a → CellsSmallQ Vd a id (seatOf keyOfK3 Zp G cF g a))
    (SM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (maskLot h x₁ kM hk
                 (seatOf keyOfK3 Zp G cF g a) (OnBytes.Model.Forest.elems a.fs)))
    (R0 : ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g]? = some As → Ar ∈ As → offPlanes (2 * g) Ar.name = true →
      ((cellsVals Sz.ref).size (2 * g) Ar.name).isSome = true → ∃ Ad : MsgAddr,
      seat₀ Ad = some (2 * g, Ar.message) ∧ heard₀ Ad ≤ roundsTo cF.blocksInOrder (borderOf g))
    (SF0 : ∀ (Ad : MsgAddr) (m : ℕ), seat₀ Ad = some (2 * g, m) → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S rd seat₀ heard₀ Ad (2 * g) m))
    (R1 : ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g + 1]? = some As → Ar ∈ As → offPlanes (2 * g + 1) Ar.name = true →
      ((cellsVals Sz.ref).size (2 * g + 1) Ar.name).isSome = true → ∃ Ad : MsgAddr,
      seat₁ Ad = some (2 * g + 1, Ar.message) ∧ heard₁ Ad ≤ roundsTo cF.blocksInOrder (borderOf g))
    (SF1 : ∀ (Ad : MsgAddr) (m : ℕ), seat₁ Ad = some (2 * g + 1, m) → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m)) :
    ∀ a x₁, (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h (Script.ofLots bs front cq tok pl tl ml) Vd (roundsTo cF.blocksInOrder
        (borderOf g)) x₁ a id (seatOf keyOfK3 Zp G cF g a) (OnBytes.Model.Forest.elems a.fs) := by
  intro a x₁ ha hx
  obtain ⟨blk, a', -, Pl', -⟩ := k5_member h hg
  have ea : a' = a := Option.some.inj (Pl'.plan.symm.trans ha)
  have Pl : PlanAt Zp g a := ea ▸ Pl'
  obtain ⟨-, kM, hk, hm, -, -⟩ := masksUpTo_yes (masks_head h hg ha hx).1 h.𝔇.l3.rad
  exact k5ScriptQ_of_senders bs front cq tok pl tl ml hSz hg Pl hx hm rfl
    (coinsFew_of_lent (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (cells := id)
      (hLent a ha))
    rfl rfl hrd hqa (hSm a ha) (SM a x₁ kM hk ha hx hm) R0 SF0 R1 SF1

end

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5ScriptQ_of_senders
#print axioms ProofFile.Honest.K5.k5ScriptQ_ofLots_by_senders
#print axioms ProofFile.Honest.K5.hQ_of_senders
