-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotsK5.lean: K5's PREMISE ON THE SCRIPT (`K5ScriptQ`,
ScriptQ.lean in this folder) AT A SCRIPT THAT IS LAID FROM LOTS (`Script.ofLots`,
Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean). IT PAYS NOTHING OF THE SCRIPT BY ITSELF: IT
EXCHANGES ONE PREMISE ON THE SCRIPT FOR PREMISES ON THE LIST OF LOTS, ON PUBLIC DATA, ON THE BOOK,
ON THE TRACE AND ON THE READERS. CONDITIONAL: under the hypothesis h, the library's head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), and on all of these. GENERAL IN THE SIZES S of
the filling, under one public premise, hSz: `planesAtRef S = Sz.ref` (SizesOffPlanes.lean in this
folder). Two definitions; three theorems.

Main names:
  `k5ScriptQ_ofLots`: **THE TOP**: `K5ScriptQ` at `Script.ofLots bs front cq tok pl tl ml`.
  WHAT IT ASKS. On the list of lots: K5's lots are among them (hM; F0, F1, first halves), and each
    agrees with the other lots of its message wherever both answer (aM; F0, F1, second halves). On
    public data: hSz, hg, Pl, hx, hm, hZ, hS, hL, and the form's reach at the two segments (R0, R1).
    On the book: hc. On the trace: hSm, hqa. On the readers: hrd. Of bs, front, cq, tok, pl, tl
    nothing.
  `maskLot`, `fillLot`: K5's LOTS, as terms of the frame's `MsgLot`: its own slots of the mask row
    (`maskTxt`, LotsMask.lean); the filling's entries of one message off the planes (`fillTxt`,
    LaysCells.lean), for an address that is seated at that message.
  `LotsAgree ml L` IS THE FRAME's (ScriptLots.lean): the premise of its `ofLots_ownMsgs`.
  `k5ScriptQ_of_forms`: the same end at a letter Q, from `OwnMsgs` at the mask's text and
    `LaysCells` at the two segments. `laysCells_ofLots`: `LaysCells` at the laying.

How. `k5ScriptQ_of_raw` (EMaskAtHead.lean), `eCells_head` (CellsQAtHead.lean),
`eMaskRaw_iff_ownMsgs` (LotsMask.lean), `eSyms_of_laysCells` (LaysCells.lean), all in this folder;
the frame's `ofLots_ownMsgs`.

Limits. `maskLot` IS A SPENDER's LOT, NOT THE SENDER's: at a list that holds it and no other lot of
that message's number the laying lays 0 at every other entry of that mask row: a Script that, under
this law's other premises, meets `K5ScriptQ` and is nobody's honest prover. The law is at letters:
true there too. NO LAW ON COINS MAY EVER STAND AT SUCH A LIST. The frame plans to lay no spender's
lot: see `k5ScriptQ_of_senders` (SendersScript.lean in this folder), of which this law is the case
where the covering lot is the lot itself. Whether the slots of two groups overlap was not looked at.
"AGREE" CARRIES THE WEIGHT, AND IS NOT PAID HERE: not between two of the filling's lots, not between
the mask's lot and the filling's (the flag parts them), not against the lot of whoever sends the
whole mask row, not against another kind's slots (the ledger's numbers: the frame's matter). For the
first two, and for the mask's lots of two groups under one public premise, see AgreeK5.lean in this
folder, which stands over this file. No lot's text is proved to be what an honest prover sends. At a
Vd that holds of no input the top says nothing: where the law is spent Vd is meant to be the
thread's own test on inputs. F0 and F1 ask a lot for each seated address of the segment, also where
the text never answers: such a lot agrees with all and costs nothing. cq, the laid Script's cells,
is a letter: nothing here ties it to the letter cells: that is the frame's clause on cells. The
premise of attention's joined law stands at one seat, one number of challenges and all plans: the
step from the top to it is not taken here. The file stands over the frame's ScriptLots.lean, which
lies in no seal. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above
the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysCells
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsMask
import Johnson.Desc.ProofFile.Honest.K5.Law.EMaskAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.CellsQAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg slotsOf script)
open ProofFile.Honest.FirstThread (Script OwnMsgs MsgLot PadLot TreeLot)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)
open ProofFile.Honest.FirstThread (LotsAgree ofLots_ownMsgs)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **K5's lot at its own slots of the mask row.** -/
noncomputable def maskLot (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) (Z5 : Seat5) (ν₅ : ℕ) :
    MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr) :=
  ⟨maskNo5 h x₁ kM hk, 0, maskTxt Bk Z5 ν₅⟩

/-- **The filling's lot at message m of segment l, off the planes**, for an address Ad that is
seated at (l, m). -/
noncomputable def fillLot (S : Sz) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (seat : MsgAddr →
          Option (ℕ × ℕ))
    (heard : MsgAddr → ℕ) (Ad : MsgAddr) (l m : ℕ) : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr) :=
  ⟨P5J.At.num Zp l m, heard Ad,
    fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd seat heard Ad l m⟩

variable {h Q}

/-- **K5's PREMISE ON THE SCRIPT FROM THE TWO FORMS**, at a letter Q. CONDITIONAL: every premise
stands, by kind, in the file's head. -/
theorem k5ScriptQ_of_forms {S : Sz} (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12)
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
    (M : OwnMsgs Q Vd N (maskNo5 h x₁ kM hk) 0 (maskTxt Bk Z5 (OnBytes.Model.Forest.elems a.fs)))
    (L0 : LaysCells h Q S Vd N rd seat₀ heard₀ (2 * g))
    (L1 : LaysCells h Q S Vd N rd seat₁ heard₁ (2 * g + 1)) :
    K5ScriptQ h Q Vd N x₁ a cells Z5 (OnBytes.Model.Forest.elems a.fs) :=
  k5ScriptQ_of_raw h hg Pl hx hm hZ hc (eMaskRaw_iff_ownMsgs.2 M)
    (eCells_head hg Pl.plan hx hSm (eSyms_of_laysCells hSz hg Pl.plan hx hS hL hrd hqa L0 L1))

/-- **The form at the laying.** CONDITIONAL: R: the form's reach; F: the lot of each address that is
seated in segment l is among the lots and agrees with the others of its message. -/
theorem laysCells_ofLots {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
    (cq : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (pl : List (PadLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (tl : ℕ → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr))
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (S : Sz) {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : MsgAddr → Option (ℕ × ℕ)}
    {heard : MsgAddr → ℕ} {l : ℕ}
    (R : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[l]? = some As → A ∈ As → offPlanes l A.name = true →
      ((cellsVals Sz.ref).size l A.name).isSome = true →
      ∃ Ad : MsgAddr, seat Ad = some (l, A.message) ∧ heard Ad ≤ N)
    (F : ∀ (Ad : MsgAddr) (m : ℕ), seat Ad = some (l, m) →
      fillLot h S rd seat heard Ad l m ∈ ml ∧ LotsAgree ml (fillLot h S rd seat heard Ad l m)) :
    LaysCells h (Script.ofLots bs front cq tok pl tl ml) S Vd N rd seat heard l :=
  ⟨R, fun Ad m hAd =>
    ofLots_ownMsgs bs front cq tok pl tl ml (F Ad m hAd).1 (F Ad m hAd).2 Vd N⟩

/-- **K5's PREMISE ON THE SCRIPT AT A SCRIPT LAID FROM LOTS.** CONDITIONAL: every premise stands, by
kind, in the file's head. IT MOVES THE DEBT: none of these is proved here. -/
theorem k5ScriptQ_ofLots {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
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
  k5ScriptQ_of_forms hSz hg Pl hx hm hZ hc hS hL hrd hqa hSm
    (ofLots_ownMsgs bs front cq tok pl tl ml hM aM Vd N)
    (laysCells_ofLots bs front cq tok pl tl ml S R0 F0)
    (laysCells_ofLots bs front cq tok pl tl ml S R1 F1)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5ScriptQ_of_forms
#print axioms ProofFile.Honest.K5.laysCells_ofLots
#print axioms ProofFile.Honest.K5.k5ScriptQ_ofLots
