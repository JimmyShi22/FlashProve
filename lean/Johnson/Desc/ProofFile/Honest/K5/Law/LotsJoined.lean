-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotsJoined.lean: ATTENTION's JOINED LAW ON K5's MEMBER
(`k5_owes_all_joined_left`, AllJoinedLeft.lean in this folder) AT A SCRIPT THAT IS LAID FROM LOTS
(`Script.ofLots`, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean), WITH ITS PREMISE ON THE
SCRIPT PAID FROM THE LIST OF LOTS. IT PAYS NOTHING OF THE SCRIPT BY ITSELF: IT MOVES THE DEBT ONTO
THE LIST OF LOTS. CONDITIONAL: under the hypothesis h, the library's head on the public input
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), and on the premises that are listed below. Three theorems.
`typedSeat` and `reach_typedSeat` are declared in TypedSeat.lean in this folder: what is said of
them here holds of them there.

Main names:
  `k5_owes_all_joined_lots`: **THE JOINED LAW AT THE LAYING**: the statement of
    `k5_owes_all_joined_left` with the letter Q set to `Script.ofLots bs front cq tok pl tl ml`, its
    premise HQ gone, and what pays HQ in its stead.
  `hQ_ofLots`: THAT PREMISE's TEXT at the laying, for all plans and places of group g.
    `k5_owes_all_joined_typed`: THE SAME LAW at bs := the first chain's sub-protocols, front := 0
    and the seats `typedSeat h A.G (2 * g)`, `typedSeat h A.G (2 * g + 1)`, no challenge heard: R0
    AND R1 ARE PAID (`reach_typedSeat`); hfix IS EXCHANGED, NOT PAID, for hoff, the premise of the
    frame's `ofLots_hfix` on the lots of trees. LEFT THERE, fifteen: hSz, hg, hA, hO, hoff, hf,
    hRdM, hLent, hrd, hqa, hSm, HM, F0, F1, hH.
  WHAT IS LEFT, BY NAME: hSz, hg, hA, hO, hfix, hf, hRdM, hLent, hrd, hqa, hSm, HM, R0, F0, R1, F1,
    hH. SEVENTEEN WHERE THE LAW AT A LETTER Q HAS NINE: the law is no worse: one premise on a free Q
    is unfolded into what a laying must have. MET BY A CHOICE OF A LETTER: hrd (a reader whose cells
    are the trace): F0 and F1 then speak of the lots at that reader. ON LETTERS AND PUBLIC DATA, no
    input, coin or trace in them: hg, hO, hf; hSz, on the filling's own sizes S; R0, R1, which
    `k5_owes_all_joined_typed` pays at the typed seats. TRUE DEBTS: hA, hfix, hRdM, hLent, hqa, hSm,
    hH, and on the list of lots HM, F0, F1: K5's lots are among the lots, and each agrees with the
    other lots of its message wherever both answer.

How. `k5ScriptQ_ofLots` (LotsK5.lean in this folder) at the seat `seatOf keyOfK3 Zp G cF g a`, whose
three public fields are the plan's by unfolding (SeatReturns.lean); the plan's facts: `k5_member`
(Member.lean); the message with the mask row: `masks_head` (ReaderReadsK5.lean) with
`masksUpTo_yes`; the number of coins: `coinsFew_of_lent` (CoinsFewOf.lean). `reach_typedSeat`:
`reach_firstSeat`, `reach_switchSeat` (ReachAtHead.lean in this folder), one premise forgotten.

Limits. IT MAY HOLD EMPTILY: the law ends in `Plays`, `Behind`, `Exchange`, `RidesPast` and
`Accepted` (Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) at the thread of `lettersHead`: each of
the five is an implication from the thread in front, and that the thread holds at any run is proved
nowhere; its test on inputs is v = w and Vd v, so where Vd fails at w the five hold of nothing. Vd,
RdL, f, test, carryX, item, n₁, n₂, w and the laying's parts are free letters. Nothing proves that
the premises can be met together. "AGREE" STANDS IN HM, F0, F1, UNPAID. S is the sizes' letter of
the filling in hA: one S in the filling and in K5's lots. In `k5_owes_all_joined_lots` bs and front
are letters: the law also stands at layings that no thread fits; hfix and hH speak of the laying.
Nothing ties cq, the laid Script's cells, to the trace's cells. In `k5_owes_all_joined_lots` the
seats are letters. What is laid in at `k5_owes_all_joined_typed` is what was asked for: no search
was made for all that could be. The file stands over AllJoinedLeft.lean, a working form, and over
the frame's ScriptLots.lean: neither lies in a seal. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsK5
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedLeft
import Johnson.Desc.ProofFile.Honest.K5.Law.ReachAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.TypedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg masksUpTo_yes)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree
  ofLots_hfix)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bk : ProverCoinCounts}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE JOINED LAW's PREMISE ON THE SCRIPT, AT A SCRIPT LAID FROM LOTS.** CONDITIONAL: every
premise stands, by name, in the file's head. -/
theorem hQ_ofLots {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok) (pl : List (PadLot Bk
              (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    {S : Sz} (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12) (G : Ground)
        {Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop}
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp G cF g a))
    {rd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)}
    {heard₀ heard₁ : MsgAddr → ℕ} (hrd : ∀ v, (rd v).cells = id v.trace)
    (hqa : ∀ v, Vd v → ∀ r c, (id v.trace : Cells).cell (2 * g) "qa" r c =
      (id v.trace : Cells).cell (2 * g + 1) "qa" r c)
    (hSm : ∀ a, (P5J.At.X Zp).A[g]? = some a → CellsSmallQ Vd a id (seatOf keyOfK3 Zp G cF g a))
    (HM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM →
      maskLot h x₁ kM hk (seatOf keyOfK3 Zp G cF g a) (OnBytes.Model.Forest.elems a.fs) ∈ ml ∧
        LotsAgree ml
          (maskLot h x₁ kM hk (seatOf keyOfK3 Zp G cF g a) (OnBytes.Model.Forest.elems a.fs)))
    (R0 : ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g]? = some As → Ar ∈ As → offPlanes (2 * g) Ar.name = true →
      ((cellsVals Sz.ref).size (2 * g) Ar.name).isSome = true →
      ∃ Ad : MsgAddr, seat₀ Ad = some (2 * g, Ar.message) ∧ heard₀ Ad ≤ roundsTo cF.blocksInOrder
          (borderOf g))
    (F0 : ∀ (Ad : MsgAddr) (m : ℕ), seat₀ Ad = some (2 * g, m) →
      fillLot h S rd seat₀ heard₀ Ad (2 * g) m ∈ ml ∧
        LotsAgree ml (fillLot h S rd seat₀ heard₀ Ad (2 * g) m))
    (R1 : ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g + 1]? = some As → Ar ∈ As → offPlanes (2 * g + 1) Ar.name = true →
      ((cellsVals Sz.ref).size (2 * g + 1) Ar.name).isSome = true →
      ∃ Ad : MsgAddr, seat₁ Ad = some (2 * g + 1, Ar.message) ∧ heard₁ Ad ≤ roundsTo cF.blocksInOrder
          (borderOf g))
    (F1 : ∀ (Ad : MsgAddr) (m : ℕ), seat₁ Ad = some (2 * g + 1, m) →
      fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m ∈ ml ∧
        LotsAgree ml (fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m)) :
    ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h (Script.ofLots bs front cq tok pl tl ml) Vd (roundsTo cF.blocksInOrder
          (borderOf g)) x₁ a id
        (seatOf keyOfK3 Zp G cF g a) (OnBytes.Model.Forest.elems a.fs) := by
  intro a x₁ ha hx
  obtain ⟨blk, a', -, Pl', -⟩ := k5_member h hg
  have ea : a' = a := Option.some.inj (Pl'.plan.symm.trans ha)
  have Pl : PlanAt Zp g a := ea ▸ Pl'
  obtain ⟨-, kM, hk, hm, -, -⟩ := masksUpTo_yes (masks_head h hg ha hx).1 h.𝔇.l3.rad
  exact k5ScriptQ_ofLots bs front cq tok pl tl ml hSz hg Pl hx hm rfl
    (coinsFew_of_lent (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (cells := id)
      (hLent a ha))
    rfl rfl hrd hqa (hSm a ha) (HM a x₁ kM hk ha hx hm).1 (HM a x₁ kM hk ha hx hm).2 R0 F0 R1 F1

/-- **ALL OF THE MEMBER's DEBTS AT THE PROVER THAT onlineProverFromPublicFiles RETURNS, AT A SCRIPT LAID FROM LOTS.**
CONDITIONAL: every premise stands, by name, in the file's head. IT MOVES THE DEBT. -/
theorem k5_owes_all_joined_lots {S₀ Cl₀ : Type} (bs : List (Block S₀ Cl₀)) (front : ℕ)
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) (hSz : planesAtRef S = Sz.ref) {g : Nat}
    (hg : g < 12) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      (Script.ofLots bs front cq tok pl tl ml).fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp A.G cF g a))
    {rd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)}
    {heard₀ heard₁ : MsgAddr → ℕ} (hrd : ∀ v, (rd v).cells = id v.trace)
    (hqa : ∀ v, Vd v → ∀ r c,
      (id v.trace : Cells).cell (2 * g) "qa" r c = (id v.trace : Cells).cell (2 * g + 1) "qa" r c)
    (hSm : ∀ a, (P5J.At.X Zp).A[g]? = some a → CellsSmallQ Vd a id (seatOf keyOfK3 Zp A.G cF g a))
    (HM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM →
      maskLot h x₁ kM hk (seatOf keyOfK3 Zp A.G cF g a) (OnBytes.Model.Forest.elems a.fs) ∈ ml ∧
      LotsAgree ml (maskLot h x₁ kM hk (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs)))
    (R0 : ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g]? = some As → Ar ∈ As → offPlanes (2 * g) Ar.name = true →
      ((cellsVals Sz.ref).size (2 * g) Ar.name).isSome = true → ∃ Ad : MsgAddr,
      seat₀ Ad = some (2 * g, Ar.message) ∧ heard₀ Ad ≤ roundsTo cF.blocksInOrder (borderOf g))
    (F0 : ∀ (Ad : MsgAddr) (m : ℕ), seat₀ Ad = some (2 * g, m) →
      fillLot h S rd seat₀ heard₀ Ad (2 * g) m ∈ ml ∧
      LotsAgree ml (fillLot h S rd seat₀ heard₀ Ad (2 * g) m))
    (R1 : ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[2 * g + 1]? = some As → Ar ∈ As → offPlanes (2 * g + 1) Ar.name = true →
      ((cellsVals Sz.ref).size (2 * g + 1) Ar.name).isSome = true → ∃ Ad : MsgAddr,
      seat₁ Ad = some (2 * g + 1, Ar.message) ∧ heard₁ Ad ≤ roundsTo cF.blocksInOrder (borderOf g))
    (F1 : ∀ (Ad : MsgAddr) (m : ℕ), seat₁ Ad = some (2 * g + 1, m) →
      fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m ∈ ml ∧
      LotsAgree ml (fillLot h S rd seat₁ heard₁ Ad (2 * g + 1) m))
    (hH : Vd w → ∃ i,
      VerifiableInference.OnPublicFiles.Flat.Holds ((Script.ofLots bs front cq tok pl tl ml).cells w) i) :
    (Plays (lettersHead h A.H (Script.ofLots bs front cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H (Script.ofLots bs front cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H (Script.ofLots bs front cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H (Script.ofLots bs front cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H (Script.ofLots bs front cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_left h (Script.ofLots bs front cq tok pl tl ml) test carryX item n₁ n₂ Vd RdL f
    w hg hA hO hfix hf hRdM hLent
    (hQ_ofLots h bs front cq tok pl tl ml hSz hg A.G hLent hrd hqa hSm HM R0 F0 R1 F1) hH

/-- **THE JOINED LAW AT THE LAYING OVER THE FIRST CHAIN, AT THE TYPED SEATS.** CONDITIONAL: every
premise stands, by name, in the file's head. IT MOVES THE DEBT. -/
theorem k5_owes_all_joined_typed (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) (hSz : planesAtRef S = Sz.ref) {g : Nat}
    (hg : g < 12) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hoff : ∀ b blk, cF.blocksInOrder[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (tl b).off j ≤ blk.rounds.length)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp A.G cF g a))
    {rd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} (hrd : ∀ v, (rd v).cells = id v.trace)
    (hqa : ∀ v, Vd v → ∀ r c,
      (id v.trace : Cells).cell (2 * g) "qa" r c = (id v.trace : Cells).cell (2 * g + 1) "qa" r c)
    (hSm : ∀ a, (P5J.At.X Zp).A[g]? = some a → CellsSmallQ Vd a id (seatOf keyOfK3 Zp A.G cF g a))
    (HM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM →
      maskLot h x₁ kM hk (seatOf keyOfK3 Zp A.G cF g a) (OnBytes.Model.Forest.elems a.fs) ∈ ml ∧
      LotsAgree ml (maskLot h x₁ kM hk (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs)))
    (F0 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g) Ad = some (2 * g, m) →
      fillLot h S rd (typedSeat h A.G (2 * g)) (fun _ => 0) Ad (2 * g) m ∈ ml ∧
      LotsAgree ml (fillLot h S rd (typedSeat h A.G (2 * g)) (fun _ => 0) Ad (2 * g) m))
    (F1 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g + 1) Ad = some (2 * g + 1, m) →
      fillLot h S rd (typedSeat h A.G (2 * g + 1)) (fun _ => 0) Ad (2 * g + 1) m ∈ ml ∧
      LotsAgree ml (fillLot h S rd (typedSeat h A.G (2 * g + 1)) (fun _ => 0) Ad (2 * g + 1) m))
    (hH : Vd w → ∃ i,
      VerifiableInference.OnPublicFiles.Flat.Holds
        ((Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml).cells w) i) :
    (Plays (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        fall (borderOf g) := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  have hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml).fixed (.own j) ≤ roundsTo cF.blocksInOrder b := by
    intro b hb j hj
    have t := ofLots_hfix cF.blocksInOrder 0 cq tok pl tl ml hoff b hb j hj
    rwa [Nat.zero_add] at t
  exact k5_owes_all_joined_lots h test carryX item n₁ n₂ Vd RdL f w cF.blocksInOrder 0 cq tok pl tl ml hSz
    hg hA hO hfix hf hRdM hLent hrd hqa hSm HM (reach_typedSeat h hG _ (by omega)) F0
    (reach_typedSeat h hG _ (by omega)) F1 hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.hQ_ofLots
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_lots
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_typed
