-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotsSenders.lean: K5's PREMISE ON THE SCRIPT, AND ATTENTION's
JOINED LAW ON K5's MEMBER, AT A SCRIPT THAT IS LAID FROM A LIST IN WHICH SOME LOT COVERS K5's
TRIPLE: NO LOT OF K5's NEED LIE IN THE LIST. The list is a letter: nothing here says whose lots it
holds. THE WIDER LAW: where LotsK5.lean and LotsJoined.lean in this folder ask that K5's lot lie in
the list and agree with the others, this file asks that SOME lot of the list agree with the others
and COVER K5's triple: answer the same element wherever K5's text answers (`Covers`, Covers.lean in
this folder). At the lot itself that is the other premise (`covers_self`):
`k5ScriptQ_ofLots_by_senders` has the elder law's statement so. Two theorems then have one
statement: `k5ScriptQ_ofLots` (LotsK5.lean) is the elder, and stays as it went out; the one here is
kept as the proof that the elder law is a case of the wider. OF RECORD FOR A LIST THAT THE FRAME
LAYS: `k5ScriptQ_of_senders` and the three laws over it. IT PAYS NOTHING OF THE SCRIPT BY ITSELF. IT
MAY HOLD EMPTILY. CONDITIONAL: under the hypothesis h, the library's head on the public input
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). No definition; two theorems. `k5ScriptQ_of_senders`,
`k5ScriptQ_ofLots_by_senders` and `hQ_of_senders` are declared in SendersScript.lean in this folder:
what is said of them here holds of them there.

What it is for. The frame plans to lay the senders' lots of whole messages and no spender's lot:
what a spender wants of the Script is an equation at its entries (`OwnMsgs`,
Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean), not a membership in the list.

Main names:
  `k5ScriptQ_of_senders`: **K5ScriptQ at the laying**: the statement of `k5ScriptQ_ofLots` with
    three premises turned: SM, SF0, SF1: there is a lot Ls in ml that agrees with the other lots of
    its message and covers `maskLot …` | `fillLot …`. These two stay as names of a triple (number,
    challenges heard, text): they stand in no list.
  `hQ_of_senders`: the joined law's premise on the Script, for all plans and places of group g.
  `k5_owes_all_joined_senders_book`: the statement of `k5_owes_all_joined_typed_book`
    (LotsJoinedBook.lean) with the same three turned. LEFT, fifteen: hSz, hg, hA, hO, hoff, hf,
    hRdM, hBook, hrd, hqa, hSm, SM, SF0, SF1, hH.
  `k5_owes_all_joined_senders_trace`: the like of `k5_owes_all_joined_typed_trace`
    (TraceIsFull.lean). LEFT, thirteen: hSz, hg, hA, hO, hoff, hf, hRdM, hBook, hT, SM, SF0, SF1,
    hH.

How. `k5ScriptQ_of_forms` (LotsK5.lean) at the laying; each `OwnMsgs` by `ofLots_ownMsgs_of_covers`
(Covers.lean). The joined law: `k5_owes_all_joined_left_book` (AllJoinedLeftBook.lean), with hfix
from hoff (`ofLots_hfix`), the reach from `reach_typedSeat` (TypedSeat.lean) and the lending from
`lends5_at_atPure` (LotsJoinedBook.lean).

Limits. SM, SF0, SF1 ARE PAID BY NOBODY HERE. COVERING AT THE MASK BEARS THE WEIGHT: wherever K5's
text answers member number j of the list `coins5 Bk k Z`, the sender's text answers the same
element, at every run's coins. That the sender's lot agrees with the other lots of the list is a
premise on the frame's own list. No list with such lots is exhibited. IT MAY HOLD EMPTILY: all that
LotsJoined.lean's Limits say holds here. Covers.lean and TraceIsFull.lean lie in no seal, nor do
some of the files beneath them: among these the frame's ScriptLots.lean and our
AllJoinedLeftBook.lean. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so
above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Covers
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceIsFull
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

section
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg masksUpTo_yes)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree
  Covers ofLots_hfix)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- SM, SF0, SF1 ARE PAID BY NOBODY. **THE JOINED LAW AT THE LAYING FROM THE SENDERS' LOTS, AT THE
TYPED SEATS AND THE BOOK's TEST.** CONDITIONAL: every premise stands, by name, in the file's head.
IT MOVES THE DEBT. -/
theorem k5_owes_all_joined_senders_book
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) (hSz : planesAtRef S = Sz.ref)
    {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hoff : ∀ b blk, cF.blocksInOrder[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (tl b).off j ≤ blk.rounds.length)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed A.B (A.B.rowsOf 0) (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp A.G cF g a)).parts 0 = true)
    {rd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers}
    (hrd : ∀ v, (rd v).cells = id v.trace)
    (hqa : ∀ v, Vd v → ∀ r c,
      (id v.trace : Cells).cell (2 * g) "qa" r c = (id v.trace : Cells).cell (2 * g + 1) "qa" r c)
    (hSm : ∀ a, (P5J.At.X Zp).A[g]? = some a → CellsSmallQ Vd a id (seatOf keyOfK3 Zp A.G cF g a))
    (SM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (maskLot h x₁ kM hk
                 (seatOf keyOfK3 Zp A.G cF g a) (OnBytes.Model.Forest.elems a.fs)))
    (SF0 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g) Ad = some (2 * g, m) → ∃ Ls ∈ ml,
      LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S rd (typedSeat h A.G (2 * g))
                 (fun _ => 0) Ad (2 * g) m))
    (SF1 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g + 1) Ad = some (2 * g + 1, m) →
      ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S rd (typedSeat h A.G (2 * g + 1))
                 (fun _ => 0) Ad (2 * g + 1) m))
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
  exact k5_owes_all_joined_left_book h (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml) test carryX item
    n₁ n₂ Vd RdL f w hg hA hO hfix hf hRdM hBook
    (hQ_of_senders h cF.blocksInOrder 0 cq tok pl tl ml hSz hg A.G (lends5_at_atPure h hg hA hBook) hrd
      hqa hSm SM (reach_typedSeat h hG _ (by omega)) SF0 (reach_typedSeat h hG _ (by omega)) SF1)
    hH

/-- hT, SM, SF0, SF1 ARE PAID BY NOBODY. **THE SAME WITH ONE PREMISE ON THE TRACE.** CONDITIONAL:
every premise stands, by name, in the file's head. -/
theorem k5_owes_all_joined_senders_trace
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) (hSz : planesAtRef S = Sz.ref)
    {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hoff : ∀ b blk, cF.blocksInOrder[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (tl b).off j ≤ blk.rounds.length)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed A.B (A.B.rowsOf 0) (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp A.G cF g a)).parts 0 = true)
    (wt : W₀ → Weights) (hT : TraceIsFull (P5J.At.X Zp) Vd (id : Cells → Cells))
    (SM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM → ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (maskLot h x₁ kM hk
                 (seatOf keyOfK3 Zp A.G cF g a) (OnBytes.Model.Forest.elems a.fs)))
    (SF0 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g) Ad = some (2 * g, m) → ∃ Ls ∈ ml,
      LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S
                 (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (typedSeat h A.G (2 * g)) (fun _ => 0) Ad (2 * g) m))
    (SF1 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g + 1) Ad = some (2 * g + 1, m) →
      ∃ Ls ∈ ml, LotsAgree ml Ls ∧
      Covers Vd (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S
                 (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (typedSeat h A.G (2 * g + 1)) (fun _ => 0) Ad
                     (2 * g + 1) m))
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
        fall (borderOf g) :=
  k5_owes_all_joined_senders_book h test carryX item n₁ n₂ Vd RdL f w cq tok pl tl ml hSz hg hA hO
    hoff hf hRdM hBook (rd := fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (fun _ => rfl)
    (hqa_of_traceIsFull h hT hg) (fun _ ha => hSm_of_traceIsFull h hT hg ha rfl rfl) SM SF0 SF1 hH

end

end ProofFile.Honest.K5
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_senders_book
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_senders_trace
