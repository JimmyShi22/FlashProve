-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotsSendersNine.lean: ATTENTION's JOINED LAW ON K5's MEMBER AT
A SCRIPT LAID FROM A LIST IN WHICH SOME LOT COVERS K5's TRIPLE, AT THE RIDERS OF `csHead` AND WITH
THE FRAME's PUBLIC TEST ON THE LENDING. SIDEWAYS against `k5_owes_all_joined_senders_book`
(LotsSenders.lean in this folder), in two halves that go opposite ways. NARROWER: the thread's
letter for the riders is fixed at `ridersOf (csHead ν st R)`, where the premise hRdM is a theorem
(`k5_rides_on_csHead`, RidesOnCs.lean). WIDER: hLends, the test `lendsRow` on the book at K5's row,
stands for hBook; under h, hg and hA hBook gives it, by `lends5_at_atPure` (LotsJoinedBook.lean) and
`lends5_iff` (LendsRow5.lean): a reading of two lemmas; no theorem of this file says so. IT PAYS
NOTHING OF THE SCRIPT. IT MAY HOLD EMPTILY. CONDITIONAL: under the hypothesis h, the library's head
on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). No definition; one theorem.

Main names:
  `k5_owes_all_joined_senders_nine`. LEFT, fourteen: hSz, hg, hA, hO, hoff, hf, hLends, hrd, hqa,
    hSm, SM, SF0, SF1, hH.

How. `k5_owes_all_joined_nine` (RidesOnCs.lean) at the laying and at the book that `onlineProverFromPublicFiles` returns;
its premise on the Script by `hQ_of_senders` (LotsSenders.lean), whose lending comes from hLends by
`lends5_iff` (LendsRow5.lean); hfix from hoff (`ofLots_hfix`); the reach from `reach_typedSeat`
(LotsJoined.lean).

Limits. SM, SF0, SF1 ARE PAID BY NOBODY HERE: covering at the mask bears the weight, as
LotsSenders.lean's Limits say; all of these hold here. `Covers` is one-way: where K5's text answers
nowhere, every lot of that number covers it. ν, st and R are free letters. Through its imports it
stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/
(lean/LIMITS.md, L15): a fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed
function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsSenders
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesOnCs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
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
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- SM, SF0, SF1 ARE PAID BY NOBODY. **THE JOINED LAW AT THE LAYING, AT THE RIDERS OF `csHead`, WITH
THE PUBLIC TEST ON THE LENDING.** CONDITIONAL: every premise stands, by name, in the file's head. -/
theorem k5_owes_all_joined_senders_nine
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
    (hLends : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow A.B 0 (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Row (seatOf keyOfK3 Zp A.G cF g a)) = true)
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
          test carryX item n₁ n₂ b0Head Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread
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
  exact k5_owes_all_joined_nine h (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml) test carryX item n₁ n₂
    Vd ν st R f w hg hA hO hfix hf hLends
    (hQ_of_senders h cF.blocksInOrder 0 cq tok pl tl ml hSz hg A.G
      (fun a ha => (lends5_iff A.B _ _).2 (hLends a ha)) hrd hqa hSm SM
      (reach_typedSeat h hG _ (by omega)) SF0 (reach_typedSeat h hG _ (by omega)) SF1)
    hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_all_joined_senders_nine
