-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotsJoinedBook.lean: ATTENTION's JOINED LAW ON K5's MEMBER AT A
SCRIPT THAT IS LAID FROM LOTS, AT THE TYPED SEATS (`k5_owes_all_joined_typed`, LotsJoined.lean in
this folder), AT THE BOOK THAT onlineProverFromPublicFiles RETURNS, WITH A TEST ON THAT BOOK IN hLent's STEAD. IT PAYS
NOTHING OF THE SCRIPT BY ITSELF: IT MOVES THE DEBT ONTO THE LIST OF LOTS. CONDITIONAL: under the
hypothesis h, the library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), and on
fifteen premises. No definition; two theorems.

Main names:
  `k5_owes_all_joined_typed_book`: **THE LAW**: the statement of `k5_owes_all_joined_typed` with the
    book set to `A.B` and hLent gone for hBook, the premise of `k5_owes_all_joined_left_book`
    (AllJoinedLeftBook.lean in this folder) with its text: a test with code on the book.
  WHAT IS LEFT, BY NAME: hSz, hg, hA, hO, hoff, hf, hRdM, hBook, hrd, hqa, hSm, HM, F0, F1, hH.
  `lends5_at_atPure`: under hA and hBook the book's lending to K5's row returns at every run's coins
    (`Lends5`, CoinsFewOf.lean), at the seat of each plan of group g.

How. `lends5_at_atPure` HAS THE STEPS OF THE PROOF OF `k5_owes_all_joined_left_book`, which knows
this and whose statement does not hand it out: `lends5_of_named` (LendsOfBook.lean),
`parts_of_atPure` (ReturnsOf.lean), `bookWhole_word`, `atPure_at_laid_ground`, `placesOk_of_planOk`
(Johnson/RunOne/Sound/KeyListsAtFK.lean), `k5_member` (Member.lean). If that file states it, that
one is the one to keep.

Limits. Those of LotsJoined.lean: IT MAY HOLD EMPTILY: each of the five parts of its end is an
implication from the thread in front, and that the thread holds at any run is proved nowhere;
nothing proves that the premises can be met together; "AGREE" STANDS IN HM, F0, F1, UNPAID; hfix is
exchanged for hoff, not paid; nothing ties cq to the trace's cells. The book is no letter any more:
the lots are typed at `A.B`. The file stands over AllJoinedLeft.lean, AllJoinedLeftBook.lean and the
frame's ScriptLots.lean: none lies in a seal. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsJoined
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedLeftBook

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
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree)
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

include h in
/-- **Under the book's test the lending to K5's row returns**, at the book that onlineProverFromPublicFiles returns.
CONDITIONAL: under the hypothesis h; hg; hA; hBook. -/
theorem lends5_at_atPure {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed A.B (A.B.rowsOf 0) (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp A.G cF g a)).parts 0 = true) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit A.B (id : Cells → Cells) (seatOf keyOfK3 Zp A.G cF g a) := by
  intro a ha
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  obtain ⟨_, _, _, _, _, _, _, -, hB⟩ := (parts_of_atPure hA).1.book
  have hw : A.B.word A.F = none := bookWhole_word hB
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := (atPure_at_laid_ground h.laid hG hA).2.2
  have hp : A.F.placesOk = true := by
    rw [eF]
    exact Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hpl : (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) ∈ A.F.first.blocksInOrder.map (·.place) := by
    rw [eF]
    obtain ⟨blk, a', hm, -, Dc⟩ := k5_member h hg
    exact List.mem_map.2 ⟨blk, List.mem_of_getElem? hm, Dc.place⟩
  exact lends5_of_named hw hp hpl (hBook a ha)

/-- **THE JOINED LAW AT THE LAYING, AT THE TYPED SEATS AND THE BOOK's TEST.** CONDITIONAL: every
premise stands, by name, in the file's head. IT MOVES THE DEBT. -/
theorem k5_owes_all_joined_typed_book
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
        fall (borderOf g) :=
  k5_owes_all_joined_typed h test carryX item n₁ n₂ Vd RdL f w cq tok pl tl ml hSz hg hA hO hoff hf
    hRdM (lends5_at_atPure h hg hA hBook) hrd hqa hSm HM F0 F1 hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.lends5_at_atPure
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_typed_book
