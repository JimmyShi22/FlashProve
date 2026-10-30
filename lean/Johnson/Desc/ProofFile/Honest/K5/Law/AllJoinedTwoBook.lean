-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoinedTwoBook.lean: CONDITIONAL: ATTENTION's JOINED LAW AT
THE LAYING BY LOTS AND THE TYPED SEATS, WITHOUT THE PREMISE "THE MAKER onlineProverFromPublicFiles RETURNS": in its stead
the library's test on the head's public files and the two binders of ReturnsLeftTwo.lean, the first
of them at a named book.

Why. `k5_owes_all_joined_typed_book` (LotsJoinedBook.lean) speaks at a letter A under hA: the maker
returns A; its lots are typed at A's book, its seats at A's ground. Here the book and the ground are
letters B and G of their own, tied to the head's files by book and hG, and A stands in the end
alone.

Main names:
  `atPure_returns_at`: `atPure_returns_two` with the book named: the maker returns an A whose
    public part, ground, description and book are Zp, G, the head's description and B.
  `k5_owes_all_joined_typed_two`: there is such an A, and at its prover the joined law's end
    holds. In hA's stead: hl, book (the book's maker returns B), range, hG. hG is no debt
    (`ground_made_at_head`, AllJoinedTwo.lean).

Which way it goes. hA is derived here from three binders under the head: the law is no worse than
LotsJoinedBook.lean's: whoever holds hA calls that one; this one asks less where the three are had.

Limits. IT MAY HOLD EMPTILY: each of the five parts of the end is an implication from the thread in
front, and that the thread holds at any run is proved nowhere; nothing proves that the premises can
be met together. Implications: none of the binders is proved here; those of LotsJoinedBook.lean
stand as they are, but for hA, with B for A's book and G for A's ground. THAT THE BOOK's MAKER
RETURNS IS PROVED AT NO FILES. The head is a hypothesis, and so is the library's test. The head and
the library's test have a member together at the library's written copy of the full-size public
files (`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), which is tied to
the package's files by no theorem. Else as ReturnsLeftTwo.lean's and LotsJoinedBook.lean's. Through
its imports the file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsJoinedBook
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedTwo

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
  {G : Ground} {B : ProverCoinCounts}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

include h in
/-- **The maker returns, with the book named.** Conditional: h; hl; book: the book's maker returns
B; range; hG. -/
theorem atPure_returns_at (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B)
    (range : I.inRange I.dummy = true) (hG : blankBy pureRoad.links Zp = some G) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A ∧ A.Z = Zp ∧
      A.G = G ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ A.B = B := by
  obtain ⟨A, hA, -, -⟩ := atPure_returns_two h hl I o S O
    (fun k0 k1 k2 e p1 p2 hs => ⟨B, book k0 k1 k2 e p1 p2 hs⟩) range
  obtain ⟨k0, k1, k2, e, p1, p2, hs⟩ := P1Opts.sends_of_laid hl h.laid.pub
  obtain ⟨G', m⟩ := made_head h ⟨k0, k1, k2, e, _, p1, p2, hs, book k0 k1 k2 e p1 p2 hs⟩
  obtain ⟨eZ, eG, eF, eB⟩ := m.unique (parts_of_atPure hA).1
  have e' : G' = G := Option.some.inj (m.ground.symm.trans hG)
  exact ⟨A, hA, eZ.symm, by rw [← eG, e'], eF.symm, eB.symm⟩

/-- **ALL OF THE MEMBER's DEBTS AT THE LAYING BY LOTS AND THE TYPED SEATS, WITHOUT THE PREMISE THAT
onlineProverFromPublicFiles RETURNS.** Conditional: every premise stands, by name, in the file's head and in
LotsJoinedBook.lean's. -/
theorem k5_owes_all_joined_typed_two
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) (hSz : planesAtRef S = Sz.ref)
    {g : Nat} (hg : g < 12)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B)
    (range : I.inRange I.dummy = true) (hG : blankBy pureRoad.links Zp = some G)
    (hO : O.keyOf = keyOfK3)
    (hoff : ∀ b blk, cF.blocksInOrder[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (tl b).off j ≤ blk.rounds.length)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed B (B.rowsOf 0) (seatOf keyOfK3 Zp G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp G cF g a)).parts 0 = true)
    {rd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers}
    (hrd : ∀ v, (rd v).cells = id v.trace)
    (hqa : ∀ v, Vd v → ∀ r c,
      (id v.trace : Cells).cell (2 * g) "qa" r c = (id v.trace : Cells).cell (2 * g + 1) "qa" r c)
    (hSm : ∀ a, (P5J.At.X Zp).A[g]? = some a → CellsSmallQ Vd a id (seatOf keyOfK3 Zp G cF g a))
    (HM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM →
      maskLot h x₁ kM hk (seatOf keyOfK3 Zp G cF g a) (OnBytes.Model.Forest.elems a.fs) ∈ ml ∧
      LotsAgree ml (maskLot h x₁ kM hk (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs)))
    (F0 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h G (2 * g) Ad = some (2 * g, m) →
      fillLot h S rd (typedSeat h G (2 * g)) (fun _ => 0) Ad (2 * g) m ∈ ml ∧
      LotsAgree ml (fillLot h S rd (typedSeat h G (2 * g)) (fun _ => 0) Ad (2 * g) m))
    (F1 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h G (2 * g + 1) Ad = some (2 * g + 1, m) →
      fillLot h S rd (typedSeat h G (2 * g + 1)) (fun _ => 0) Ad (2 * g + 1) m ∈ ml ∧
      LotsAgree ml (fillLot h S rd (typedSeat h G (2 * g + 1)) (fun _ => 0) Ad (2 * g + 1) m))
    (hH : Vd w → ∃ i,
      VerifiableInference.OnPublicFiles.Flat.Holds
        ((Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml).cells w) i) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A ∧ A.G = G ∧
      A.B = B ∧
      ((Plays (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
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
          fall (borderOf g)) := by
  obtain ⟨A, hA, -, eG, -, eB⟩ :=
    atPure_returns_at h (I := I) (o := o) (S := S) (O := O) hl book range hG
  subst eG
  subst eB
  exact ⟨A, hA, rfl, rfl,
    k5_owes_all_joined_typed_book h test carryX item n₁ n₂ Vd RdL f w cq tok pl tl ml hSz hg hA hO
      hoff hf hRdM hBook hrd hqa hSm HM F0 F1 hH⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_at
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_typed_two
