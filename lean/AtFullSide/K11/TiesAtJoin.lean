-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/TiesAtJoin.lean: what the head's merge (the kind K11) asks of a `Script`, stated at
the `Script` that is laid of the one list of the senders' lots (`joinQ`,
Johnson/Desc/ProofFile/Honest/Thread/Join.lean), at the first chain's thread under the library's
head. The merge sends no message. It reads one entry of a message that the opening's sender of the
kind K1 sends, 38 entries of a message that a code switch (the kind K2) sends, and the cells. So it
hands the list no lot: for each message one `Covers` (Honest/Small/Covers.lean) of its own lot by
the sender's lot carries the sender's place in the list over to the merge's lot. No definition.
Lemmas; none of the library's goals. It lies in the side library because it imports files of it.

  1  `spender_ownMsgs_at_join`   a lot that a lot of the list covers has `OwnMsgs` at `joinQ`
  2  `k11_cells_at_join`         `K11CellsQ`, where the cells are laid as the index's matrix
  3  `k11_indexTie_at_join`      the field indexTie of `K11ScriptMsg`, against K1's lot
  4  `k11_maskTie_at_join`       the field maskTie, against a sender's lot that is a parameter
  5  `k11_scriptMsg_at_join`     the two together: `K11ScriptMsg`
  6  `book_at_atPure`            the book of these lemmas is the book that `onlineProverFromPublicFiles` returns
  7  `k11_exchange_at_join`      `k11_exchange_by_kind` (Honest/K11/Plays/ExchangeByKind.lean),
                                 called at `joinQ` and at that book

What stays a hypothesis.
  * h: the library's head. hb: the maker's base returns Bs. In 7: hb₀, b₀ is at most 346.
  * hB, in 3 and 5: `bookWhole`, called at the head's description, returns B. A return means only
    that the checks inside `bookWhole` passed.
  * hagI, hagM: the other lots of the joined list that bear the sender's lot's number agree with it
    (`LotsAgree`), at each of the two senders' lots. In 7: hag, that all lots of messages of the
    list agree (`MsgsAgree`), which gives both. Where the test `agreeB` of Join.lean passes,
    `agree_of_test` gives hag.
  * hJ, hP, hR: the list of jobs holds, at member 2, a job with the opening's plan and ride.
  * hin, hc: some lot Ls of the other senders' share covers the merge's lot of the mask row. No text
    of a code switch is named here. `k11MaskLot_covered_at_zero` (MaskLotCoveredAtZero.lean of this
    folder) gives hc for the switch into link 24, under its own hypothesis hv on that sender. It
    rests on a test that asks a part's name, its count and that the owners' cuts fit: that test
    passes as well at a book that lends another owner's coins of that count. That the switch's lot
    lies in anybody's share is not said here.
  * hhalf: the prover's half at the merge's place is `headMergeHalf`. For the half that keeps its
    tables (`headMergeHalfKeep`) nothing is said here.
  * hA, in 6 and 7: `onlineProverFromPublicFiles` returns.

Limits.
  * No list is laid here: the jobs, the reader wit and the other senders' share are parameters. So
    is the prover H: in 7 `onlineProverFromPublicFiles`'s return gives the book alone.
  * Chain 0 alone.
  * `k11_cells_at_join` fixes what the cells are as a function of the input's index, and the
    reader of the weights with them. It is true by how the cells are laid. What the head of
    Honest/K11/Plays/CellsAtEntryOf.lean says of its hypothesis hQ holds of this lemma too.
  * Both fields of `K11ScriptMsg` speak behind a played step of the merge. Where no step is played
    they say nothing.
  * `k11_exchange_at_join` has all limits of ExchangeByKind.lean. It does not say that the verifier
    accepts any run.
  * That the thread stands at any state is not said: at a Vd that holds of no input each lemma here
    that names Vd says nothing.
  * That the maker's base returns is a hypothesis here (hb). `base_at_head`
    (TiesAtJoinUnderHead.lean of this folder) has it under the head.
  * The full size; the format's second hash function. Closed facts by Lean's kernel lie beneath.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K11.IndexLotCovered
import AtFullSide.K14.MakersBookOne
import Johnson.Desc.ProofFile.Honest.K11.Plays.CellsAtEntryOf
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotInList
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexTieOfOwn
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskBridge
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLots
import Johnson.Desc.ProofFile.Honest.Thread.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim WsLay)
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (PlaceIn SendJob msgTxt)
open ProofFile.Honest.K4.Lot (k4IndexNum)
open ProofFile.Honest.K11
open AtFullSide.K14 (makers_book_one)

/-! ## 1 A spender's lot -/

/-- **A lot that a lot of the joined list covers has `OwnMsgs` at the joined `Script`.** The covered
lot may lie in the list or not. -/
theorem spender_ownMsgs_at_join {Bk : ProverCoinCounts} {Cl Wl Xi Y Cells Tok : Type} {bs : List (Block S Cl)}
    {front : Nat} {arr : ℕ → ℕ → ℕ} {wit : Wl → PlaceIn Xi} {own₀ : Y}
    {jobs : List (Nat × SendJob (PlaceIn Xi) Y)} {Oth : Others Bk Wl}
    (cells : Wl → Cells) (tok : Wl → Tok) {Vd : Wl → Prop} {N : Nat} {Ls L : MsgLot Bk Wl}
    (hin : Ls ∈ joinMl bs front arr wit own₀ jobs Oth)
    (hag : LotsAgree (joinMl bs front arr wit own₀ jobs Oth) Ls) (hc : Covers Vd N Ls L) :
    OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs Oth) Vd N L.n L.fx L.txt :=
  ofLots_ownMsgs_of_covers bs front cells tok (joinPl bs jobs Oth) (joinTl wit own₀ jobs Oth)
    (joinMl bs front arr wit own₀ jobs Oth) hin hag hc

/-! ## 2 The cells -/

/-- **The merge's hypothesis on the cells, where the cells are laid as the index's matrix** and the
weights are read off the same index. It asks nothing of the lots, of the book or of any test. -/
theorem k11_cells_at_join {Bk : ProverCoinCounts} {Cl Rc Tr Xi Y : Type} (bs : List (Block S Cl)) (front : Nat)
    (tok : Local Cm.Idx Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (wit : Local Cm.Idx Rc ProofFile.Inst Tr → PlaceIn Xi) (own₀ : Y)
    (jobs : List (Nat × SendJob (PlaceIn Xi) Y)) (Oth : Others Bk (Local Cm.Idx Rc ProofFile.Inst Tr))
    (lay : WsLay) (Vd : Local Cm.Idx Rc ProofFile.Inst Tr → Prop) :
    K11CellsQ
      (joinQ bs front (fun v => VerifiableInference.OnPublicFiles.Flat.matrixOf v.w₀) tok arr wit own₀
        jobs Oth)
      lay (fun i => ⟨OnBytes.HonestTrace.entryOf i⟩) Vd :=
  k11CellsQ_at_entryOf Bk Rc Tr _ lay Vd fun _ _ => rfl

/-! ## 3 The two messages -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {B : ProverCoinCounts}

section
variable {W₀ Rc Ky Tr X₀ X Xi Y : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (front : Nat)
  (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xi)
  (own₀ : Y) (jobs : List (Nat × SendJob (PlaceIn Xi) Y))
  (Oth : Others B (Local W₀ Rc ProofFile.Inst Tr)) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
  (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
  (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
    (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
    (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay))

/-- **The field indexTie at the joined `Script`**, against the lot that K1's list lays for the
opening's message 4. -/
theorem k11_indexTie_at_join (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hhalf : ((lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g => g.place == IM.k11Place) =
        some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)))
    {J : SendJob (PlaceIn Xi) Y} (hJ : (2, J) ∈ jobs)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (hagI : LotsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Oth)
      ⟨k4IndexNum Zp, front + roundsTo cF.blocksInOrder 2, msgTxt 0 wit J own₀ 4⟩) :
    K11IndexTieF
      (lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      SaidOk 346 (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins
        (lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
          carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id
      (dataAtHead h (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) carryX)
      24 := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hb)
  exact indexTieOfOwn Z D r Zp Np cF x h B W₀ Rc Ky Tr X₀ X H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w
    _ claims weights c₀ hb hhalf
    (spender_ownMsgs_at_join cells tok
      (List.mem_append.2 (Or.inl (openingLot_mem_list h O front wit own₀ J hP jobs hJ))) hagI
      (k11IndexLot_covered h O hB X claims weights wit J own₀ hP hR Vd 0 _))

/-- **The field maskTie at the joined `Script`**, against a lot Ls of the other senders' share that
covers the merge's lot. B is any book here: whatever is needed of it sits inside hc. -/
theorem k11_maskTie_at_join (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hhalf : ((lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g => g.place == IM.k11Place) =
        some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)))
    {Ls : MsgLot B (Local W₀ Rc ProofFile.Inst Tr)} (hin : Ls ∈ Oth.ml)
    (hagM : LotsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Oth) Ls)
    (hc : Covers Vd 0 Ls (k11MaskLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place
      (_root_.K11.parOf Zp Bs.G₀) claims weights (P5J.At.num Zp 24 0) 3531)) :
    K11MaskTieF
      (lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      SaidOk 346 (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins
        (lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
          carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id
      (dataAtHead h (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) carryX)
      24 :=
  maskTieOfOwn Z D r Zp Np cF x h B W₀ Rc Ky Tr X₀ X H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    claims weights c₀ hb hhalf
    (spender_ownMsgs_at_join cells tok (List.mem_append.2 (Or.inr hin)) hagM hc)

/-- **The merge's hypothesis on the messages at the joined `Script`.** -/
theorem k11_scriptMsg_at_join (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hhalf : ((lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g => g.place == IM.k11Place) =
        some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)))
    {J : SendJob (PlaceIn Xi) Y} (hJ : (2, J) ∈ jobs)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (hagI : LotsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Oth)
      ⟨k4IndexNum Zp, front + roundsTo cF.blocksInOrder 2, msgTxt 0 wit J own₀ 4⟩)
    {Ls : MsgLot B (Local W₀ Rc ProofFile.Inst Tr)} (hin : Ls ∈ Oth.ml)
    (hagM : LotsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Oth) Ls)
    (hc : Covers Vd 0 Ls (k11MaskLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place
      (_root_.K11.parOf Zp Bs.G₀) claims weights (P5J.At.num Zp 24 0) 3531)) :
    K11ScriptMsg
      (lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      SaidOk 346 (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins
        (lettersHead h H (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
          carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id
      (dataAtHead h (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) carryX)
      24 :=
  (scriptMsgIff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
    ⟨k11_maskTie_at_join h H front cells tok wit own₀ jobs Oth test carryX item n₁ n₂ b₀ Vd Rd Kp w
        claims weights c₀ hb hhalf hin hagM hc,
      k11_indexTie_at_join h H front cells tok wit own₀ jobs Oth test carryX item n₁ n₂ b₀ Vd Rd Kp
        w claims weights c₀ hb hB hhalf hJ hP hR hagI⟩

end

/-! ## 4 The book -/

/-- **The book of the lemmas above is the book that `onlineProverFromPublicFiles` returns**, at whatever filling. So each
lemma that takes hB can be called at that book. -/
theorem book_at_atPure (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B := by
  obtain ⟨B, -, hB, -, -, hall⟩ := makers_book_one h
  rw [(hall _ _ _ _ _ P A hA).1]
  exact hB

/-! ## 5 The kind's debt, called -/

/-- **`k11_exchange_by_kind` at the joined `Script` and the book that `onlineProverFromPublicFiles` returns.** Q is the
joined `Script`, by hQ. The lemmas above supply its two hypotheses on the `Script`; their own
hypotheses remain. -/
theorem k11_exchange_at_join {Rc Ky Tr X₀ X Xi Y : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {P : OnlineProverParts Cm.Idx Rc Tr X₀ X}
    {A : OnlineProverWithDescription Cm.Idx Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (H : Prover Cm.Idx Rc ProofFile.Inst Ky Tr X₀ X) (front : Nat)
    (tok : Local Cm.Idx Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local Cm.Idx Rc ProofFile.Inst Tr → PlaceIn Xi) (own₀ : Y)
    (jobs : List (Nat × SendJob (PlaceIn Xi) Y)) (Oth : Others A.B (Local Cm.Idx Rc ProofFile.Inst Tr))
    (Q : Script A.B (Local Cm.Idx Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hQ : Q = joinQ cF.blocksInOrder front (fun v => VerifiableInference.OnPublicFiles.Flat.matrixOf v.w₀) tok
      (P5J.At.arr Zp) wit own₀ jobs Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local Cm.Idx Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local Cm.Idx Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local Cm.Idx Rc ProofFile.Inst Tr)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay))
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (hb₀ : b₀ ≤ 346)
    (hhalf : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf (headClaimsAt cF Zp Bs.G₀) (fun i => ⟨OnBytes.HonestTrace.entryOf i⟩)
          (_root_.K11.parOf Zp Bs.G₀)))
    (hag : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Oth))
    {J : SendJob (PlaceIn Xi) Y} (hJ : (2, J) ∈ jobs)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    {Ls : MsgLot A.B (Local Cm.Idx Rc ProofFile.Inst Tr)} (hin : Ls ∈ Oth.ml)
    (hc : Covers Vd 0 Ls (k11MaskLot A.B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place
      (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀)
      (fun i => ⟨OnBytes.HonestTrace.entryOf i⟩) (P5J.At.num Zp 24 0) 3531)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b j := by
  subst hQ
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hb)
  exact k11_exchange_by_kind Z D r Zp Np cF x h A.B Cm.Idx Rc Ky Tr X₀ X H _ test carryX item n₁ n₂
    b₀ Vd Rd Kp w _ _ c₀ hb hb₀ hhalf
    (k11_scriptMsg_at_join h H front _ tok wit own₀ jobs Oth test carryX item n₁ n₂ b₀ Vd Rd Kp w _
      _ c₀ hb (book_at_atPure h hA) hhalf hJ hP hR
      (hag _ (List.mem_append.2 (Or.inl (openingLot_mem_list h O front wit own₀ J hP jobs hJ))))
      hin (hag _ (List.mem_append.2 (Or.inr hin))) hc)
    (k11_cells_at_join cF.blocksInOrder front tok (P5J.At.arr Zp) wit own₀ jobs Oth _ Vd)

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.spender_ownMsgs_at_join
#print axioms AtFullSide.K11.k11_cells_at_join
#print axioms AtFullSide.K11.k11_indexTie_at_join
#print axioms AtFullSide.K11.k11_maskTie_at_join
#print axioms AtFullSide.K11.k11_scriptMsg_at_join
#print axioms AtFullSide.K11.book_at_atPure
#print axioms AtFullSide.K11.k11_exchange_at_join
