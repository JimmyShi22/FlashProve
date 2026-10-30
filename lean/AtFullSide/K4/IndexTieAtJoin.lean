-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K4/IndexTieAtJoin.lean: CONDITIONAL.

What turned against the first form. "Agree" is hm, `MsgsAgree` of the joined list of
messages' lots, a proposition (it was `agreeB … = true`, of which the half on pads was idle).
"Owned", which was idle, has fallen with its list of seats. New: `k4IndexOwn_at_join` (the step to
`OwnMsgs`, a statement of its own), `k4IndexTie_at_join_coins` (the tie with its end at
`rowSpentGl`), and beside each of the two ties its form at a fit list. The ends of the two elder
statements are unturned.

What is here. THE TIE `K4IndexTieAt` (Honest/K4/Law/WoTies.lean) AT THE JOINED SCRIPT `joinQ`
(Honest/Thread/Join.lean, of other writers) AND AT THE BOOK A.B THAT `onlineProverFromPublicFiles` RETURNS.
The sender's lot is K1's lot of message n of a job x of the list; owner and start of the lent coin
are the written numbers of AtFullSide/K14/RawFactsWritten.lean (`rawIdxW`).
  `k4IndexOwn_at_join`   A.B lends K4's row (the test `lendsRow`, of `k4Book_at_atPure`), and
      `OwnMsgs` holds at the joined Script at the three fields of K4's text `k4IndexLotG`, with no
      fence on the input and none on the challenges (`k4IndexOwn_ofLots`, Law/W/MaskCovers.lean).
      It asks g < 12 and that `k4PubG` returns, not `LaidK4`: no thread stands in it.
  `k4IndexTie_at_join`   the end of `k4IndexTie_of_ownMsgsG` (Honest/K4/Law/W/IndexLotGIs.lean) with
      Q := joinQ cF.blocksInOrder … and Bk := A.B. That end is kept because it is the form of the hypothesis
      hIx of `k4_exchange_wo_head` (Law/WoHead.lean). IT READS `(endRun cp).getD 0 zeroE`: a list's
      reader with a value behind it. THE DEFAULT BEHIND getD IS DEAD THERE, in this sense: by
      `k4_endRun_coin` (Honest/K4/Law/W/IndexTieCoins.lean) that value, read back, is member number
      `k4Takes` − 1 of `rowSpentGl` wherever the book lends the row and `SumAt` holds, and in this
      end both stand in front of it. That lemma is an equation of two values: that `endRun cp` has
      a member is not said by it.
  `k4IndexTie_at_join_coins`   the end of `k4IndexTie_coinsG` (the same file) with Q := joinQ
      cF.blocksInOrder … and Bk := A.B: member number `k4Takes` − 1 of `rowSpentGl` is the reader's mask
      entry at the entry that the index masks' ledger hands out next. In its end stand no getD, no
      `lendRow` and no `SumAt`. What stays a premise inside that end: the thread's sentence, that
      the state behind the step has a ledger of the index masks, and that this ledger hands out an
      entry.
  `k4IndexTie_at_join_fit`, `k4IndexTie_at_join_coins_fit`   the two ties from the one premise F,
      `JoinFit` (Honest/Thread/JoinFit.lean, of other writers), in the stead of hm: of F's seven
      fields one, msgs, is spent, six are idle there, and the list of seats is a free letter.
WHAT STAYS A HYPOTHESIS, BY NAME: h (the library's head) · hAt (onlineProverFromPublicFiles returns A) · hm ("agree"; in
the forms at a fit list: F) · hx, hn₀ (the job lies in the list and sends message n) · hn (that
message's number is K4's) · hC (hasCoins at A.B for that one job) · hE ("the key": what K1's text
answers at K4's entry is the owner's coin at the written start + takes) · Lh, hQ (in
`k4IndexOwn_at_join`: hg, hP) · and, inside the ends, the thread's sentence.
Not shown here. That any of these holds anywhere. An equation at each run's coins: no value of a
coin is cut off, nothing is counted. The limits of the files named hold here too. No property is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskCovers
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexLotGIs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexTieCoins
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BookAtPure
import AtFullSide.K4.OwnersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs MsgLot Others joinQ joinMl joinPl joinTl
  MsgsAgree JoinFit)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4IndexRow k4IndexPlace k4IndexLotG k4PubG k4IndexNum k4IndexTakes)
open AtFullSide.K14 (rawIdxW)

/-- The written owner and start of the index masks' message. No hypothesis. -/
theorem rawIdxW_owner_start :
    rawIdxW.owner = ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ∧ rawIdxW.base.e = 8647 := ⟨rfl, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, hAt, hm, hx, hn₀, hn, hC, hg, hP and hE. **AT THE BOOK THAT onlineProverFromPublicFiles RETURNS AND
THE JOINED SCRIPT: A.B LENDS K4's ROW, AND `OwnMsgs` HOLDS AT K4's TEXT FOR ITS ENTRY OF THE INDEX
MASKS' MESSAGE**, which is in no list: the lot in the list is K1's. The first half is
`k4Book_at_atPure`'s and spends h, hAt, hg and hP alone; it stands here because the two ties below
call both halves. -/
theorem k4IndexOwn_at_join (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hAt : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Tr X' Xi Xs : Type}
    (front : ℕ) (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr → ProofFile.Honest.K1.PlaceIn Xi) (own₀ : Xs)
    (jobs : List (ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hm : MsgsAgree (joinMl cF.blocksInOrder front arr wit own₀ jobs O))
    {x : ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs} (hx : x ∈ jobs) {n : ℕ}
    (hn₀ : n < x.2.P.sent.size)
    (hn : arr (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).1
      (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).2 = k4IndexNum Zp)
    (hC : dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = ProofFile.Honest.K1.dueR x.2.P x.2.ride)
    {g : ℕ} (hg : g < 12) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : ProofFile.Inst → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp)
    (hE : ∀ (c : Coins A.B) w hd y', ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n c w hd true
        (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y') :
    lendsRow A.B 0 (k4Place Qp) (k4RowIn Qp) = true ∧
    OwnMsgs (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) (fun _ => True) 0
      (k4IndexLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp g).n
      (k4IndexLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp g).fx
      (k4IndexLotG (Bk := A.B) (Rc := Rc) X' cells weights tokens look Zp g).txt := by
  obtain ⟨hB, -, _, idx, -, hidx, -, J⟩ :=
    k4Book_at_atPure h hAt (Rc := Rc) (X := X') cells weights tokens (look Qp) g hg Qp hP
  obtain rfl : idx = rawIdxW :=
    Option.some.inj (hidx.symm.trans (AtFullSide.K4.indexOwner_at_head h))
  have hLs : (⟨arr (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).1
        (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).2, front + roundsTo cF.blocksInOrder x.1,
        ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n⟩ : MsgLot A.B (Local W₀ Rc ProofFile.Inst Tr)) ∈
      joinMl cF.blocksInOrder front arr wit own₀ jobs O := by
    unfold joinMl
    exact List.mem_append.2 (Or.inl (ProofFile.Honest.K1.mem_k1MsgLots hx
      (List.mem_map.2 ⟨n, List.mem_range.2 hn₀, rfl⟩)))
  have OW := k4IndexOwn_ofLots (X := X') cells weights tokens look cF.blocksInOrder front cellsQ tok
    (joinPl cF.blocksInOrder jobs O) (joinTl wit own₀ jobs O) (joinMl cF.blocksInOrder front arr wit own₀ jobs O)
    hLs (hm _ hLs) hP J hn (Vq := fun _ => True) (N := 0)
    (fun c w hd _ _ => by
      obtain ⟨y, hy⟩ := ProofFile.Honest.K1.msgTxt_answers hC wit own₀ n c w
        (hd.take (front + roundsTo cF.blocksInOrder x.1)) true (k4IndexRow Zp g) (k4IndexPlace Zp g)
      show (ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n c w (hd.take (front + roundsTo cF.blocksInOrder x.1)) true
        (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true
      rw [hy]
      rfl)
    hE
  exact ⟨hB, OW⟩

/-- CONDITIONAL on h, hAt, hm, hx, hn₀, hn, hC, hE, Lh and hQ. **K4's TIE ON THE INDEX MASKS'
ENTRY, AT THE JOINED SCRIPT AND THE BOOK THAT onlineProverFromPublicFiles RETURNS.** The end is the form of the
hypothesis hIx of `k4_exchange_wo_head`. The default behind its getD is dead there: by
`k4_endRun_coin` (Honest/K4/Law/W/IndexTieCoins.lean) that value, read back, is member number
k4Takes − 1 of `rowSpentGl` wherever the book lends the row and `SumAt` holds: both stand in front
of it here. -/
theorem k4IndexTie_at_join (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hAt : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Ky Tr X₀ X' Xi Xs : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (front : ℕ) (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr → ProofFile.Honest.K1.PlaceIn Xi) (own₀ : Xs)
    (jobs : List (ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front arr wit own₀ jobs O))
    {x : ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs} (hx : x ∈ jobs) {n : ℕ}
    (hn₀ : n < x.2.P.sent.size)
    (hn : arr (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).1
      (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).2 = k4IndexNum Zp)
    (hC : dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = ProofFile.Honest.K1.dueR x.2.P x.2.ride)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {xx : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g xx blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp xx.2 = some Qp)
    (hE : ∀ (c : Coins A.B) w hd y', ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n c w hd true
        (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y') :
    ∀ blk,
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
      ∃ cc,
        lendRow A.B
          (A.B.rowsOf (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test
            carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test
            carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts 0 = .ok cc ∧
        ∀ name endName (cp : SumCoins name endName (mergeSum Qp)),
        SumAt cc (k0 Qp.g + 15) name endName (mergeSum Qp) cp →
        K4IndexTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test
          carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)) := by
  obtain ⟨hB, OW⟩ := k4IndexOwn_at_join h hAt (X' := X') front cellsQ tok arr wit own₀ jobs O hm hx
    hn₀ hn hC Lh.lt cells weights tokens look (k4PubG_of Lh hQ) hE
  exact (k4IndexTie_of_ownMsgsG h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX
    item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh hQ hB OW (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => Nat.zero_le _)).2

/-- CONDITIONAL on h, hAt, F, hx, hn₀, hn, hC, hE, Lh and hQ. **THE SAME AT A FIT LIST.** Of F's
seven fields one is spent: msgs. The six fields pads, owned, nums, trees, found and fits are idle
here, and the list of seats is a free letter: the statement above asks less. -/
theorem k4IndexTie_at_join_fit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hAt : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Ky Tr X₀ X' Xi Xs : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (front : ℕ) (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr → ProofFile.Honest.K1.PlaceIn Xi) (own₀ : Xs)
    (jobs : List (ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder front arr seats wit own₀ jobs O)
    {x : ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs} (hx : x ∈ jobs) {n : ℕ}
    (hn₀ : n < x.2.P.sent.size)
    (hn : arr (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).1
      (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).2 = k4IndexNum Zp)
    (hC : dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = ProofFile.Honest.K1.dueR x.2.P x.2.ride)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {xx : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g xx blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp xx.2 = some Qp)
    (hE : ∀ (c : Coins A.B) w hd y', ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n c w hd true
        (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y') :
    ∀ blk,
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
      ∃ cc,
        lendRow A.B
          (A.B.rowsOf (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test
            carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test
            carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts 0 = .ok cc ∧
        ∀ name endName (cp : SumCoins name endName (mergeSum Qp)),
        SumAt cc (k0 Qp.g + 15) name endName (mergeSum Qp) cp →
        K4IndexTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test
          carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)) :=
  k4IndexTie_at_join h hAt H front cellsQ tok arr wit own₀ jobs O test carryX item n₁ n₂ b₀ Vd Rd
    Kp w₁ F.msgs hx hn₀ hn hC Said Lh hQ hE

/-- CONDITIONAL on h, hAt, hm, hx, hn₀, hn, hC, hE, Lh and hQ. **THE SAME TIE WITH ITS END AT
`rowSpentGl`: BEHIND THE MEMBER's STEP, AT THAT RUN's OWN COINS, MEMBER NUMBER k4Takes − 1 OF WHAT
A.B's ENTRIES HAND K4's ROW TO SPEND IS THE READER's MASK ENTRY AT THE ENTRY THAT THE INDEX MASKS'
LEDGER HANDS OUT NEXT.** The end of `k4IndexTie_coinsG` at the joined Script and A.B: no getD, no
`lendRow` and no `SumAt` stands in it. cells, weights, tokens and look are letters that neither a
hypothesis nor the end reads: the proof lays K4's text at them, so they are handed by hand. -/
theorem k4IndexTie_at_join_coins (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hAt : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Ky Tr X₀ X' Xi Xs : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (front : ℕ) (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr → ProofFile.Honest.K1.PlaceIn Xi) (own₀ : Xs)
    (jobs : List (ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front arr wit own₀ jobs O))
    {x : ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs} (hx : x ∈ jobs) {n : ℕ}
    (hn₀ : n < x.2.P.sent.size)
    (hn : arr (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).1
      (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).2 = k4IndexNum Zp)
    (hC : dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = ProofFile.Honest.K1.dueR x.2.P x.2.ride)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {xx : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g xx blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub}
    (hQ : k4PubOf Zp xx.2 = some Qp)
    (hE : ∀ (c : Coins A.B) w hd y', ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n c w hd true
        (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y') :
    ∀ blk,
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
      ∀ ds' l e l',
      ledgerAt ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX
        item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s').2 = some l →
      takeEntry l = some (e, l') →
      (rowSpentGl A.B (c.look 0) (k4Place Qp) (k0 Qp.g + 16) 0)[k4Takes Qp.P Qp.hp Qp.g - 1]? =
        some ((h.𝔇.rw13
          ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s')
          ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c y.2.st.input (y.2.st.heard ++ ds'))).mask
          ⟨((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s').2.out.indexMasks, e⟩) := by
  obtain ⟨hB, OW⟩ := k4IndexOwn_at_join h hAt (X' := X') front cellsQ tok arr wit own₀ jobs O hm hx
    hn₀ hn hC Lh.lt cells weights tokens look (k4PubG_of Lh hQ) hE
  exact k4IndexTie_coinsG h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
    n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh hQ hB OW (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => Nat.zero_le _)

/-- CONDITIONAL on h, hAt, F, hx, hn₀, hn, hC, hE, Lh and hQ. **THE SAME AT A FIT LIST.** Of F's
seven fields one is spent: msgs. The six fields pads, owned, nums, trees, found and fits are idle
here, and the list of seats is a free letter: the statement above asks less. -/
theorem k4IndexTie_at_join_coins_fit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hAt : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Ky Tr X₀ X' Xi Xs : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (front : ℕ) (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr → ProofFile.Honest.K1.PlaceIn Xi) (own₀ : Xs)
    (jobs : List (ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder front arr seats wit own₀ jobs O)
    {x : ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) Xs} (hx : x ∈ jobs) {n : ℕ}
    (hn₀ : n < x.2.P.sent.size)
    (hn : arr (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).1
      (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder x.1 x.2.P n).2 = k4IndexNum Zp)
    (hC : dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = ProofFile.Honest.K1.dueR x.2.P x.2.ride)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {xx : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g xx blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub}
    (hQ : k4PubOf Zp xx.2 = some Qp)
    (hE : ∀ (c : Coins A.B) w hd y', ProofFile.Honest.K1.msgTxt 0 wit x.2 own₀ n c w hd true
        (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y') :
    ∀ blk,
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item n₁ n₂
        b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
      ∀ ds' l e l',
      ledgerAt ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX
        item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s').2 = some l →
      takeEntry l = some (e, l') →
      (rowSpentGl A.B (c.look 0) (k4Place Qp) (k0 Qp.g + 16) 0)[k4Takes Qp.P Qp.hp Qp.g - 1]? =
        some ((h.𝔇.rw13
          ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s')
          ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c y.2.st.input (y.2.st.heard ++ ds'))).mask
          ⟨((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s').2.out.indexMasks, e⟩) :=
  k4IndexTie_at_join_coins h hAt H front cellsQ tok arr wit own₀ jobs O test carryX item n₁ n₂ b₀ Vd
    Rd Kp w₁ F.msgs hx hn₀ hn hC Said Lh cells weights tokens look hQ hE

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.rawIdxW_owner_start
#print axioms ProofFile.Honest.K4.W.k4IndexOwn_at_join
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_join
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_join_fit
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_join_coins
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_join_coins_fit
