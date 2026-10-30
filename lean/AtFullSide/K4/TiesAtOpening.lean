-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K4/TiesAtOpening.lean: CONDITIONAL. hE, "THE KEY", IS
NO PREMISE: in each of the six statements it is had by a call of one of two laws of K1's
files, `opening_look_row_at` and `opening_look_idx_at` (AtFullSide/K1/OpeningLookK4.lean).
What stays a premise: h, hAP, hm (or F), hx, Lh, hQ and the
thread's sentence. Six statements with their proofs; no definition. A law with hE as a premise is
each of our three laws named below.

WHAT THAT IS, AND WHAT NOT.
It is an identity of two readings at each run's coins: no law over coins;
nothing on how the element is drawn, on who else reads or spends it, or that it stands at no other
entry; the ties' other premises stay, and no thread is shown to stand at any state. K1's authors'
rider, which goes with every quotation of their laws, to the letter: "An identity of two readings of
one element, at each run's coins: it says WHICH element of the run the entry is. It says nothing on
how that element is drawn, on who else reads or spends it, or that it stands at no other entry. Of
hE, "the key", it is the whole, in hE's own signs, at K1's opening's job, under the head and an
opening: for row 2 as it stands, for row 1 with rowZeroW for row. It pays hE in no tie until that
tie's top calls it." AT A BOOK THAT DOES NOT COVER THE PART's DUE THE TWO LAWS SAY NOTHING: at A.B
the count is had: `hasCoins_two_at_book` (Honest/K1/Law/HasCoinsAtBook.lean; called here for hC; in
the forms at F: F.coins). sendFits, which K1's authors ask to be named beside their two laws: at the
written plan it is their `fits_first_written` (Honest/K1/Law/FitsWritten.lean): not called here. THE
FOURTEEN FILES BENEATH THE TWO LAWS THAT ARE NO ROWS OF laws.12, by K1's authors' own list:
AtFullSide/K1/OpeningLookK4; Honest/K1/Law/LookOfCut; beneath them AtFullSide/K1/OpeningStartsW,
OpeningLengthsW, OpeningSeatsK4, SegmentZeroAtWritten, SegmentZeroJoints, MergeRowAtWritten;
Honest/K1/Law/RowOwnerAtWritten, MaskStartIsBook, DueIsBook, StartAtFour; and two of K4's house:
Honest/K4/Lot/IndexNum, MaskNum.

What is here. THE TWO TIES OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) ON A RUN's
COINS, `K4MaskTieAt` (Honest/K4/Law/ScriptAt.lean) and `K4IndexTieAt` (Honest/K4/Law/WoTies.lean),
AT THE JOINED SCRIPT `joinQ` (Honest/Thread/Join.lean, of other writers)
AND THE BOOK A.B THAT `onlineProverFromPublicFiles` RETURNS, WITH THE SENDER LAID IN AS A WRITTEN TERM: the opening's job
of the shared sending (K1), at member number 2 of the flat list:
    placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd
that is, the plan and the fold at the ground A.G and the public part A.Z of what `onlineProverFromPublicFiles` returns:
the spelling of hJ in K1's authors' `hasCoins_two_at_book` and in their two laws. first (the number
that the job's first new message gets) and Dd (the filling of its main rows) stay letters.
  `k4MaskTie_at_opening`   `k4MaskTie_at_joinQ_k1` (Honest/K4/Law/W/MaskTieAtJoin.lean) at
      y := (2, that job), n := 0, g := 0, row := `rowZeroW`, L := mask rows times the mask code's
      length at the plan's message number 0.
  `k4IndexTie_at_opening`, `k4IndexTie_at_opening_coins`   `k4IndexTie_at_join` and
      `k4IndexTie_at_join_coins` (AtFullSide/K4/IndexTieAtJoin.lean) at x := (2, that job), n := 4,
      arr := P5J.At.arr Zp, at every group g for which Lh holds (Lh.lt: g below 12).
  `…_fit`   beside each, its form at F, `JoinFit` (Honest/Thread/JoinFit.lean, of other writers):
      two fields are spent, msgs and coins.

AGAINST THESE THREE LAWS, PREMISE BY PREMISE.
  FALLEN (each had here by a call): hlt | hn₀ · hn · hC · hrow · hL · hE.
  NEW: hx AT THAT JOB: the laws' hx let the caller choose the pair; here it says that the pair of 2
      and K1's opening's job lies in the list: whoever lays the list owes that. Nothing else is
      new: no opening is a premise: it is drawn out of the head (h.laid.opened), and no letter of
      it stands in a statement.
  UNTURNED: h · hAP | hAt · hm (or F) · Lh (for the mask row at g := 0) · hQ · hT | the thread's
      sentence inside the ends.
WHICH PREMISE IS HAD BY WHICH CALL (K1's authors' laws on public data stand under h and an opening,
at the plan at the description's own ground Bs.G₀ and at Zp; those under AtFullSide/K1/ are trials
of that house, on no list). THE SEAM A.Z = Zp, A.G = Bs.G₀ is `atPure_at_laid_ground`
(Honest/AtHeadGround.lean) at h.laid, the opening's blank and hAP: hx, hE and hC are carried over it
by rewriting.
  hlt | hn₀   `openingNos_head` (AtFullSide/K1/OpeningLengthsW.lean)
  hn at n = 0 `maskNum_zero` (AtFullSide/K1/OpeningSeatsK4.lean)
  hn at n = 4 `index_two` (Honest/K1/Law/K1NumAtHead.lean) with `index_atAll` and `pin1_atAll`
              (Johnson/Desc/K1/Law/)
  hC          `hasCoins_two_at_book` (Honest/K1/Law/HasCoinsAtBook.lean); in the forms at F: F.coins
  hrow        our `rowOwner_at_head` (AtFullSide/K4/OwnersAtHead.lean) at (0, rowZeroW), a member of
              the written rows by `rowZeroW_written` (AtFullSide/K1/SegmentZeroAtWritten.lean)
  hL          `maskReads_below` (AtFullSide/K1/OpeningRoomK4.lean) at `k4PubG_of` Lh hQ
  hE at n = 0 `opening_look_row_at` at h, hAP and hJ := rfl, at the book A.B
  hE at n = 4 `opening_look_idx_at` at the same and Lh.lt
              In each proof hE stands as a "have" in our law's own signs, with the letters laid in:
              Lean holds K1's authors' end against it.

Not shown here. NO INSTANCE OF ALL THE REMAINING PREMISES TOGETHER CAN BE SHOWN TODAY: the thread's
sentence (hT; ThrS inside the ends) has no known instance at the full size at any Script, and F (the
forms at a fit list) has no known instance at the full size; hE is no premise any more; I found no
two premises that bar each other; the other six (h · hAP · hm · hx · Lh · hQ) each have a law, and
their letters let them be met at one object; A LEAN TERM THAT HAS THE SIX TOGETHER, at a list with
an empty record of the other senders, IS NO PART OF THIS LIBRARY.
One tension [argued, not shown]: the only list
at which hm and hx are known together has an EMPTY record of the other senders; there Script.ofLots
lays zero at every message that is not K1's, and we expect the thread's sentence to fail: the
instance that counts needs the whole join. That hm holds at any list; that any list is fit; that any
list holds the pair; that the thread stands at any state: where it stands at none, all six say
nothing. That L is 8192 is K1's authors' `openingLens_head`, over the seam: not called here. The
mask row at group 0 alone: the other eleven groups' mask rows are other senders'. Each statement is
an equation at a run's own coins, entry by entry: nothing is said on how an element of the coins is
sampled, no value of a coin is cut off, nothing is counted. The full size and the format's second
hash function alone. The limits of the files named hold here too. Nothing on soundness, on completeness or on
any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskTieAtJoin
import AtFullSide.K4.IndexTieAtJoin
import AtFullSide.K1.OpeningSeatsK4
import AtFullSide.K1.OpeningRoomK4
import AtFullSide.K1.OpeningLookK4
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsAtBook
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.AtHeadGround

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
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)
open ProofFile.Honest.FirstThread (WtF lettersHead Others joinQ joinMl MsgsAgree JoinFit)
open ProofFile.Honest.K1 (SendJob PlaceIn msgTxt placeJob firstFold index_two hasCoins_two_at_book)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4IndexRow k4IndexPlace k4IndexTakes)
open AtFullSide.K14 (rawIdxW)
open AtFullSide.K1 (rowZeroW rowZeroW_written openingNos_head maskNum_zero maskReads_below
  opening_look_row_at opening_look_idx_at)
open AtFullSide.K4 (rowOwner_at_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {W₀ Rc Ky Tr X₀ X' Xi Xj : Type} {Wa Rca Tra Xa₀ Xa : Type}
  {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (front : ℕ)
  (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xi)
  (own₀ : Xj) (jobs : List (ℕ × SendJob (PlaceIn Xi) Xj))
  (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, hAP, hm, hx, Lh, hQ and hT. **THE TIE ON THE MASK ROW AT GROUP 0, AT K1's
OPENING's JOB AND ITS MESSAGE NUMBER 0.** The law `k4MaskTie_at_joinQ_k1` with hlt, hn, hC, hrow, hL
and hE each had by a call: the head says by which, and what the call for hE is and is not. -/
theorem k4MaskTie_at_opening (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O)) (first : ℕ)
    (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    {k m : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m 0 x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
      carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  have hE : ∀ (k : Coins A.B) w hd ν y',
      ν < (shapeAt (firstPar A.G.first (gpOf A.Z)) 0).maskRows *
        ((firstPar A.G.first (gpOf A.Z)).codes.mask.getD
          (shapeAt (firstPar A.G.first (gpOf A.Z)) 0).maskCode default).ell →
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 0
        k w hd true 0 ν = some y' →
      (k.look 0 rowZeroW.owner).2.eAt (rowZeroW.base.e + ν) = .ok y' :=
    opening_look_row_at h hAP wit own₀ first Dd rfl
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  have hC := hasCoins_two_at_book h hAP first Dd (Y := Xj) rfl
  rw [eZ, eG] at hx hE hC
  exact k4MaskTie_at_joinQ_k1 h H front cellsQ tok wit own₀ jobs O test carryX item n₁ n₂ b₀ Vd Rd
    Kp w₁ hAP hm hx (openingNos_head h Op).1 Lh (maskNum_zero h Op) hC hQ
    (rowOwner_at_head h (0, rowZeroW) (List.mem_of_mem_head? rowZeroW_written)) hE
    (maskReads_below h Op (k4PubG_of Lh hQ)) hT

/-- CONDITIONAL on h, hAP, F, hx, Lh, hQ and hT. **THE SAME AT A FIT LIST.** Of F two fields are
spent: msgs, in hm's stead, and coins, which at this job is hC. The statement above asks less of the
list. -/
theorem k4MaskTie_at_opening_fit (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs O)
    (first : ℕ) (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    {k m : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m 0 x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
      carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  have hE : ∀ (k : Coins A.B) w hd ν y',
      ν < (shapeAt (firstPar A.G.first (gpOf A.Z)) 0).maskRows *
        ((firstPar A.G.first (gpOf A.Z)).codes.mask.getD
          (shapeAt (firstPar A.G.first (gpOf A.Z)) 0).maskCode default).ell →
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 0
        k w hd true 0 ν = some y' →
      (k.look 0 rowZeroW.owner).2.eAt (rowZeroW.base.e + ν) = .ok y' :=
    opening_look_row_at h hAP wit own₀ first Dd rfl
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  rw [eZ, eG] at hx hE
  exact k4MaskTie_at_joinQ_k1 h H front cellsQ tok wit own₀ jobs O test carryX item n₁ n₂ b₀ Vd Rd
    Kp w₁ hAP F.msgs hx (openingNos_head h Op).1 Lh (maskNum_zero h Op) (F.coins _ hx) hQ
    (rowOwner_at_head h (0, rowZeroW) (List.mem_of_mem_head? rowZeroW_written)) hE
    (maskReads_below h Op (k4PubG_of Lh hQ)) hT

/-- CONDITIONAL on h, hAP, hm, hx, Lh and hQ. **K4's TIE ON THE INDEX MASKS' ENTRY, AT K1's
OPENING's JOB AND ITS MESSAGE NUMBER 4, AT EACH GROUP.** The law `k4IndexTie_at_join` with hn₀, hn,
hC and hE each had by a call: the head says by which, and what the call for hE is and is not. The
end is that law's: on its getD see that law's docstring. -/
theorem k4IndexTie_at_opening (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O)) (first : ℕ)
    (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    ∀ blk, (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
    ∀ c s mm E ds y cols s', ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp)
        wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
    drawsFit blk.rounds ds = true →
    (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX
        item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
    ∃ cc, lendRow A.B (A.B.rowsOf (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp)
        wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain) (c.look (lettersHead h
        H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX item n₁ n₂ b₀
        Vd Rd Kp w₁).thread.chain) (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens
        look Qp).parts 0 = .ok cc ∧
    ∀ name endName (cp : SumCoins name endName (mergeSum Qp)), SumAt cc (k0 Qp.g + 15) name endName
        (mergeSum Qp) cp →
    K4IndexTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c y.2 s' (Reading.gl.val ((endRun
        cp).getD 0 zeroE)) := by
  have hE : ∀ (c : Coins A.B) w hd y',
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 4
        c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y' :=
    opening_look_idx_at h hAP wit own₀ first Dd rfl Lh.lt
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  have hC := hasCoins_two_at_book h hAP first Dd (Y := Xj) rfl
  rw [eZ, eG] at hx hE hC
  have e : (P5J.At.N Zp cF).index = (1, 0) :=
    VerifiableInference.Desc.K1.index_atAll h Op (VerifiableInference.Desc.K1.pin1_atAll h)
  exact k4IndexTie_at_join h hAP H front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O test carryX
    item n₁ n₂ b₀ Vd Rd Kp w₁ hm hx (openingNos_head h Op).2
    (congrArg (fun s : ℕ × ℕ => P5J.At.arr Zp s.1 s.2) ((index_two h Op).trans e)) hC Said Lh hQ hE

/-- CONDITIONAL on h, hAP, F, hx, Lh and hQ. **THE SAME AT A FIT LIST.** Of F two fields are spent:
msgs, in hm's stead, and coins, which at this job is hC. The statement above asks less of the list.
-/
theorem k4IndexTie_at_opening_fit (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs O)
    (first : ℕ) (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    ∀ blk, (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
    ∀ c s mm E ds y cols s', ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp)
        wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
    drawsFit blk.rounds ds = true →
    (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX
        item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
    ∃ cc, lendRow A.B (A.B.rowsOf (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp)
        wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain) (c.look (lettersHead h
        H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX item n₁ n₂ b₀
        Vd Rd Kp w₁).thread.chain) (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens
        look Qp).parts 0 = .ok cc ∧
    ∀ name endName (cp : SumCoins name endName (mergeSum Qp)), SumAt cc (k0 Qp.g + 15) name endName
        (mergeSum Qp) cp →
    K4IndexTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c y.2 s' (Reading.gl.val ((endRun
        cp).getD 0 zeroE)) := by
  have hE : ∀ (c : Coins A.B) w hd y',
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 4
        c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y' :=
    opening_look_idx_at h hAP wit own₀ first Dd rfl Lh.lt
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  rw [eZ, eG] at hx hE
  have e : (P5J.At.N Zp cF).index = (1, 0) :=
    VerifiableInference.Desc.K1.index_atAll h Op (VerifiableInference.Desc.K1.pin1_atAll h)
  exact k4IndexTie_at_join h hAP H front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O test carryX
    item n₁ n₂ b₀ Vd Rd Kp w₁ F.msgs hx (openingNos_head h Op).2
    (congrArg (fun s : ℕ × ℕ => P5J.At.arr Zp s.1 s.2) ((index_two h Op).trans e)) (F.coins _ hx)
    Said Lh hQ hE

/-- CONDITIONAL on h, hAP, hm, hx, Lh and hQ. **THE SAME TIE WITH ITS END AT `rowSpentGl`.** The law
`k4IndexTie_at_join_coins` with hn₀, hn, hC and hE each had by a call: the head says by which, and
what the call for hE is and is not. cells, weights, tokens and look are letters that neither a
hypothesis nor the end reads: they are handed by hand, as in that law. -/
theorem k4IndexTie_at_opening_coins (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O)) (first : ℕ)
    (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    ∀ blk, (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
    ∀ c s mm E ds y cols s', ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp)
        wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
    drawsFit blk.rounds ds = true →
    (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX
        item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
    ∀ ds' l e l', ledgerAt ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit
        own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s').2 = some l →
    takeEntry l = some (e, l') →
    (rowSpentGl A.B (c.look 0) (k4Place Qp) (k0 Qp.g + 16) 0)[k4Takes Qp.P Qp.hp Qp.g - 1]? = some
        ((h.𝔇.rw13 ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs
        O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s') ((lettersHead h H (joinQ
        cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w₁).thread.wit c y.2.st.input (y.2.st.heard ++ ds'))).mask ⟨((lettersHead h H (joinQ cF.blocksInOrder
        front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w₁).thread.seat c y.2 s').2.out.indexMasks, e⟩) := by
  have hE : ∀ (c : Coins A.B) w hd y',
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 4
        c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y' :=
    opening_look_idx_at h hAP wit own₀ first Dd rfl Lh.lt
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  have hC := hasCoins_two_at_book h hAP first Dd (Y := Xj) rfl
  rw [eZ, eG] at hx hE hC
  have e : (P5J.At.N Zp cF).index = (1, 0) :=
    VerifiableInference.Desc.K1.index_atAll h Op (VerifiableInference.Desc.K1.pin1_atAll h)
  exact k4IndexTie_at_join_coins h hAP H front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O test
    carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hm hx (openingNos_head h Op).2
    (congrArg (fun s : ℕ × ℕ => P5J.At.arr Zp s.1 s.2) ((index_two h Op).trans e)) hC Said Lh cells
    weights tokens look hQ hE

/-- CONDITIONAL on h, hAP, F, hx, Lh and hQ. **THE SAME AT A FIT LIST.** Of F two fields are spent:
msgs, in hm's stead, and coins, which at this job is hC. The statement above asks less of the list.
-/
theorem k4IndexTie_at_opening_coins_fit (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs O)
    (first : ℕ) (Dd : RowDataOf Xi)
    (hx : ((2, placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) :
      ℕ × SendJob (PlaceIn Xi) Xj) ∈ jobs)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    ∀ blk, (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
    ∀ c s mm E ds y cols s', ThrS (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp)
        wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
    drawsFit blk.rounds ds = true →
    (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX
        item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y cols s' →
    ∀ ds' l e l', ledgerAt ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit
        own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s').2 = some l →
    takeEntry l = some (e, l') →
    (rowSpentGl A.B (c.look 0) (k4Place Qp) (k0 Qp.g + 16) 0)[k4Takes Qp.P Qp.hp Qp.g - 1]? = some
        ((h.𝔇.rw13 ((lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs
        O) test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s') ((lettersHead h H (joinQ
        cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w₁).thread.wit c y.2.st.input (y.2.st.heard ++ ds'))).mask ⟨((lettersHead h H (joinQ cF.blocksInOrder
        front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w₁).thread.seat c y.2 s').2.out.indexMasks, e⟩) := by
  have hE : ∀ (c : Coins A.B) w hd y',
      msgTxt 0 wit (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 4
        c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 rawIdxW.owner).2.eAt (rawIdxW.base.e + k4IndexTakes Zp g) = .ok y' :=
    opening_look_idx_at h hAP wit own₀ first Dd rfl Lh.lt
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  rw [eZ, eG] at hx hE
  have e : (P5J.At.N Zp cF).index = (1, 0) :=
    VerifiableInference.Desc.K1.index_atAll h Op (VerifiableInference.Desc.K1.pin1_atAll h)
  exact k4IndexTie_at_join_coins h hAP H front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O test
    carryX item n₁ n₂ b₀ Vd Rd Kp w₁ F.msgs hx (openingNos_head h Op).2
    (congrArg (fun s : ℕ × ℕ => P5J.At.arr Zp s.1 s.2) ((index_two h Op).trans e)) (F.coins _ hx)
    Said Lh cells weights tokens look hQ hE

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_opening
#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_opening_fit
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_opening
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_opening_fit
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_opening_coins
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at_opening_coins_fit
