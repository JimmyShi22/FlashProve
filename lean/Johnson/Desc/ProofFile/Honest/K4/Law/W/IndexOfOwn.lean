-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexOfOwn.lean: CONDITIONAL. Statements with their proofs.

What is here. THE TIE `K4IndexTieAt` (Law/WoTies.lean: the witness's mask entry under the index
masks' next entry is the coin) AS THE TOPS ON THE PENDING ROW's ITEM ASK IT (the hypothesis hIx of
`k4_exchange_wo_head`, Law/WoHead.lean, to the letter) FOLLOWS FROM ONE EQUATION ON THE SCRIPT's
MESSAGES AT PUBLIC NUMBERS (`k4IndexTie_of_own`): message number `k4IndexNum Zp` holds, in its mask
part, at row `k4IndexRow Zp g` and place `k4IndexPlace Zp g` (Lot/IndexNum.lean), the last coin of
the row that the book lends K4's place (`k4IndexTextG`, Lot/IndexTxtG.lean). The equation's form is
`OwnMsgsForm` (Law/W/MaskOfOwn.lean): «own entries of a message». How. Law/W/IndexEntryAt.lean has
the entry's number, row and place from nine facts on a state of the verifier's.
Law/W/IndexFactsThr.lean has the nine wherever the thread with the library's own values stands at a
border at which the item pinI is open, in a link's piece number 2 or later (`indexEntry_border`).
`indexEntry_thr` IS THAT STATEMENT AT THE BORDER IN FRONT OF K4's MEMBER: that pinI is open there
is Johnson/Road/K4/W/PinIFront.lean's. The member's accepted step leaves the statement, the book
and «out» (`kept_atS`, Johnson/Road/K4/KeptAtS.lean): so the same holds at the state behind it, at
which the tie speaks. The coin: the first end coin of the merge's part is the row's coin number
`spentTo` + the first stretch's length (`endRun_seated`), and that is the row's last
(`k4_last_coin`).

  `spentTo_next`, `k4_last_coin`   **the merge's end coin is the last in the list of the coins that
      the row spends.**
  `endRun_seated`   an end coin of a part of the lent row, in the row's list of coins.
  `k4IndexTextG_at`   the text at its one entry.
  `indexEntry_thr`   **the entry as public numbers, where the thread stands in front of the
      member.**
  `k4IndexNum_is`   the message's number, in the letters of the library's table.
  `k4IndexTie_of_own`   **hIx, from the equation on the Script.**

ON THE COIN. `k4_last_coin` (Lean's): the merge's end coin is number `k4Takes` − 1 of the list of
coins that the row spends. A READING, no statement of Lean's: `k4MaskTxt` (Law/W/MaskOfOwn.lean)
reads the numbers j with j + 1 < `k4Takes` of that same list: so, IN ONE GROUP's ROW, the two texts
read no NUMBER of the list twice. WHETHER TWO NUMBERS ARE ONE COIN OF AN OWNER's HANGS ON THE
BOOK's ENTRIES: Bk is a letter: nothing is shown.

Not shown here. THAT ANY SCRIPT MEETS THE EQUATION: O is a hypothesis. THAT THE THREAD HOLDS AT ANY
RUN: where it stands nowhere `indexEntry_thr` and `k4IndexTie_of_own` are empty. The hypotheses of
`k4IndexTie_of_own`, all: h (the library's `P5J.AtMgA` on the public files), `LaidK4`, O, and the
form's two fences met wherever the thread stands in front of the member (hV, hN: at Vq := fun _ =>
True and N := 0 both hold outright). Of h together with `LaidK4`, O, hV and hN no example is known
to us. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has a member
at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own
Limits say what it is worth). `k4IndexTie_of_own` KEEPS THE FORM IN WHICH THE HYPOTHESIS hIx IS
STATED: Qp IS A LETTER THAT NOTHING HERE TIES TO THE GROUP g, no premise says by name that the book
lends the row, and the end begins «lendRow … = .ok cc →». SO: at another group's Qp the statement
holds and speaks of that group's coin at this group's entry · WHERE THE BOOK LENDS NO ROW THE TEXT
SAYS «none», A LAYING BY LOTS (`Script.ofLots`, Honest/Thread/ScriptLots.lean) LAYS ANOTHER LOT's
ANSWER OR 0 THERE, AND THE STATEMENT IS SILENT; so it is where the ledger hands out nothing · THE
FORMS WITH Qp MADE OF THE GROUP's NUMBER AND THE PUBLIC TEST ON THE BOOK BY NAME:
`k4IndexTie_of_ownMsgsG` (Law/W/IndexLotGIs.lean), `k4IndexTie_coinsG` (Law/W/IndexTieCoins.lean) ·
O IS ONE CALL AWAY FROM A LIST OF LOTS (`ofLots_ownMsgs`, Honest/Thread/ScriptLots.lean, through
`ownMsgsForm_iff`, Law/W/MaskAtLots.lean): it is not to be called there. Nothing on any other entry
of the message; that no other member's text answers at this entry is not said here.
THE FULL SIZE ALONE, and the format's second hash function alone. Beneath it stand closed facts by Lean's
own kernel, which no independent checker has replayed (Johnson/Road/K4/W/PinIFront.lean's one; the
library's beneath `nextFits_head`, `below_written` and `seat_at_head`, which
Law/W/IndexFactsThr.lean calls). A program's walk from import to import, which reads import lines
alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*,
stopped at 74 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge: so these counts are lower bounds; it met no module under ThirdParty/ or Johnson/D/. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexFactsThr
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskOfOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTies
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontHead
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCoins
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexTxtG
import Johnson.Road.K4.W.PinIFront
import Johnson.Road.K4.K04Within
import Johnson.Road.K4.K4HeadWritten
import Johnson.P5J.ReadsTestsAtHead
import Johnson.P5J.PlanSitsCore
import Johnson.HB.LLHARD.CountsAtName
import Johnson.HB.LLHARD.ToldCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Road.K4 (AtK4 CellsK kept_atS parOf k4DataWide k4Means_mgWide ledgersFit_of_C
  nextFits_head eAll)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.Rec (nextFitsB)
open OnBytes.Road.K4.W (pinI_front_of_fit k4_pinI_front_full)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit)
open VerifiableInference.Desc.First (S Item pubAll ePubAt ePubAt_mem pubOfItems bookAt pubWide_hand
  openSets start)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K12.Door (msgsOfChain placesBelowB)
open VerifiableInference.Desc.K13.Law (LFull below_written rwBook)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT mgWide MgData WideData mgBase linksFull moreAll
  mgAll_more_base)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open P5J (AtMgA CellsM TS)
open VerifiableInference.Desc.Part.MaskedSum (Ends)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt row_jobs)
open ProofFile.Honest.FirstThread (Script WtF lettersHead foldFacts_thr)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head)
open ProofFile.Honest.K4.Lot (k4IndexRows k4IndexTakes k4IndexRow k4IndexPlace k4IndexNum k4IndexTextG)

/-! ## 1 The coin -/

/-- The coins in front of the next part. CONDITIONAL on h. -/
theorem spentTo_next {V W X : Type} (ps : List (Part V W X)) (i : ℕ) (p : Part V W X)
    (h : ps[i]? = some p) : spentTo ps (i + 1) = spentTo ps i + coinsIn p := by
  unfold spentTo
  rw [List.take_add_one, h]
  simp

/-- **THE MERGE's END COIN IS THE LAST OF THE COINS THAT THE ROW SPENDS.** Public; no hypothesis. -/
theorem k4_last_coin (Q : K4Pub) :
    spentTo (k4RowIn Q) (k0 Q.g + 15) + ownRun (mergeSum Q).shape + 1 =
      k4Takes Q.P Q.hp Q.g := by
  obtain ⟨a, b, hp⟩ := (row_jobs Q).2.2.2.2.2.2
  have len : (k4RowIn Q).length = k0 Q.g + 16 := by
    rw [k4RowIn_all, List.length_append, List.length_replicate]
    rfl
  have e := spentTo_next _ _ _ hp
  rw [sum_coinsIn (V := Unit) a b (mergeSum Q) ⟨1, 1⟩ rfl] at e
  have e' : spentTo (k4RowIn Q) (k0 Q.g + 16) =
      spentTo (k4RowIn Q) (k0 Q.g + 15) + (ownRun (mergeSum Q).shape + 1) := e
  have t := k4_coins_total Q
  rw [len] at t
  omega

section
variable {W₀ Rc Xi Tr X : Type} {cells : Tr → Cells} {weights : W₀ → Weights}
  {tokens : Xi → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}

/-- **The mask entry of end value number e of a part of the lent row is the row's coin number
`spentTo` + the first stretch's length + e.** (Law/FlatCoins.lean's `endRun_spent` has the like at a
row whose parts are not seated.) CONDITIONAL on hcp, hen and he. -/
theorem endRun_seated
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts} {i : ℕ}
    {name endName : String} {J : SumJob K4In Unit} {cp : SumCoins name endName J}
    (hcp : SumAt c i name endName J cp) (en : Ends) (hen : J.shape.ends = some en) (e : ℕ)
    (he : e < en.n) :
    (endRun cp).getD e zeroE =
      (spentOf _ c).getD (spentTo (k4RowIn Q) i + (ownRun J.shape + e)) zeroE := by
  have hsum := sum_coinsIn (V := Unit) name endName J en hen
  have hcoin := k4_coin i (sumPart (V := Unit) name endName J) cp hcp (ownRun J.shape + e)
    (by rw [hsum]; omega)
  have hrun : (runsE ((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends)
      cp.2.1).getD (ownRun J.shape + e) zeroE = (endRun cp).getD e zeroE := by
    have e0 : runsE ((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends) cp.2.1 =
        coinsE cp.2.1.1 ++ runsE (endRuns endName J.shape.ends) cp.2.1.2 := rfl
    have l0 : (coinsE cp.2.1.1).length = ownRun J.shape := by simp [coinsE]
    rw [e0, List.getD_append_right _ _ _ _ (by rw [l0]; omega), l0, Nat.add_sub_cancel_left,
      runsE_ends]
    rfl
  exact (hcoin.trans hrun).symm

end

/-- The text at its one entry. CONDITIONAL on hl. -/
theorem k4IndexTextG_at {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub) (row place : ℕ) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts}
    (hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Qp)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts 0 = .ok c) :
    k4IndexTextG X cells weights tokens look Qp row place k w hd true row place =
      some (Reading.gl.val ((spentOf _ c).getD (k4Takes Qp.P Qp.hp Qp.g - 1) zeroE)) := by
  have hlt : k4Takes Qp.P Qp.hp Qp.g - 1 < (spentOf _ c).length := by
    rw [spent_total cells weights tokens look Qp c]
    have := k4_last_coin Qp
    omega
  unfold k4IndexTextG
  rw [if_pos ⟨rfl, rfl, rfl⟩, hl]
  show ((spentOf _ c)[k4Takes Qp.P Qp.hp Qp.g - 1]?).map Reading.gl.val = _
  rw [List.getElem?_eq_getElem hlt, List.getD_eq_getElem _ _ hlt]
  rfl

/-! ## 2 Where the thread stands -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- The message's number, in the letters of the library's table. CONDITIONAL on h. -/
theorem k4IndexNum_is : k4IndexNum Zp = h.𝔇.arr h.𝔇.N.index.1 h.𝔇.N.index.2 := by
  have e : h.𝔇.N.index = (1, 0) := P5J.index_at_head h.toAtMg
  rw [e]
  rfl

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hT, hl and ht. **WHERE THE THREAD STANDS IN FRONT OF THE MEMBER: THE ENTRY
THAT THE INDEX MASKS' LEDGER HANDS OUT NEXT, AND THE READER's MASK ENTRY THERE, AT PUBLIC NUMBERS.**
z: any public part; w: any witness. -/
theorem indexEntry_thr {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (z : ProofFile.InstPub) (w : WtF) {l l' : Ledger} {c' : ℕ} (hl : ledgerAt s = some l)
    (ht : takeEntry l = some (c', l')) :
    c' = takenNo (k4IndexRows Zp) (k4IndexTakes Zp g) ∧
      (h.𝔇.rw13 (z, s) w).mask ⟨s.out.indexMasks, c'⟩ =
        w.msg (k4IndexNum Zp) true (k4IndexRow Zp g) (k4IndexPlace Zp g) := by
  have A := atK4_of_laid Lh
  have N9 := nine_head h Lh
  have hk := Lh.num
  have hg := Lh.lt
  have hseg := Lh.seg
  have hfit := k4_pinI_front_full
  rw [Bool.and_eq_true] at hfit
  have hbd : k ≤ cF.blocksInOrder.length := by
    have := N9.border
    omega
  subst hseg
  exact indexEntry_border h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A.here A.link
    (by rw [A.piece]; exact Nat.le_succ 2) hbd (by omega) (pinI_front_of_fit A hfit.1) hT z w hl ht

/-- CONDITIONAL on h, Lh, O, hV and hN. **THE HYPOTHESIS hIx OF THE TOPS ON THE PENDING ROW's ITEM,
FROM ONE EQUATION ON THE SCRIPT's MESSAGES AT PUBLIC NUMBERS.** -/
theorem k4IndexTie_of_own
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (O : OwnMsgsForm Q Vq N (k4IndexNum Zp) 0
      (k4IndexTextG X' cells weights tokens look Qp (k4IndexRow Zp g) (k4IndexPlace Zp g)))
    (hV : ∀ c s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E →
      Vq mm.st.input)
    (hN : ∀ c s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E →
      N ≤ mm.st.heard.length) :
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum Qp)),
        lendRow Bk
          (Bk.rowsOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts 0 = .ok cc →
        SumAt cc (k0 Qp.g + 15) name endName (mergeSum Qp) cp →
        K4IndexTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)) := by
  intro blk hb c s mm E ds y cols s' hT _ hS cc name endName cp hlend hcp ds' l c' l' hl ht
  obtain ⟨_, hdec⟩ := k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh blk hb s _ _ s' _
    hS.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := kept_atS hdec
  have hl' : ledgerAt s = some l := by
    have e : ledgerAt s' = some l := hl
    unfold ledgerAt at e ⊢
    rw [hR.st, hR.out] at e
    exact e
  obtain ⟨ei, eh⟩ := moved_state hS.1
  have R := (indexEntry_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT.1
    y.2.st.input.x.pub (Q.wit c y.2.st.input (y.2.st.heard ++ ds')) hl' ht).2
  have eR : h.𝔇.rw13 (y.2.st.input.x.pub, s') (Q.wit c y.2.st.input (y.2.st.heard ++ ds')) =
      h.𝔇.rw13 (y.2.st.input.x.pub, s) (Q.wit c y.2.st.input (y.2.st.heard ++ ds')) := by
    show rwBook h.𝔇.arr h.𝔇.mat13 (_, s') _ = rwBook h.𝔇.arr h.𝔇.mat13 (_, s) _
    unfold rwBook
    dsimp only
    rw [hR.st, hR.book]
  show (h.𝔇.rw13 (y.2.st.input.x.pub, s') (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))).mask
    ⟨s'.out.indexMasks, c'⟩ = _
  rw [eR, hR.out, R, endRun_seated hcp ⟨1, 1⟩ rfl 0 (by decide)]
  have ix : spentTo (k4RowIn Qp) (k0 Qp.g + 15) + (ownRun (mergeSum Qp).shape + 0) =
      k4Takes Qp.P Qp.hp Qp.g - 1 := by
    have := k4_last_coin Qp
    omega
  rw [ix]
  exact O c y.2.st.input (y.2.st.heard ++ ds') (ei ▸ hV c s mm E hT.1)
    (by
      have := hN c s mm E hT.1
      rw [List.length_append, eh, List.length_append]
      omega)
    true _ _ _ (k4IndexTextG_at cells weights tokens look Qp _ _ c _ _ hlend)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.spentTo_next
#print axioms ProofFile.Honest.K4.W.k4_last_coin
#print axioms ProofFile.Honest.K4.W.endRun_seated
#print axioms ProofFile.Honest.K4.W.k4IndexTextG_at
#print axioms ProofFile.Honest.K4.W.k4IndexNum_is
#print axioms ProofFile.Honest.K4.W.indexEntry_thr
#print axioms ProofFile.Honest.K4.W.k4IndexTie_of_own
