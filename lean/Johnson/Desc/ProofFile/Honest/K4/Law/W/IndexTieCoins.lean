-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexTieCoins.lean: CONDITIONAL. Statements with their
proofs.

What is here. THE TIE ON THE INDEX MASKS' ENTRY OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN
ROUNDS (sub-protocol K4), WITH ITS END SAID AT `rowSpentGl` (Honest/Law/Rule/CoinBack.lean): the
owners' own field elements at the book's entries. `k4IndexTie_of_ownMsgsG` (Law/W/IndexLotGIs.lean)
ends in the form of the hypothesis hIx of `k4_exchange_wo_head` (Law/WoHead.lean): the reader's
mask entry is `(endRun cp).getD 0 zeroE`, read back: a list's reader with a value behind it, under
the premise `SumAt`. Here that end is joined to the list, and the tie is stated in the form of the
mask row's (`k4MaskTie_coinsG`, Law/W/MaskLotGPub.lean).

  `k4_rowSpentGl_lent`, `k4_rowSpentGl_length`   where the book lends K4's row, `rowSpentGl` at K4's
      place and number of parts is the list `spentOf` of what is lent, read back member by member;
      it has just `k4Takes` members.
  `k4_endRun_coin`   **the join**: where the book lends the row and the merge's part is handed cp,
      member number `k4Takes` − 1 of `rowSpentGl` is `(endRun cp).getD 0 zeroE` read back: an
      equation of two values: what that reader returns there is a member of the list; that `endRun
      cp` has a member is not said by it.
  `k4IndexTie_coinsG`   **the tie**: behind the member's step, at that run's own coins, member
      number `k4Takes` − 1 of `rowSpentGl` is the reader's mask entry at the entry that the index
      masks' ledger hands out next. In its end stand no list's reader with a value behind it, no
      reading, no packing, no «lendRow … →» and no `SumAt`: hB pays the lending (`lendsRow_iff`),
      the last clause of `row_jobs` with `sumAt_some` (Law/SlotsOwn.lean) pays `SumAt`.

Not shown here. WHAT STAYS A PREMISE IN THE TIE's END: that the state behind the step has a ledger
of the index masks, and that this ledger hands out an entry: the two of `K4IndexTieAt`
(Law/WoTies.lean). THAT ANY BOOK PASSES hB: it is at chain number 0 and reads the book's first
table alone: false at any book that keeps an owner's row in another table, or that leaves out an
entry for a run that a part states; no such book of the full size is known to us. THAT ANY SCRIPT
MEETS O; O follows from `ofLots_ownMsgs` (Honest/Thread/ScriptLots.lean) at any list that holds the
lot and agrees with it, the list of that one lot among them: no file calls the tie so, it is not to
be called there, AND THE LOT IS NOT LAID: it is the text, number and fence of a lemma on the
sender's lot. WHOSE RUN HOLDS THAT MEMBER: the book's fact: Bk is a letter. That the thread holds
at any run. The hypotheses of the tie, all: h (the library's `P5J.AtMgA` on the public files),
`LaidK4`, hQ, hB, O, hV, hN; of these together no example is known to us. That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what
it is worth). THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). A LAW,
NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexLotGIs

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
open ProofFile.Honest.K4.SlotsOwn (SumAt row_jobs sumAt_some)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4IndexLotG)

/-! ## 1 The list, where the book lends -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} {cells : Tr → Cells} {weights : W₀ → Weights}
  {tokens : Xi → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}

/-- CONDITIONAL on hl. **Where the book lends K4's row, `rowSpentGl` is what is lent to be spent,
read back member by member.** -/
theorem k4_rowSpentGl_lent {k : Coins Bk}
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}
    (hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c) :
    rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0 =
      (spentOf _ c).map Reading.gl.val := by
  have s1 := spent_same _ c
  have s2 := ProofFile.Honest.spentOf_row Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q) _ 0 c hl
  have len : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts.length =
      k0 Q.g + 16 := by
    show ((k4RowIn Q).map _).length = _
    rw [List.length_map, k4RowIn_length]
  rw [← val_rowSpent, ← len, ← s2, ← s1]

/-- CONDITIONAL on hl. There it has just `k4Takes` members. -/
theorem k4_rowSpentGl_length {k : Coins Bk}
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}
    (hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c) :
    (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0).length = k4Takes Q.P Q.hp Q.g := by
  rw [k4_rowSpentGl_lent hl, List.length_map]
  exact spent_total cells weights tokens look Q c

/-- CONDITIONAL on hl and hcp. **THE JOIN: member number k4Takes − 1 of `rowSpentGl` is the first
of the end run that the merge's part is handed, read back.** -/
theorem k4_endRun_coin {k : Coins Bk}
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}
    (hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    {name endName : String} {cp : SumCoins name endName (mergeSum Q)}
    (hcp : SumAt c (k0 Q.g + 15) name endName (mergeSum Q) cp) :
    (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0)[k4Takes Q.P Q.hp Q.g - 1]? =
      some (Reading.gl.val ((endRun cp).getD 0 zeroE)) := by
  have hlt := index_lookup_lt cells weights tokens look Q c
  have ix : spentTo (k4RowIn Q) (k0 Q.g + 15) + (ownRun (mergeSum Q).shape + 0) =
      k4Takes Q.P Q.hp Q.g - 1 := by
    have := k4_last_coin Q
    omega
  rw [k4_rowSpentGl_lent hl, List.getElem?_map, List.getElem?_eq_getElem hlt,
    endRun_seated hcp ⟨1, 1⟩ rfl 0 (by decide), ix, List.getD_eq_getElem _ _ hlt]
  rfl

end

/-! ## 2 The tie -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, hB, O, hV and hN. **BEHIND THE MEMBER's STEP, AT THAT RUN's OWN COINS:
MEMBER NUMBER k4Takes − 1 OF WHAT THE BOOK's ENTRIES HAND K4's ROW TO SPEND IS THE READER's MASK
ENTRY AT THE ENTRY THAT THE INDEX MASKS' LEDGER HANDS OUT NEXT.** -/
theorem k4IndexTie_coinsG
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (hB : lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) = true)
    {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (O : OwnMsgs Q Vq N
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).n
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).fx
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).txt)
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
      ∀ ds' l e l',
      ledgerAt ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2
        s').2 = some l →
      takeEntry l = some (e, l') →
      (rowSpentGl Bk (c.look 0) (k4Place Qp) (k0 Qp.g + 16) 0)[k4Takes Qp.P Qp.hp Qp.g - 1]? =
        some ((h.𝔇.rw13
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s')
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c y.2.st.input
            (y.2.st.heard ++ ds'))).mask
          ⟨((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2
            s').2.out.indexMasks, e⟩) := by
  intro blk hb c s mm E ds y cols s' hT hd hS ds' l e l' hl ht
  obtain ⟨cc, hcc, tie⟩ := (k4IndexTie_of_ownMsgsG h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said
    Lh hQ hB O hV hN).2 blk hb c s mm E ds y cols s' hT hd hS
  obtain ⟨a, b, hp⟩ := (row_jobs Qp).2.2.2.2.2.2
  obtain ⟨cp, hcp⟩ := sumAt_some cc (k0 Qp.g + 15) a b (mergeSum Qp) hp
  have t := tie a b cp hcp ds' l e l' hl ht
  have v := k4_endRun_coin hcc hcp
  rw [← t] at v
  exact v

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_rowSpentGl_lent
#print axioms ProofFile.Honest.K4.W.k4_rowSpentGl_length
#print axioms ProofFile.Honest.K4.W.k4_endRun_coin
#print axioms ProofFile.Honest.K4.W.k4IndexTie_coinsG
