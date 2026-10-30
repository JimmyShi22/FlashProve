-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskLotGPub.lean: CONDITIONAL but for the first. Five
statements with their proofs.

What is here. On `k4MaskLotG` (Lot/MaskLotG.lean), the lot of the member of the feed-forward layers'
own rounds (sub-protocol K4) of group g for its segment's mask row, which takes g alone. IT IS NOT
LAID: it is the text, number and fence of a lemma on the lot of the message's sender. (1)
`k4MaskLotG_isSome`: **WHETHER THE LOT ANSWERS IS PUBLIC**: at every run's coins, input and
challenges it answers just where `k4PubG Zp g` returns a Qp, the entry lies inside the fences and
`lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp)` (Honest/Small/LendsRow.lean) is true: a Bool of the book,
the public part, g and the entry. No hypothesis. (2) `k4MaskLotG_alike`: two runs' coins that agree
in the members of `rowSpentGl` … (Honest/Law/Rule/CoinBack.lean) that the text reads give one answer
of the lot at every entry, whatever the inputs and the challenges: `k4MaskTextG_alike`
(Law/W/MaskTxtGPub.lean), whose head says what that hypothesis is, at the lot. (3)
`k4MaskLotG_none`: where the public test says false at whatever `k4PubG Zp g` returns, the lot
answers at no entry; so too where `k4PubG` returns nothing. (4) `k4LotsG_apart`: under h, the
library's hypothesis `P5J.AtMgA` on the public files, two groups' lots bear two message numbers:
numbers that differ, and no more; no file calls it. (5) `k4MaskTie_coinsG`: FROM `OwnMsgs`
(Honest/Thread/ScriptLots.lean, of other writers) AT THE LOT's THREE FIELDS, WITH THE PUBLIC TEST AS
A NAMED HYPOTHESIS hB: wherever the thread with the library's own values stands in front of the
member and the state has the segment's part a, the mask row's entry at a's next slot plus j IS
MEMBER NUMBER j OF `rowSpentGl Bk (c.look 0) (k4Place Qp) (k4RowIn Qp).length 0`, at every j with j
+ 1 below `k4Takes`, which is 3 or more (`k4Takes_three`, Law/W/MaskTxtGIs.lean). hB IS SPENT IN IT:
it pays the clause «the book lends the row» of the tie `K4MaskTieAt` (Law/ScriptAt.lean) at the
stand's own coins; the fence is the plan's number; no look-up with a default, no reading and no
packing stand in its end.

NO LAW AT A LIST OF LOTS IS HERE: at a list that holds a spender's lot and not the whole-message lot
of the message's SENDER the laying lays 0 at the message's other entries, so a law on coins there
says nothing of what is sent. AND (5) ITSELF CAN BE CALLED AT SUCH A LIST: its O follows from
`ofLots_ownMsgs` (Honest/Thread/ScriptLots.lean) at any list that holds the lot and agrees with it,
the list of that one lot among them; it asks nothing of the message's other entries or of its
sender: it is not to be called there.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT is a hypothesis: where the thread stands
nowhere (5) is empty; so it is where the state has no part of the segment. Of h, `LaidK4`, hQ, hB,
O, hT, hV and hN together no example is known to us. That h can hold: the side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). THAT THE PUBLIC TEST
IS TRUE AT ANY BOOK FOR K4's ROW: no such book is known to us; IT STANDS AT THE FIRST CHAIN AND
READS THE BOOK's FIRST TABLE ALONE: it is false at a book that keeps the row of an owner of K4's
runs in another table, and at one that leaves out an entry for a run that a part states with the
count 0. THAT ANY SCRIPT MEETS `OwnMsgs` AT THESE FIELDS. WHERE THE LOT ANSWERS NOTHING, A LAYING BY
LOTS LAYS ANOTHER LOT's ANSWER OR ZERO: (1) says where that is. That the lot agrees with the
sender's lot. Whether two members of a list, or of two groups' lists, are one coin of an owner's
hangs on the book: nothing is shown. THE FULL SIZE ALONE, and the format's second hash function alone, in
(4) and (5). A program's walk from import to import, which reads import lines alone and stops
unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70
modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property. No property is claimed.

  `k4MaskLotG_isSome`   **answers or not: a Bool of the book, the public part, g and the entry**
  `k4MaskLotG_alike`   the same members read, one answer
  `k4MaskLotG_none`   the public test false: no answer anywhere
  `k4LotsG_apart`   two groups, two numbers
  `k4MaskTie_coinsG`   **the entries are members of `rowSpentGl`; the public test by name, and
      spent**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskOfOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskNumsApart
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskTxtGPub
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PubGOf
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskLotG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT seatTab dataQ)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4MaskLotG k4PubG)

/-- **ANSWERS OR NOT IS PUBLIC**: at every run's coins, input and challenges. -/
theorem k4MaskLotG_isSome {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    ((k4MaskLotG X cells weights tokens look Zp g).txt k w hd mask row place).isSome =
      (k4PubG Zp g).any fun Qp =>
        decide (mask = true ∧ row = 0 ∧ Forest.elems (P5J.At.X Zp).y.fo ≤ place ∧
          place + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g) &&
        lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) := by
  show ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X cells weights tokens look Qp
    (Forest.elems (P5J.At.X Zp).y.fo) k w hd mask row place).isSome = _
  cases k4PubG Zp g with
  | none => rfl
  | some Qp => exact k4MaskTextG_isSome cells weights tokens look Qp _ k w hd mask row place

/-- CONDITIONAL on hk. **Two runs' coins that agree in what the text reads give one answer of the
lot**, whatever the inputs and the challenges. -/
theorem k4MaskLotG_alike {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ) {k k' : Coins Bk}
    (hk : ∀ Qp, k4PubG Zp g = some Qp →
      (rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0).take
          (k4Takes Qp.P Qp.hp Qp.g - 1) =
        (rowSpentGl Bk (k'.look 0) (k4Place Qp) (k4RowIn Qp).length 0).take
          (k4Takes Qp.P Qp.hp Qp.g - 1))
    (w w' : Local W₀ Rc Xi Tr) (hd hd' : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    (k4MaskLotG X cells weights tokens look Zp g).txt k w hd mask row place =
      (k4MaskLotG X cells weights tokens look Zp g).txt k' w' hd' mask row place := by
  show ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X cells weights tokens look Qp
      (Forest.elems (P5J.At.X Zp).y.fo) k w hd mask row place) =
    (k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X cells weights tokens look Qp
      (Forest.elems (P5J.At.X Zp).y.fo) k' w' hd' mask row place
  cases hp : k4PubG Zp g with
  | none => rfl
  | some Qp =>
    exact k4MaskTextG_alike cells weights tokens look Qp (hk Qp hp) w w' hd hd' mask row place

/-- CONDITIONAL on hB. **Where the public test says false at what `k4PubG` returns, the lot answers
at no entry**; so too where `k4PubG` returns nothing. -/
theorem k4MaskLotG_none {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ)
    (hB : ∀ Qp, k4PubG Zp g = some Qp → lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) = false)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    (k4MaskLotG X cells weights tokens look Zp g).txt k w hd mask row place = none := by
  show ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X cells weights tokens look Qp
    (Forest.elems (P5J.At.X Zp).y.fo) k w hd mask row place) = none
  cases hp : k4PubG Zp g with
  | none => rfl
  | some Qp =>
    exact k4MaskTextG_none cells weights tokens look Qp (hB Qp hp) _ k w hd mask row place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}

/-- CONDITIONAL on h, hg, hg' and hne. Two groups' lots bear two message numbers. -/
theorem k4LotsG_apart (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {cells cells' : Tr → Cells}
    {weights weights' : W₀ → Weights} {tokens tokens' : ProofFile.Inst → Array Nat}
    {look look' : K4Pub → List Fmt.Drawn → Forest.Heard} {g g' : ℕ} (hg : g < 12) (hg' : g' < 12)
    (hne : g' ≠ g) :
    (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells' weights' tokens' look' Zp g').n ≠
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).n :=
  fun e => hne (maskNum_inj_head h hg' hg e)

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, hB, O, hT, hV and hN. **THE MASK ROW's ENTRIES UNDER THE MEMBER's
SLOTS ARE MEMBERS OF `rowSpentGl`**, from `OwnMsgs` at the lot's three fields. hB pays the
lending. -/
theorem k4MaskTie_coinsG {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) (hB : lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) = true)
    {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (O : OwnMsgs Q Vq N
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).n
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).fx
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).txt)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    ∀ a, segAt? s = some a → ∀ ds j, j + 1 < k4Takes Qp.P Qp.hp Qp.g →
      (rowSpentGl Bk (c.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[j]? =
        some ((dataQ (h.𝔇.N.sent m 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c mm.st.input
            (mm.st.heard ++ ds)))).mask (a.F.next + j)) := by
  intro a ha ds j hj
  have hP := k4PubG_of Lh hQ
  obtain rfl := Lh.seg
  have O' : OwnMsgsForm Q Vq N (maskNumAt Zp (2 * g)) 0
      (k4MaskTxt X' cells weights tokens look Qp (Forest.elems (P5J.At.X Zp).y.fo)) := by
    intro k' w' hd' hv hn mask row place y hy
    refine O k' w' hd' hv hn mask row place y ?_
    show ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X' cells weights tokens look Qp
      (Forest.elems (P5J.At.X Zp).y.fo) k' w' (hd'.take 0) mask row place) = some y
    rw [hP]
    exact hy
  have tie := k4MaskTie_of_own h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ O' hT hV hN
  obtain ⟨cr, hl⟩ := (lendsRow_iff c 0 (k4Place Qp)
    (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts).2
    ((k4_lends_row cells weights tokens look Qp Bk).trans hB)
  have hlen : (spentOf _ cr).length = k4Takes Qp.P Qp.hp Qp.g :=
    spent_total cells weights tokens look Qp cr
  have e0 := tie a cr ha hl ds j (by
    rw [hlen]
    exact hj)
  have eL : (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts.length =
      (k4RowIn Qp).length := List.length_map _
  have e1 : spentOf _ cr = rowSpent Bk (c.look 0) (k4Place Qp) (k4RowIn Qp).length 0 := by
    rw [spent_same, spentOf_row Bk _ _ _ _ 0 cr hl, eL]
  have hj' : j < (spentOf _ cr).length := by
    rw [hlen]
    omega
  rw [← val_rowSpent, List.getElem?_map, ← e1, List.getElem?_eq_getElem hj']
  refine congrArg some ?_
  rw [e0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
  rfl

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskLotG_isSome
#print axioms ProofFile.Honest.K4.W.k4MaskLotG_alike
#print axioms ProofFile.Honest.K4.W.k4MaskLotG_none
#print axioms ProofFile.Honest.K4.W.k4LotsG_apart
#print axioms ProofFile.Honest.K4.W.k4MaskTie_coinsG
