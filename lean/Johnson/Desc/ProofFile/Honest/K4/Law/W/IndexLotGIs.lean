-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexLotGIs.lean: CONDITIONAL where a hypothesis is named.
Statements with their proofs.

What is here. LAWS ON THE LOT OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol
K4) FOR ITS ENTRY OF THE INDEX MASKS' MESSAGE (`k4IndexTextG`, Lot/IndexTxtG.lean; `k4IndexLotG`,
Lot/IndexLotG.lean): whether it answers; what it answers; and the tie on that entry from `OwnMsgs`
at its three fields. The lot's public data are made of the group's number (`k4PubG_fields`,
`k4PubG_place`, Law/W/PubGOf.lean).

  `k4RowIn_length`   K4's row has `k0 Q.g + 16` parts: the number of parts at which `rowSpentGl` is
      read here; the mask row's laws write it `(k4RowIn Q).length`.
  `index_lookup_lt`, `index_lookup_some`   **the look-up in the text returns**, at every row of
      coins: no hypothesis. (`k4Takes` is never 0: `k4_last_coin`; the list has that length:
      `spent_total`.)
  `k4IndexTextG_isSome`   **WHETHER THE TEXT ANSWERS IS PUBLIC**: the entry's fence and the Bool
      `lendsRow Bk 0 (k4Place Q) (k4RowIn Q)` (Honest/Small/LendsRow.lean; Law/W/LendsK4.lean), a
      Bool of the book and the member's public data: no coins and no input on the right: no
      hypothesis.
  `k4IndexTextG_coin`   **WHERE THE TEXT ANSWERS, ITS VALUE IS MEMBER NUMBER `k4Takes` − 1 OF
      `rowSpentGl`** (Honest/Law/Rule/CoinBack.lean): the owners' own field elements at the book's
      entries: on the right stand the book, the coins' look, the place, two numbers of the plan: no
      reader of the input, no packing, no reading.
  `k4IndexTextG_none`   a tooth: where the Bool is false the text says «none» at every entry.
  `k4IndexLotG_txt`   where `k4PubG` returns, the lot's text is the text at what it returns.
  `k4IndexLotG_isSome`, `k4IndexLotG_none`   **the first and the tooth AT THE LOT**: a Bool of the
      book, the public part, the group's number and the entry: no hypothesis on `k4PubG`.
  `k4IndexLotG_answers`   under hP and hB the lot answers at its entry at every run's coins.
  `k4IndexTie_of_ownMsgsG`   **the tie on the entry from `OwnMsgs` at the three fields of the lot,
      WITH hB BY NAME AND SPENT IN BOTH HALVES**: the lot answers at every run's coins; and behind
      the member's step THE BOOK's LENDING RETURNS, at that run's coins, and at what it returns the
      tie holds: the premise «lendRow … = .ok cc →» of `k4IndexTie_of_own` (Law/W/IndexOfOwn.lean)
      is paid by hB (`lendsRow_iff`).

THE LOT IS NOT LAID: it is the text, number and fence of a lemma on the lot of the message's
sender. NO LAW AT A LIST OF LOTS IS HERE, NOR ANYWHERE BESIDE IT. BUT `k4IndexTie_of_ownMsgsG` IS
ONE CALL AWAY FROM ONE: its hypothesis O follows from `ofLots_ownMsgs`
(Honest/Thread/ScriptLots.lean) at ANY list that holds the lot and agrees with it, the list of that
one lot among them; the tie asks nothing of the message's other entries or of its sender: it is not
to be called there. Law/W/IndexTieCoins.lean alone calls it.

Not shown here. THAT ANY BOOK PASSES THE TEST hB: IT IS AT CHAIN NUMBER 0 AND READS THE BOOK's
FIRST TABLE ALONE: it is false at any book that keeps an owner's row in another table, and at any
book that leaves out an entry for a run that a part states, be its count 0; no such book of the
full size is known to us. THAT ANY SCRIPT MEETS O. THAT A SCRIPT LAID BY LOTS IS WHAT THE HONEST
PROVER SENDS is said nowhere. THAT THE THREAD HOLDS AT ANY RUN: where it stands nowhere the tie's
second half is empty. The hypotheses of the tie, all: h (the library's `P5J.AtMgA` on the public
files), `LaidK4`, hQ, hB, O, hV and hN; of these together no example is known to us. Whether two
members of `rowSpentGl`, of one row or of two, are one coin of an owner's: that hangs on the book's
entries: Bk is a letter. That the lot agrees with the sender's lot, or with another kind's at this
message. Where the text says «none» a laying by lots (`Script.ofLots`) lays another lot's answer or
0. THE TIE's VALUE IS SAID IN THE FORM OF THE HYPOTHESIS hIx OF `k4_exchange_wo_head`
(Law/WoHead.lean), `(endRun cp).getD 0 zeroE` read back: a list's reader with a value behind it;
that it is the member that the text reads, and the tie with its end said at `rowSpentGl`:
Law/W/IndexTieCoins.lean. THE PREMISE `SumAt` IN THE TIE's END IS NOT IDLE AND NOT EMPTY:
`sumAt_some` (Law/SlotsOwn.lean) hands a cp at every cc where the row has that part, which the last
clause of `row_jobs` (that file) gives: Law/W/IndexTieCoins.lean joins them. The length of
`rowSpentGl`, where the book lends: that file. That h can hold: the side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Where h stands:
THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one. Nothing on soundness,
on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexLotG
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexOfOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PubGOf
import Johnson.Desc.ProofFile.Honest.Law.Rule.CoinBack
import Johnson.Desc.ProofFile.Honest.K4.Law.TieIs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LendsK4

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
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4IndexRow k4IndexPlace k4IndexTextG k4IndexLotG k4PubG)

/-! ## 1 The text -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)

/-- K4's row has so many parts. No hypothesis. -/
theorem k4RowIn_length : (k4RowIn Q).length = k0 Q.g + 16 := by
  rw [k4RowIn_all, List.length_append, List.length_replicate]
  rfl

/-- The number that the text reads is below the list's length. No hypothesis. -/
theorem index_lookup_lt
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts) :
    k4Takes Q.P Q.hp Q.g - 1 < (spentOf _ c).length := by
  have hl := spent_total cells weights tokens look Q c
  have h1 := k4_last_coin Q
  rw [hl]
  omega

/-- **THE LOOK-UP IN THE TEXT RETURNS**, at every row of coins. No hypothesis. -/
theorem index_lookup_some
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts) :
    ((spentOf _ c)[k4Takes Q.P Q.hp Q.g - 1]?).isSome = true := by
  rw [List.getElem?_eq_getElem (index_lookup_lt cells weights tokens look Q c)]
  rfl

/-- **WHETHER THE TEXT ANSWERS IS PUBLIC**: the entry's fence, and whether the book lends K4's
public row: no coins and no input on the right. No hypothesis. -/
theorem k4IndexTextG_isSome (row place : ℕ) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) (mask : Bool) (r p : ℕ) :
    (k4IndexTextG X cells weights tokens look Q row place k w hd mask r p).isSome =
      (decide (mask = true ∧ r = row ∧ p = place) && lendsRow Bk 0 (k4Place Q) (k4RowIn Q)) := by
  have e := lendRow_isSome k 0 (k4Place Q)
    (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts
  rw [k4_lends_row cells weights tokens look Q Bk] at e
  unfold k4IndexTextG
  by_cases hc : mask = true ∧ r = row ∧ p = place
  · rw [if_pos hc, decide_eq_true hc, Bool.true_and, ← e]
    cases lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 with
    | error er => rfl
    | ok c =>
      show (((spentOf _ c)[k4Takes Q.P Q.hp Q.g - 1]?).map Reading.gl.val).isSome = true
      rw [Option.isSome_map]
      exact index_lookup_some cells weights tokens look Q c
  · rw [if_neg hc, decide_eq_false hc, Bool.false_and]
    rfl

/-- A tooth: where the book does not lend K4's public row the text says «none» at every entry.
CONDITIONAL on hB. -/
theorem k4IndexTextG_none (hB : lendsRow Bk 0 (k4Place Q) (k4RowIn Q) = false) (row place : ℕ)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r p : ℕ) :
    k4IndexTextG X cells weights tokens look Q row place k w hd mask r p = none := by
  have e := k4IndexTextG_isSome (X := X) cells weights tokens look Q row place k w hd mask r p
  rw [hB, Bool.and_false] at e
  cases h : k4IndexTextG X cells weights tokens look Q row place k w hd mask r p with
  | none => rfl
  | some y =>
    rw [h] at e
    cases e

/-- **WHERE THE TEXT ANSWERS, ITS VALUE IS NUMBER k4Takes − 1 OF THE OWNERS' OWN FIELD ELEMENTS THAT
THE BOOK's ENTRIES HAND K4's ROW TO SPEND.** No reader of the input, no packing and no reading on
the right. CONDITIONAL on e. -/
theorem k4IndexTextG_coin {row place : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {mask : Bool} {r p : ℕ} {y : Cb.Gl.E}
    (e : k4IndexTextG X cells weights tokens look Q row place k w hd mask r p = some y) :
    (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0)[k4Takes Q.P Q.hp Q.g - 1]? = some y := by
  unfold k4IndexTextG at e
  split at e
  · cases hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 with
    | error er =>
      rw [hl] at e
      have e0 : (none : Option Cb.Gl.E) = some y := e
      cases e0
    | ok c =>
      rw [hl] at e
      have e' : ((spentOf _ c)[k4Takes Q.P Q.hp Q.g - 1]?).map Reading.gl.val = some y := e
      have s1 := spent_same _ c
      have s2 := ProofFile.Honest.spentOf_row Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q) _ 0 c hl
      have len : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts.length =
          k0 Q.g + 16 := by
        show ((k4RowIn Q).map _).length = _
        rw [List.length_map, k4RowIn_length]
      rw [← val_rowSpent, List.getElem?_map, ← len, ← s2, ← s1]
      exact e'
  · cases e

end

/-! ## 2 The lot -/

/-- Where `k4PubG` returns, the lot's text is the text at what it returns. CONDITIONAL on hP. -/
theorem k4IndexLotG_txt {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) :
    (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt =
      k4IndexTextG X cells weights tokens look Qp (k4IndexRow Zp g) (k4IndexPlace Zp g) := by
  unfold k4IndexLotG
  rw [hP]
  rfl

/-- CONDITIONAL on hP and hB. **UNDER THE PUBLIC TEST ON THE BOOK THE LOT ANSWERS AT ITS ENTRY, AT
EVERY RUN's COINS.** -/
theorem k4IndexLotG_answers {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) (hB : lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) = true)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) :
    ((k4IndexLotG X cells weights tokens look Zp g).txt k w hd true (k4IndexRow Zp g)
      (k4IndexPlace Zp g)).isSome = true := by
  rw [k4IndexLotG_txt cells weights tokens look hP, k4IndexTextG_isSome, hB,
    decide_eq_true ⟨rfl, rfl, rfl⟩]
  rfl

/-- **WHETHER THE LOT ANSWERS IS PUBLIC**: a Bool of the book, the public part, the group's number
and the entry: no coins and no input on the right. No hypothesis. -/
theorem k4IndexLotG_isSome {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r p : ℕ) :
    ((k4IndexLotG X cells weights tokens look Zp g).txt k w hd mask r p).isSome =
      (k4PubG Zp g).any fun Qp =>
        decide (mask = true ∧ r = k4IndexRow Zp g ∧ p = k4IndexPlace Zp g) &&
          lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) := by
  show ((k4PubG Zp g).bind fun Qp =>
    k4IndexTextG X cells weights tokens look Qp (k4IndexRow Zp g) (k4IndexPlace Zp g) k w hd mask r
      p).isSome = _
  cases k4PubG Zp g with
  | none => rfl
  | some Qp =>
    exact k4IndexTextG_isSome cells weights tokens look Qp (k4IndexRow Zp g) (k4IndexPlace Zp g) k
      w hd mask r p

/-- A tooth, at the lot: where the book does not lend the public row of what `k4PubG` returns, or
`k4PubG` returns nothing, the lot says «none» at every entry. CONDITIONAL on hB. -/
theorem k4IndexLotG_none {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ)
    (hB : ∀ Qp, k4PubG Zp g = some Qp → lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) = false)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r p : ℕ) :
    (k4IndexLotG X cells weights tokens look Zp g).txt k w hd mask r p = none := by
  show ((k4PubG Zp g).bind fun Qp =>
    k4IndexTextG X cells weights tokens look Qp (k4IndexRow Zp g) (k4IndexPlace Zp g) k w hd mask r
      p) = none
  cases hP : k4PubG Zp g with
  | none => rfl
  | some Qp =>
    exact k4IndexTextG_none cells weights tokens look Qp (hB Qp hP) (k4IndexRow Zp g)
      (k4IndexPlace Zp g) k w hd mask r p

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, hB, O, hV and hN. **UNDER THE PUBLIC TEST ON THE BOOK, BY NAME: THE
LOT ANSWERS AT ITS ENTRY AT EVERY RUN's COINS; AND BEHIND THE MEMBER's STEP THE BOOK's LENDING
RETURNS AT THAT RUN's COINS, AND AT WHAT IT RETURNS THE TIE ON THE ENTRY HOLDS**, from `OwnMsgs` at
the three fields of the lot. -/
theorem k4IndexTie_of_ownMsgsG
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
    (∀ (c : Coins Bk) (w : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn),
      ((k4IndexLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).txt c w hd true
        (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true) ∧
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∃ cc,
        lendRow Bk
          (Bk.rowsOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts 0 = .ok cc ∧
        ∀ name endName (cp : SumCoins name endName (mergeSum Qp)),
        SumAt cc (k0 Qp.g + 15) name endName (mergeSum Qp) cp →
        K4IndexTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)) := by
  refine ⟨k4IndexLotG_answers cells weights tokens look (k4PubG_of Lh hQ) hB, ?_⟩
  rw [k4IndexLotG_txt cells weights tokens look (k4PubG_of Lh hQ)] at O
  intro blk hb c s mm E ds y cols s' hT hd hS
  obtain ⟨cc, hcc⟩ := (lendsRow_iff c 0 (k4Place Qp)
    (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts).2
    ((k4_lends_row cells weights tokens look Qp Bk).trans hB)
  exact ⟨cc, hcc, fun name endName cp hA =>
    k4IndexTie_of_own h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh O hV hN blk hb c s mm E
      ds y cols s' hT hd hS cc name endName cp hcc hA⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4RowIn_length
#print axioms ProofFile.Honest.K4.W.index_lookup_lt
#print axioms ProofFile.Honest.K4.W.index_lookup_some
#print axioms ProofFile.Honest.K4.W.k4IndexTextG_isSome
#print axioms ProofFile.Honest.K4.W.k4IndexTextG_none
#print axioms ProofFile.Honest.K4.W.k4IndexTextG_coin
#print axioms ProofFile.Honest.K4.W.k4IndexLotG_txt
#print axioms ProofFile.Honest.K4.W.k4IndexLotG_answers
#print axioms ProofFile.Honest.K4.W.k4IndexLotG_isSome
#print axioms ProofFile.Honest.K4.W.k4IndexLotG_none
#print axioms ProofFile.Honest.K4.W.k4IndexTie_of_ownMsgsG
