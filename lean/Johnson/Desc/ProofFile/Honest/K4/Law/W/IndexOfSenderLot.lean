-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexOfSenderLot.lean: CONDITIONAL. Statements with their
proofs.

What is here. THE LEMMA ON THE SENDER's LOT, FOR THE ONE ENTRY OF THE INDEX MASKS' MESSAGE THAT THE
MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) OF GROUP g READS: `OwnMsgs`
(Honest/Thread/ScriptLots.lean) at the three fields of K4's lot `k4IndexLotG` (Lot/IndexLotG.lean)
FOLLOWS FROM `OwnMsgs` AT THE LOT OF THE MESSAGE's SENDER, under a public test on the book
(`K4LastEntry`, Law/W/LastEntry.lean) and two sentences on the sender's text. K4's lot is not laid:
it is the text, number and fence of this lemma. No list of lots stands in any statement here.

  `k4_rowSpentGl_takes`   under the test `rowSpentGl` at K4's place has just `k4Takes` members: off
      the public row: no reader of the input stands in the statement or in its proof.
  `k4_last_is_owners`   **WHOSE THE MEMBER IS**: under the test, at every run's coins: member number
      `k4Takes` − 1 of `rowSpentGl`, which is what K4's text reads (`k4IndexTextG_coin`,
      Law/W/IndexLotGIs.lean), IS THERE, AND IS ELEMENT NUMBER eL.start.e OF WHAT THE RUN HOLDS AT
      eL's OWNER: «there is y, both».
  `k4_last_of_member`   the same as an implication from the list's member.
  `k4IndexOwn_of_senderLot`   **THE LEMMA.** The library's hypothesis h on the public files,
      `LaidK4`, a thread and a state of the verifier do not stand in it; hP, hn and the entry are
      premises on the public part Zp.
  `k4IndexTie_of_senderLot`   the end of `k4IndexTie_coinsG` (Law/W/IndexTieCoins.lean), to the
      letter, from the sender's lot: a member of `rowSpentGl` is the reader's mask entry: WITH
      `k4_last_is_owners`, THIS IS WHAT BEARS THE LOCK.
  `k4Index_owner_is_entry`   **the sender's sentence meets the verifier's reader**: behind the
      member's step, at that run's own coins: the element that hE names is the reader's mask entry
      at the entry that the index masks' ledger hands out next. NO TEST ON THE BOOK STANDS IN IT,
      and no public data of K4's member: the address and the number in hE are letters there: SO IT
      IS NO TEST THAT LOCK AND KEY FIT.

THE SENDER's LOT STANDS AS THREE LETTERS: nS (its number), fS, tS (its text): so `OwnMsgs` can be
handed in whichever form the sender's authors have it. WHERE THEIR LEMMA GIVES THE SENDER's MESSAGE
UNDER «there is», hA AND hE MUST BE HAD AT THAT SAME MESSAGE. THE TWO SENTENCES ON THE SENDER's
TEXT, tS, at K4's entry (the mask part; row `k4IndexRow Zp g`; place `k4IndexPlace Zp g`): hA: it
answers, at every run's coins, WHERE `OwnMsgs` ITSELF SPEAKS AND NO WIDER: at each input that Vq
lets by, at the first fS of at least N challenges (a sender's text may answer under a public test
on the input alone) · hE: what it answers is element number eL.start.e of what the run holds at
eL's owner (`Cs.eAt`, Honest/Frame.lean, which refuses beyond the count: no packing, no reading, no
value that stands in). hA IS THE SENDER's AUTHORS' TO SHOW. hE IS NOT THEIRS ALONE: it names eL,
THE BOOK's entry for K4's merge: what they can show is which element of their own coins the entry
holds; that eL names that owner and that number is the book's makers'. (On the mask row's side hE
holds the sender's own letters: the two sides are not alike here.)

THE ONE EQUATION THAT JOINS LOCK AND KEY LIES FOLDED INSIDE hE, WHICH NAMES eL AND THE ENTRY
TOGETHER; IT HAS TWO HALVES: eL.owner = ‹the sender's own address› · eL.start.e = ‹where the
sender's coins for this message's mask rows begin› + ‹the number of K4's entry in the sender's own
order›. THE FIRST HALF IS AS UNSHOWN AS THE SECOND, and it is what makes the coin the sender's. THE
VERIFIER's SIDE OF THE SECOND IS HAD, under h, at a stand of the thread, at the full size: the
entry is number t := `k4IndexTakes Zp g` of the ledger's order (row t % rows, place t / rows, by
the definitions in Lot/IndexNum.lean; that the ledger in front of the member is that of just t
takes: `indexEntry_border`, `indexLedger_border`, Law/W/IndexFactsThr.lean). THE BOOK's MAKER's
SIDE, that the entry for K4's g-th merge starts at that base plus t, IS A FACT ON THE WRITTEN
DESCRIPTION THAT IS NOT SHOWN.

ONE LETTER Vq SERVES THREE USES in the two statements on the thread: hA wants it narrow (the
inputs at which the sender's text answers), OS has it at the letter of whoever shows `OwnMsgs`, hV
wants it wide (every input at a stand of the thread): SO THEY ASK THAT AT A STAND OF THE THREAD THE
INPUT PASSES THE SENDER's PUBLIC TEST: that is not shown.

THREE KINDS' PARTS READ THIS MESSAGE. That no two entries of the book hand one element to two of
them is the book's own test («once»): not here: the frame's authors' law for two parts at two
addresses (Honest/BookApart.lean), under «the book passes its own tests»; K4's calls of it, among
K4's own twelve: Law/W/RowsApart.lean, Law/W/LastsApart.lean (`k4Lasts_apart`); against the two
other kinds' parts: theirs.

Not shown here. THAT ANY BOOK OF THE FULL SIZE MEETS `K4LastEntry`: its limits bind here (chain
number 0; the book's first table alone); at a small made-up plan and book it has a member by
evaluation (Law/W/LastEntryToy.lean). ITS FIELD lends COMPARES THE BOOK WITH WHAT K4's OWN PARTS
STATE (names, counts, order, lengths): no fact on the book alone gives it: it is K4's authors' to
show, and nobody has. THAT ANY SENDER's TEXT MEETS hA AND hE; THAT ANY SCRIPT MEETS OS; that the
sender's lot bears K4's number (hn): under the library's hypothesis that number is the library's
own at the index masks' seat (`k4IndexNum_is`, Law/W/IndexOfOwn.lean). Of the hypotheses together
no example is known to us. THE LAST TWO STATEMENTS ARE EMPTY WHERE THE THREAD STANDS NOWHERE IN
FRONT OF THE MEMBER, where its step is not taken, where the state behind it has no ledger of the
index masks, or where that ledger hands out nothing. Where h stands (these two): that h can hold:
the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what
it is worth); THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). A LAW,
NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LastEntry
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexTieCoins

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
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head)
open OnBytes.Road.K4 (kept_atS)
open VerifiableInference.Desc.K13.Law (rwBook)
open ProofFile.Honest.K4.Lot (k4IndexLotG k4IndexTextG k4IndexNum k4IndexRow k4IndexPlace k4PubG)

/-! ## 1 Whose the member is -/

section
variable {Bk : ProverCoinCounts} {Q : K4Pub} {es₁ : List Ahead} {eL : Ahead}

/-- CONDITIONAL on K. Under the test the list has just `k4Takes` members: off the public row; no
reader of the input stands in the statement or in the proof. -/
theorem k4_rowSpentGl_takes (K : K4LastEntry Bk Q es₁ eL) (k : Coins Bk) :
    (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0).length = k4Takes Q.P Q.hp Q.g := by
  obtain ⟨c, hl⟩ := (lendsRow_iff k 0 (k4Place Q) (k4RowIn Q)).2 K.lends
  have s1 := spent_same _ c
  have s2 := ProofFile.Honest.spentOf_row Bk (Bk.rowsOf 0) (k.look 0) (k4Place Q) _ 0 c hl
  rw [← k4RowIn_length Q, ← val_rowSpent, List.length_map, ← s2, ← s1, spentOf_length]
  exact k4_coins_total Q

/-- CONDITIONAL on K. **THE MEMBER THAT K4's TEXT READS IS THERE, AND IS ELEMENT NUMBER eL.start.e
OF WHAT THE RUN HOLDS AT eL's OWNER.** -/
theorem k4_last_is_owners (K : K4LastEntry Bk Q es₁ eL) (k : Coins Bk) :
    ∃ y, (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0)[k4Takes Q.P Q.hp Q.g - 1]? =
        some y ∧
      (k.look 0 eL.owner).2.eAt eL.start.e = .ok y := by
  have hlen := k4_rowSpentGl_takes K k
  have hpos := k4_last_coin Q
  have hf : eL.start.e < (k.look 0 eL.owner).1.e := by
    rw [look_dueIs k 0 eL.owner]
    have := K.fits
    omega
  have hs : sliceGl (k.look 0) eL = [(k.look 0 eL.owner).2.e ⟨eL.start.e, hf⟩] := by
    unfold sliceGl
    have hn : eL.start.e < (List.ofFn (k.look 0 eL.owner).2.e).length := by
      rw [List.length_ofFn]
      exact hf
    rw [K.one, List.drop_eq_getElem_cons hn, List.take_succ_cons, List.take_zero,
      List.getElem_ofFn]
  have he : rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0 =
      es₁.flatMap (sliceGl (k.look 0)) ++ [(k.look 0 eL.owner).2.e ⟨eL.start.e, hf⟩] := by
    rw [rowSpentGl_entries, ← k4RowIn_length Q, K.ents, List.flatMap_append, ← hs]
    show _ ++ (sliceGl (k.look 0) eL ++ []) = _
    rw [List.append_nil]
  have la : (es₁.flatMap (sliceGl (k.look 0))).length = k4Takes Q.P Q.hp Q.g - 1 := by
    rw [he, List.length_append, List.length_singleton] at hlen
    omega
  refine ⟨(k.look 0 eL.owner).2.e ⟨eL.start.e, hf⟩, ?_, ?_⟩
  · rw [he, ← la, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · unfold Cs.eAt
    rw [dif_pos hf]

/-- CONDITIONAL on K and e. The same as an implication from the list's member. -/
theorem k4_last_of_member (K : K4LastEntry Bk Q es₁ eL) (k : Coins Bk) {y : Cb.Gl.E}
    (e : (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0)[k4Takes Q.P Q.hp Q.g - 1]? =
      some y) :
    (k.look 0 eL.owner).2.eAt eL.start.e = .ok y := by
  obtain ⟨y', h1, h2⟩ := k4_last_is_owners K k
  rw [h1] at e
  obtain rfl := Option.some.inj e
  exact h2

end

/-! ## 2 The lemma -/

/-- CONDITIONAL on hP, K, hn, hA, hE and OS. **`OwnMsgs` AT THE THREE FIELDS OF K4's LOT, FROM
`OwnMsgs` AT THE SENDER's LOT.** nS, fS, tS: the three fields of the sender's lot for the whole
message: its number, after how many challenges its text changes no more, its text. -/
theorem k4IndexOwn_of_senderLot {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X CellsT Tok : Type}
    (Q : Script Bk (Local W₀ Rc Xi Tr) CellsT Tok MsgT) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) {es₁ : List Ahead} {eL : Ahead}
    (K : K4LastEntry Bk Qp es₁ eL) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4IndexNum Zp) {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (tS k w (hd.take fS) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
    (hE : ∀ k w hd y', tS k w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (k.look 0 eL.owner).2.eAt eL.start.e = .ok y')
    (OS : OwnMsgs Q Vq N nS fS tS) :
    OwnMsgs Q Vq N
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).n
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt := by
  intro k w hd hv hN mask r p y ht
  rw [k4IndexLotG_txt cells weights tokens look hP] at ht
  have hs := k4IndexTextG_isSome (X := X) cells weights tokens look Qp (k4IndexRow Zp g)
    (k4IndexPlace Zp g) k w
    (hd.take (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx)
    mask r p
  rw [ht] at hs
  have hfence : mask = true ∧ r = k4IndexRow Zp g ∧ p = k4IndexPlace Zp g := by
    by_cases hc : mask = true ∧ r = k4IndexRow Zp g ∧ p = k4IndexPlace Zp g
    · exact hc
    · rw [decide_eq_false hc, Bool.false_and] at hs
      cases hs
  obtain ⟨rfl, rfl, rfl⟩ := hfence
  have hy := k4_last_of_member K k
    (k4IndexTextG_coin cells weights tokens look Qp ht)
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 (hA k w hd hv hN)
  have e2 := hE k w (hd.take fS) y' hy'
  rw [hy] at e2
  obtain rfl := Except.ok.inj e2
  have o := OS k w hd hv hN true (k4IndexRow Zp g) (k4IndexPlace Zp g) y hy'
  rw [hn] at o
  exact o

/-! ## 3 The key turned -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, K, hn, hA, hE, OS, hV and hN, and on what stands in front of its end:
the thread stands in front of the member, the member's step is taken, the state behind it has a
ledger of the index masks, and that ledger hands out an entry; where these hold nowhere it is empty.
**THE END OF `k4IndexTie_coinsG`, FROM THE SENDER's LOT.** The four readers cells, weights, tokens,
look stand in no hypothesis and not in the end: they serve the proof alone; whoever calls names
them. -/
theorem k4IndexTie_of_senderLot
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {es₁ : List Ahead} {eL : Ahead}
    (K : K4LastEntry Bk Qp es₁ eL) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4IndexNum Zp) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ c w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (tS c w (hd.take fS) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
    (hE : ∀ c w hd y', tS c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 eL.owner).2.eAt eL.start.e = .ok y')
    (OS : OwnMsgs Q Vq N nS fS tS)
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
            s').2.out.indexMasks, e⟩) :=
  k4IndexTie_coinsG h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh hQ K.lends
    (k4IndexOwn_of_senderLot Q cells weights tokens look (k4PubG_of Lh hQ) K nS fS tS hn hA hE OS)
    hV hN

/-! ## 4 The sender's sentence meets the verifier's reader: no test on the book -/

/-- CONDITIONAL on h, Lh, hn, hA, hE, OS, hV and hN, and on what stands in front of its end, as
above. **BEHIND THE MEMBER's STEP, AT THAT RUN's OWN COINS: THE ELEMENT THAT THE SENDER's SENTENCE
NAMES IS THE READER's MASK ENTRY AT THE ENTRY THAT THE INDEX MASKS' LEDGER HANDS OUT NEXT.** o, s₀:
the address and the number that hE names: letters. NO TEST ON THE BOOK STANDS IN IT, and no public
data of K4's member: so it is no test that lock and key fit. -/
theorem k4Index_owner_is_entry
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4IndexNum Zp) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ c w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (tS c w (hd.take fS) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
    {o : Addr} {s₀ : ℕ}
    (hE : ∀ c w hd y', tS c w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (c.look 0 o).2.eAt s₀ = .ok y')
    (OS : OwnMsgs Q Vq N nS fS tS)
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
      (c.look 0 o).2.eAt s₀ =
        .ok ((h.𝔇.rw13
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s')
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c y.2.st.input
            (y.2.st.heard ++ ds'))).mask
          ⟨((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2
            s').2.out.indexMasks, e⟩) := by
  intro blk hb c s mm E ds y cols s' hT _ hS ds' l e l' hl ht
  obtain ⟨_, hdec⟩ := k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh blk hb s _ _ s' _
    hS.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := kept_atS hdec
  have hl' : ledgerAt s = some l := by
    have e0 : ledgerAt s' = some l := hl
    unfold ledgerAt at e0 ⊢
    rw [hR.st, hR.out] at e0
    exact e0
  obtain ⟨ei, eh⟩ := moved_state hS.1
  have R := (indexEntry_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT.1
    y.2.st.input.x.pub (Q.wit c y.2.st.input (y.2.st.heard ++ ds')) hl' ht).2
  have eR : h.𝔇.rw13 (y.2.st.input.x.pub, s') (Q.wit c y.2.st.input (y.2.st.heard ++ ds')) =
      h.𝔇.rw13 (y.2.st.input.x.pub, s) (Q.wit c y.2.st.input (y.2.st.heard ++ ds')) := by
    show rwBook h.𝔇.arr h.𝔇.mat13 (_, s') _ = rwBook h.𝔇.arr h.𝔇.mat13 (_, s) _
    unfold rwBook
    dsimp only
    rw [hR.st, hR.book]
  have hv : Vq y.2.st.input := ei ▸ hV c s mm E hT.1
  have hNN : N ≤ (y.2.st.heard ++ ds').length := by
    have := hN c s mm E hT.1
    rw [List.length_append, eh, List.length_append]
    omega
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 (hA c y.2.st.input (y.2.st.heard ++ ds') hv hNN)
  have o1 := OS c y.2.st.input (y.2.st.heard ++ ds') hv hNN true _ _ y' hy'
  rw [hn] at o1
  rw [hE c y.2.st.input _ y' hy']
  show Except.ok y' = .ok ((h.𝔇.rw13 (y.2.st.input.x.pub, s')
    (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))).mask ⟨s'.out.indexMasks, e⟩)
  rw [eR, hR.out, R]
  exact congrArg Except.ok o1.symm

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_rowSpentGl_takes
#print axioms ProofFile.Honest.K4.W.k4_last_is_owners
#print axioms ProofFile.Honest.K4.W.k4_last_of_member
#print axioms ProofFile.Honest.K4.W.k4IndexOwn_of_senderLot
#print axioms ProofFile.Honest.K4.W.k4IndexTie_of_senderLot
#print axioms ProofFile.Honest.K4.W.k4Index_owner_is_entry
