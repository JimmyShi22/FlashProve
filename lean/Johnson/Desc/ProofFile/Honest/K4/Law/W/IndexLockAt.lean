-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexLockAt.lean: CONDITIONAL but for the first statement.
Two definitions, and statements with their proofs.

What is here. «THE LOCK AT THE SENDER's LETTERS», FOR THE ONE ENTRY OF THE INDEX MASKS' MESSAGE
THAT THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) READS: the public test
`K4LastEntry` (Law/W/LastEntry.lean) TAKEN AT TWO LETTERS OF THE MESSAGE's SENDER: o, its own
address, and s₀, a number among ITS coins: the book's last spending entry for K4's row names that
owner and starts at that number. It gives the one equation that joins lock and key
(Law/W/IndexOfSenderLot.lean's head) A NAME: a closed public fact, decidable at a written book.
Under it the lemma on the sender's lot and the key are stated with hE AT THESE TWO LETTERS: so hA,
hE and OS name no ENTRY of the book's any more; the book stays in them as the coins' type, and
«what the run holds at o» reads its first table: where Vq lets an input by, hA with hE says that o
has a row there with more than s₀ coins of the extension field. They are the sender's authors' to
show, at a book whose first table has their row; the name is K4's authors', each piece of it with
its own (that the entry names that owner and that number: the book's makers').

  `K4LastEntryAt Bk Q o s₀`   **THE NAME**: there are es₁ and eL with `K4LastEntry Bk Q es₁ eL`,
      eL.owner = o and eL.start.e = s₀. The book's own two letters stand under «there are»: the book
      fixes them.
  `k4LastEntryAtB`, `k4LastEntryAtB_iff`   **the same test as a Bool**, made of calls that stand
      already (`lendsRow`, `rowEntries`), with its «iff»: no coin in it.
  `k4LastEntryAt_fixed`   at one book and one Q the name holds at ONE pair (o, s₀): so where it is
      true at s₀ it is false at s₀ + 1: THE STATEMENT's FORM OF «THE START ONE OFF»; IT IS NO TOOTH
      AT THE JOIN: which pair the sender's sentence has, only a sender's text can say. (A tooth
      there, by evaluation, at a made-up sender's text of our own: Law/W/IndexJoinToy.lean.)
  `k4LastAt_is_owners`   whose the member is, under the name: member number `k4Takes` − 1 of
      `rowSpentGl` is there, and is element number s₀ of what the run holds at o.
  `k4IndexOwn_at`   **THE LEMMA UNDER THE NAME.**
  `k4IndexTie_at`   **THE KEY UNDER THE NAME**: the end of `k4IndexTie_coinsG`
      (Law/W/IndexTieCoins.lean), to the letter.

Not shown here. THAT THE NAME HOLDS AT ANY BOOK OF THE FULL SIZE, AT ANY SENDER's LETTERS. NEVER
FROM THESE STATEMENTS: «K4's coins are the sender's» as had · «lock and key fit». The limits of
Law/W/LastEntry.lean and Law/W/IndexOfSenderLot.lean bind here: chain number 0 and the book's first
table alone; the field lends compares the book with what K4's own parts state; one letter Vq serves
three uses; that any sender's text meets hA and hE; that any Script meets OS; `k4IndexTie_at` is
empty where the thread stands nowhere in front of the member, where its step is not taken, or where
the ledger hands out nothing. Of the hypotheses together no example is known to us. Where h stands
(`k4IndexTie_at`): that h can hold: the side library AtFullSide proves, with no hypothesis, that h
has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth); THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexOfSenderLot

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
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4IndexLotG k4IndexNum k4IndexRow k4IndexPlace k4PubG)

/-! ## 1 The name -/

/-- **THE LOCK AT THE SENDER's LETTERS.** o: the sender's own address. s₀: a number among its coins.
This defines the form of a hypothesis; the definition claims nothing. -/
def K4LastEntryAt (Bk : ProverCoinCounts) (Q : K4Pub) (o : Addr) (s₀ : ℕ) : Prop :=
  ∃ es₁ eL, K4LastEntry Bk Q es₁ eL ∧ eL.owner = o ∧ eL.start.e = s₀

/-- The same test as a Bool: no coin in it. This is a definition; it claims nothing. -/
def k4LastEntryAtB (Bk : ProverCoinCounts) (Q : K4Pub) (o : Addr) (s₀ : ℕ) : Bool :=
  lendsRow Bk 0 (k4Place Q) (k4RowIn Q) &&
    (rowEntries Bk (k4Place Q) (k4RowIn Q).length 0).getLast?.any fun e =>
      e.count.e == 1 && e.owner == o && e.start.e == s₀

section
variable {Bk : ProverCoinCounts} {Q : K4Pub} {o o' : Addr} {s₀ s₀' : ℕ}

/-- **The Bool is true just where the name holds.** No hypothesis. -/
theorem k4LastEntryAtB_iff : k4LastEntryAtB Bk Q o s₀ = true ↔ K4LastEntryAt Bk Q o s₀ := by
  unfold k4LastEntryAtB K4LastEntryAt
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hl, ha⟩
    cases hg : (rowEntries Bk (k4Place Q) (k4RowIn Q).length 0).getLast? with
    | none =>
      rw [hg] at ha
      cases ha
    | some e =>
      rw [hg] at ha
      have ha' : (e.count.e == 1 && e.owner == o && e.start.e == s₀) = true := ha
      simp only [Bool.and_eq_true, beq_iff_eq] at ha'
      refine ⟨(rowEntries Bk (k4Place Q) (k4RowIn Q).length 0).dropLast, e,
        ⟨hl, ?_, ha'.1.1⟩, ha'.1.2, ha'.2⟩
      exact (List.dropLast_append_getLast? e (Option.mem_def.2 hg)).symm
  · rintro ⟨es₁, eL, K, h1, h2⟩
    refine ⟨K.lends, ?_⟩
    rw [K.ents, List.getLast?_append, List.getLast?_singleton]
    show (eL.count.e == 1 && eL.owner == o && eL.start.e == s₀) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨K.one, h1⟩, h2⟩

/-- CONDITIONAL on J and J'. **AT ONE BOOK AND ONE Q THE NAME HOLDS AT ONE PAIR.** -/
theorem k4LastEntryAt_fixed (J : K4LastEntryAt Bk Q o s₀) (J' : K4LastEntryAt Bk Q o' s₀') :
    o' = o ∧ s₀' = s₀ := by
  obtain ⟨es₁, eL, K, rfl, rfl⟩ := J
  obtain ⟨es₁', eL', K', rfl, rfl⟩ := J'
  have e := K.ents.symm.trans K'.ents
  have e2 := (List.append_inj' e rfl).2
  obtain rfl := List.singleton_inj.1 e2
  exact ⟨rfl, rfl⟩

/-- CONDITIONAL on J. **THE MEMBER THAT K4's TEXT READS IS THERE, AND IS ELEMENT NUMBER s₀ OF WHAT
THE RUN HOLDS AT o.** -/
theorem k4LastAt_is_owners (J : K4LastEntryAt Bk Q o s₀) (k : Coins Bk) :
    ∃ y, (rowSpentGl Bk (k.look 0) (k4Place Q) (k0 Q.g + 16) 0)[k4Takes Q.P Q.hp Q.g - 1]? =
        some y ∧
      (k.look 0 o).2.eAt s₀ = .ok y := by
  obtain ⟨es₁, eL, K, rfl, rfl⟩ := J
  exact k4_last_is_owners K k

end

/-! ## 2 The lemma under the name -/

/-- CONDITIONAL on hP, J, hn, hA, hE and OS. **`OwnMsgs` AT THE THREE FIELDS OF K4's LOT, FROM
`OwnMsgs` AT THE SENDER's LOT.** hA, hE and OS name no entry of the book's. -/
theorem k4IndexOwn_at {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X CellsT Tok : Type}
    (Q : Script Bk (Local W₀ Rc Xi Tr) CellsT Tok MsgT) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) {o : Addr} {s₀ : ℕ} (J : K4LastEntryAt Bk Qp o s₀) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4IndexNum Zp) {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (tS k w (hd.take fS) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
    (hE : ∀ k w hd y', tS k w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (k.look 0 o).2.eAt s₀ = .ok y')
    (OS : OwnMsgs Q Vq N nS fS tS) :
    OwnMsgs Q Vq N
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).n
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt := by
  obtain ⟨es₁, eL, K, rfl, rfl⟩ := J
  exact k4IndexOwn_of_senderLot Q cells weights tokens look hP K nS fS tS hn hA hE OS

/-! ## 3 The key under the name -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, J, hn, hA, hE, OS, hV and hN, and on what stands in front of its end:
the thread stands in front of the member, the member's step is taken, the state behind it has a
ledger of the index masks, and that ledger hands out an entry; where these hold nowhere it is empty.
**THE END OF `k4IndexTie_coinsG`, UNDER THE NAME.** The four readers cells, weights, tokens, look
stand in no hypothesis and not in the end: they serve the proof alone; whoever calls names them. -/
theorem k4IndexTie_at
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {o : Addr} {s₀ : ℕ} (J : K4LastEntryAt Bk Qp o s₀)
    (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4IndexNum Zp) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ c w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (tS c w (hd.take fS) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
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
      (rowSpentGl Bk (c.look 0) (k4Place Qp) (k0 Qp.g + 16) 0)[k4Takes Qp.P Qp.hp Qp.g - 1]? =
        some ((h.𝔇.rw13
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2 s')
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c y.2.st.input
            (y.2.st.heard ++ ds'))).mask
          ⟨((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.seat c y.2
            s').2.out.indexMasks, e⟩) := by
  obtain ⟨es₁, eL, K, rfl, rfl⟩ := J
  exact k4IndexTie_of_senderLot h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh (cells := cells)
    (weights := weights) (tokens := tokens) (look := look) hQ K nS fS tS hn hA hE OS hV hN

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4LastEntryAtB_iff
#print axioms ProofFile.Honest.K4.W.k4LastEntryAt_fixed
#print axioms ProofFile.Honest.K4.W.k4LastAt_is_owners
#print axioms ProofFile.Honest.K4.W.k4IndexOwn_at
#print axioms ProofFile.Honest.K4.W.k4IndexTie_at
