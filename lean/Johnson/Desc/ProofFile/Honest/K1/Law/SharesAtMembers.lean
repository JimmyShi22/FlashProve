-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SharesAtMembers.lean: THE SHARED "SENDING" (the kind K1): K1's
WHOLE DEBT OF SHARES OF "THE EXCHANGE" AT EACH OF ITS 51 MEMBERS IN THE SEGMENTS, AS ONE LAW A SORT,
IN THE FORM IN WHICH ProofFile's GATHER ASKS IT, AT lettersHead (Honest/Thread/FirstHead.lean), THE PROVER
H AND THE SCRIPT Q FREE. Three theorems; no definition. A JOIN OF LAWS THAT LIE; NO NEW ARGUMENT.

THE END, THE SAME IN ALL THREE, IS THE END OF THE BINDER hXhear OF ProofFile's owesS_framesT
(Honest/Thread/GatherFramesT.lean), FROM "∀ j : Item" ON, OUR NUMBER LAID FOR ITS "14 * l + i + 2":
the share ExchangeAtS (Honest/Thread/SharesS.lean) at each item that the row at the number owes, but
for an item that is open in front of it and is a pin, pinI, pinW, or a constr at one of the
library's parts4.

  - k1_shares_two: number 2, the opening: UNDER h · R at the sort "opening".
  - k1_shares_reads: K1.noL l false (hl : l < 25): UNDER h · R at the sort "reads l" · hSaid (the
    family gives SaidOk) · hTie (THE SHARE AT THE ITEM tie l: A PREMISE).
  - k1_shares_digits: K1.noL l true: UNDER h · R at the sort "digits l".

THE WORD "SHARE". Here a share is ONE ITEM's PART OF THE DEBT "the exchange" (ExchangeAtS): a
pointwise sentence. ProofFile's Fall.share and Part.badShare are odds: another sense of the word, in the
same library.

WHICH LAW PAYS WHICH ITEM. pin m t: exchange_pin · pinI: exchange_pinI (ExchangeAtPins.lean) · row 0
(sample 0): exchange_rows_two · row l (sample 1), row l (sample 2): exchange_rows_fifty_tied
(ExchangeAtHead.lean) · tie l: hTie, HANDED THROUGH · forms l j n: exchangeAtS_forms_of_tie
(FormsShareOfTie.lean), from hTie · pin l 0 and constr l small at "reads": open in front: the end's
middle premise is absurd there: they are the gather's. THAT THE ROW OWES NOTHING ELSE: three closed
tests (OwedAtMembers.lean).

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
NEVER ON SOUNDNESS's ROAD. (A fence. WHY IT BINDS HERE:
k1_shares_reads calls a fenced law, exchangeAtS_forms_of_tie.)

ALOUD. IT PAYS NOTHING AT A SCRIPT. R, THE RECORD K1Seated (Honest/K1/Seated.lean), IS A PREMISE,
WHOLE: its fields msgs and pads, THE TIE, ARE EQUATIONS ON THE SCRIPT Q, PROVED OF NO SCRIPT. THE
BOOK AND THE PROVER H ARE TIED BY NOTHING BUT R's FIELD hasCoins. R's NEAREST PAYER:
k1Seated_two_at_book, k1Seated_fifty_at_book (RecordAtBookFill.lean): at a returned prover's own
book, under two premises on the filling's lots AND THE TIE: not called here. THE ENDS AT
THE 51 MEMBERS ARE AT MOST 229 BY THE TESTS (which say that a row owes nothing else), AND 229 BY AN
EVALUATION OUTSIDE THIS LIBRARY (3 · 25 times 7, and one more at l = 24 · 25 times 2): OF THESE 25
ARE hTie ITSELF, HANDED THROUGH; 204 ARE DERIVED. EACH END STANDS UNDER THE PAIR ThrS AND THE
MEMBER's ACCEPTED STEP, INSIDE ExchangeAtS: AN IMPLICATION: where no state of a run meets the pair
it says nothing: so, by another house's reading (argued; no Lean), from number 13 on at the prover
that onlineProverFromPublicFiles returns at the filling widerFillAt, for families that give PlayedTo. No filling is named
here.

THE BOOK. The sentence, to the letter, with
its first arm, in marks: "At a book whose count at the part's address does not cover the part's due
this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is a premise
here." OUR OWN WORDS: it stands among the premises as the field hasCoins of the record K1Seated (the
binder R), at k1_shares_two, k1_shares_reads, k1_shares_digits.

Limits. hXhear asks every i < IM.nAt l: K1's members are two of these numbers a segment (three at l
= 0): WHO JOINS THE SHARES BY NUMBER INTO ONE hXhear IS NOT SAID HERE. W's sending, number 356, has
a binder of its own and is not here. THE FULL SIZE ALONE; the format's second hash function alone. The
gather's file is held as a reading copy and is not imported: that the end is its binder's is held by
a program, not by Lean. It stands over files of L25's and of ours that are on no seal. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.OwedAtMembers
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsShareOfTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
  {J : SendJob (PlaceIn ProofFile.Inst) X} {own₀ : X} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- IT PAYS NOTHING AT A SCRIPT: R IS A PREMISE, WHOLE. **K1's SHARES AT NUMBER 2**, in the gather's
form: pin 0 0, pinI, row 0 (sample 0). -/
theorem k1_shares_two
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 2 blk wit J own₀
      .opening arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
        2).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 2 →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        2 j := by
  intro j hj _
  rcases owed_two hj with rfl | rfl | rfl
  · exact exchange_pin R Said 0 0 rfl
  · exact exchange_pinI R Said
  · exact exchange_rows_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w R Said

/-- IT PAYS NOTHING AT A SCRIPT: R IS A PREMISE, WHOLE; hTie IS THE SHARE AT tie l, HANDED THROUGH.
**K1's SHARES AT A SEGMENT's "reads"**, in the gather's form: pin l 1, row l (sample 1), tie l, the
forms. -/
theorem k1_shares_reads {l : ℕ} (hl : l < 25)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l false) blk
      wit J own₀ (.reads l) arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hTie : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) (.tie l)) :
    ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
        (K1.noL l false)).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened (K1.noL l false) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (K1.noL l false) j := by
  intro j hj hmid
  rcases owed_reads hl hj with (rfl | rfl | rfl | ⟨y, hy, rfl⟩) | ⟨hc, ho⟩
  · exact exchange_pin R Said l 1 rfl
  · exact exchange_rows_fifty_tied h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl false R Said
  · exact hTie
  · exact exchangeAtS_forms_of_tie h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl hy hTie
  · obtain ⟨h1, -, -, h4⟩ := hmid ho
    rcases hc with rfl | rfl
    · exact absurd rfl (h1 l 0)
    · exact absurd rfl (h4 l .small (by decide))

/-- IT PAYS NOTHING AT A SCRIPT: R IS A PREMISE, WHOLE. **K1's SHARES AT A SEGMENT's "digits"**, in
the gather's form: pin l 2, row l (sample 2). -/
theorem k1_shares_digits {l : ℕ} (hl : l < 25)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l true) blk
      wit J own₀ (.digits l) arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
        (K1.noL l true)).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened (K1.noL l true) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (K1.noL l true) j := by
  intro j hj _
  rcases owed_digits hl hj with rfl | rfl
  · exact exchange_pin R Said l 2 rfl
  · exact exchange_rows_fifty_tied h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl true R Said

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_shares_two
#print axioms ProofFile.Honest.K1.k1_shares_reads
#print axioms ProofFile.Honest.K1.k1_shares_digits
