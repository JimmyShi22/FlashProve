-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LastEntry.lean: one structure (the form of a hypothesis),
and statements with their proofs.

What is here. A PUBLIC TEST ON THE BOOK OF COINS, AT THE ROW OF THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4): the book lends the row, and THE LAST OF THE BOOK's SPENDING
ENTRIES FOR THE ROW's PARTS, SET APART, HANDS ONE COIN. It is made of tests that stand already and
names no new one: `lendsRow` (Honest/Small/LendsRow.lean), `rowEntries` (Honest/BookStretch.lean).
The laws on the index masks' entry take it as it is (Law/W/IndexOfSenderLot.lean); the laws on the
segment's mask row take it with a test on the entries in front, es₁ (Law/W/MaskLock.lean).

  `K4LastEntry Bk Q es₁ eL`   three fields, NO COIN IN ANY, each decidable at a written book: lends:
      the book lends K4's public row · ents: the row's spending entries, part by part, are es₁ with
      eL behind them · one: eL hands one coin of the extension field.
  `lendsRuns_fit`, `lendsRowAt_fit`, `lendsRow_fit`   no kind is named: EVERY SPENDING ENTRY OF A
      ROW THAT THE BOOK LENDS FITS ITS OWNER's COUNT: where the Bool is true, each entry passes
      `cutFits` at its owner's count, from its own start on, at its own count.
  `K4LastEntry.fits`   so eL's one coin lies inside the count that the book has at eL's owner
      (`lookDue`, Honest/Small/LendsRow.lean): no field: it follows from the three.
  `rowSpentGl_entries`   no kind is named: what a row's parts spend, as field elements
      (`rowSpentGl`, Honest/Law/Rule/CoinBack.lean), is its entries' runs, one behind the other: the
      like of `rowSpent_entries` (Honest/BookStretch.lean) without the packing.

Not shown here. THAT ANY BOOK MEETS THE THREE: no book of the full size is written. lends IS AT
CHAIN NUMBER 0 AND READS THE BOOK's FIRST TABLE ALONE: it is false at a book that keeps an owner's
row in another table. WHO eL's OWNER IS, and where its coin starts, are letters here. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookStretch
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.Law.Rule.CoinBack
import Johnson.Desc.ProofFile.Honest.K4.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Place)

/-- **A PUBLIC TEST ON THE BOOK: it lends K4's row, and the last spending entry of the row's parts,
set apart, hands one coin.** es₁: the entries in front. eL: the last. This defines the form of a
hypothesis; the definition claims nothing. -/
structure K4LastEntry (Bk : ProverCoinCounts) (Q : K4Pub) (es₁ : List Ahead) (eL : Ahead) : Prop where
  lends : lendsRow Bk 0 (k4Place Q) (k4RowIn Q) = true
  ents : rowEntries Bk (k4Place Q) (k4RowIn Q).length 0 = es₁ ++ [eL]
  one : eL.count.e = 1

variable {V W X : Type}

/-- Where a list of runs is lent, each entry fits its owner's count. CONDITIONAL on the Bool. -/
theorem lendsRuns_fit (due : Addr → Due) : ∀ (ds : List (String × Due)) (l : List Ahead),
    lendsRuns due ds l = true → ∀ e ∈ l, cutFits (due e.owner) e.start e.count = true
  | [], [], _, _, he => nomatch he
  | [], _ :: _, h, _, _ => by simp [lendsRuns] at h
  | _ :: _, [], h, _, _ => by simp [lendsRuns] at h
  | d :: ds, a :: l, h, e, he => by
    unfold lendsRuns at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, hc⟩, hf⟩, hr⟩ := h
    have hcd : a.count = d.2 := eq_of_beq hc
    rcases List.mem_cons.1 he with rfl | he'
    · rw [hcd]
      exact hf
    · exact lendsRuns_fit due ds l hr e he'

/-- Where a row is lent from the part number j on, each of its spending entries fits its owner's
count. CONDITIONAL on the Bool. -/
theorem lendsRowAt_fit (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Place) :
    ∀ (ps : List (Part V W X)) (j : Nat), lendsRowAt B rows due a ps j = true →
    ∀ e ∈ rowEntries B a ps.length j, cutFits (due e.owner) e.start e.count = true
  | [], _, _, _, he => nomatch he
  | p :: ps, j, h, e, he => by
    have h' : (lendsPart B rows due ⟨a, j⟩ p && lendsRowAt B rows due a ps (j + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have he' : e ∈ spentE B ⟨a, j⟩ ++ rowEntries B a ps.length (j + 1) := he
    rcases List.mem_append.1 he' with h1 | h2
    · unfold lendsPart at hp
      simp only [Bool.and_eq_true] at hp
      exact lendsRuns_fit due _ _ hp.1.2 e h1
    · exact lendsRowAt_fit B rows due a ps (j + 1) hr e h2

/-- The like for the Bool. CONDITIONAL on h. -/
theorem lendsRow_fit (B : ProverCoinCounts) (ch : Nat) (a : Place) (ps : List (Part V W X))
    (h : lendsRow B ch a ps = true) :
    ∀ e ∈ rowEntries B a ps.length 0, cutFits (lookDue B ch e.owner) e.start e.count = true :=
  lendsRowAt_fit B (B.rowsOf ch) (lookDue B ch) a ps 0 h

/-- CONDITIONAL on K. **The last entry's one coin lies inside its owner's count.** -/
theorem K4LastEntry.fits {Bk : ProverCoinCounts} {Q : K4Pub} {es₁ : List Ahead} {eL : Ahead}
    (K : K4LastEntry Bk Q es₁ eL) : eL.start.e + 1 ≤ (lookDue Bk 0 eL.owner).e := by
  have hm : eL ∈ rowEntries Bk (k4Place Q) (k4RowIn Q).length 0 := by
    rw [K.ents]
    exact List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))
  have hf := lendsRow_fit Bk 0 (k4Place Q) (k4RowIn Q) K.lends eL hm
  unfold cutFits at hf
  have hd := (of_decide_eq_true hf).2
  rw [K.one] at hd
  exact hd

/-- What a row's parts spend, as field elements, is its entries' runs, one behind the other. No
hypothesis. -/
theorem rowSpentGl_entries (Bk : ProverCoinCounts) (look : Addr → (d : Due) × Cs d) (p : Place) : ∀ n j,
    rowSpentGl Bk look p n j = (rowEntries Bk p n j).flatMap (sliceGl look)
  | 0, _ => rfl
  | n + 1, j => by
    show (spentE Bk ⟨p, j⟩).flatMap (sliceGl look) ++ rowSpentGl Bk look p n (j + 1) =
      (spentE Bk ⟨p, j⟩ ++ rowEntries Bk p n (j + 1)).flatMap (sliceGl look)
    rw [List.flatMap_append, rowSpentGl_entries Bk look p n (j + 1)]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lendsRuns_fit
#print axioms ProofFile.Honest.K4.W.lendsRowAt_fit
#print axioms ProofFile.Honest.K4.W.lendsRow_fit
#print axioms ProofFile.Honest.K4.W.K4LastEntry.fits
#print axioms ProofFile.Honest.K4.W.rowSpentGl_entries
