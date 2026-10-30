-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawLeaves.lean: THE SMALLNESS TEST, ITS FIRST HALF: WHAT ITS BLOCK LEAVES, IN
THE FORM OF Johnson/Desc/Sound/FoldHeard.lean.

The proof file's hypothesis on soundness at a description's own decision asks of every block behind
the reply's, beside its kind's lemma: `Block.Leaves heard`: where the block's decision goes on, what
the record holds as the reply that was heard is as it was.
  `decide_atS`: a yes of the kind's decision at the seat of AtS.lean turns, of the carried record,
    the smallness test's record alone.
  `hear_leaves`: GENERAL IN THE READING: the block leaves every reading of the carried record that
    `S.putTl` leaves.
  `hear_leaves_reply`: so it leaves the reply that was heard (s.out.reply); `hear_leaves_out`,
    `hear_leaves_fork`, `hear_leaves_statement`, `hear_leaves_mark`, `hear_leaves_book`,
    `hear_leaves_book_roots`, `hear_leaves_trees`: and all that was put out, the ledger, the chain's
    statement, the mark, the book, the book with the count of roots, the book's trees.
Statements and proofs; over ALL records, rounds and columns, as the form asks.
The third law of that family (`Piece.PassesTok`: the block's extractor hands the witness's token on)
is not typed here. The piece of Johnson/Desc/First/K8/LawPiece.lean has the identity as its
extractor.


-/
import Johnson.Desc.First.K8.LawAtS
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- A yes of the decision, at the seat of AtS.lean. -/
theorem decide_atS {Cl : Type} (p : Par) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List
           UInt64)))
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s') : ∃ tl' : HTailF2, s' = s.putTl tl' := by
  obtain ⟨r, _, _, _, _, _, _, _, _, _, hl⟩ := decide_ok atS p s s' rs gs h
  obtain ⟨tl, _, e⟩ := atS_lay s s' _ _ hl
  exact ⟨_, e⟩

/-- **The block leaves every reading that `S.putTl` leaves.** -/
theorem hear_leaves {Cl α : Type} (h : S → α) (hh : ∀ (s : S) (tl : HTailF2), h (s.putTl tl) = h s)
    (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves h := by
  intro s rs gs s' hd
  obtain ⟨tl', rfl⟩ := decide_atS p s s' rs gs hd
  exact hh s tl'

/-- The reply that was heard. -/
theorem hear_leaves_reply {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s =>
    s.out.reply :=
  hear_leaves _ (fun s tl => by rw [(putTl_rest s tl).2.2.2.2.2.2.1]) p

theorem hear_leaves_out {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => s.out :=
  hear_leaves _ (fun s tl => (putTl_rest s tl).2.2.2.2.2.2.1) p

theorem hear_leaves_fork {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves S.fork? :=
  hear_leaves _ putTl_fork p

theorem hear_leaves_statement {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => s.st
    :=
  hear_leaves _ (fun s tl => (putTl_rest s tl).1) p

theorem hear_leaves_mark {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => s.failed :=
  hear_leaves _ (fun s tl => (putTl_rest s tl).2.2.2.2.1) p

/-- The book, and so its trees. -/
theorem hear_leaves_book {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => s.book :=
  hear_leaves _ (fun s tl => (putTl_rest s tl).2.1) p

/-- The book with the count of roots. -/
theorem hear_leaves_book_roots {Cl : Type} (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => (s.book, s.roots) :=
  hear_leaves _ (fun s tl => by rw [(putTl_rest s tl).2.1, (putTl_rest s tl).2.2.1]) p

theorem hear_leaves_trees {Cl : Type} (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => s.book.trees :=
  hear_leaves _ (fun s tl => by rw [(putTl_rest s tl).2.1]) p

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_leaves
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_reply
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_fork
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_book_roots
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_trees
