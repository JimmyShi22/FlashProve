-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/ThreeCounts.lean: code switching: THREE COUNTS OF TREES AT A CODE SWITCH ARE
ONE: the book's count of trees (what is owed on the numbers seats from it) · p.firstTree + t.roots
(K2.seat_by_new seats from it) · N.treesAt at the place (the table of joints' own number). That
N.sent m 0, which the ties' premise M reads, is seated from that one count is the test sentPlaceB's
matter (Tw/K2C/SentByPlace.lean); the three premises together: Tw/K2C/ThreeTogether.lean. Theorems
with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  bookTrees_roots   where the test atFirstBook (Johnson/Desc/K12/Door/DoorBools.lean) accepts, at
                    whichever first tree: the book has as many trees as the state has counted roots
  k2P_firstTree     the code switch's parameters as the lot makes them (IM.k2P,
                    Johnson/IMR/K2Seat.lean) have firstTree = 0, where the public part is
                    ProofFile.pubPlain's: by pub_firstTree (Johnson/IMR/SeatKeeps.lean)
  counts_one        behind a way in that leaves the book and the roots:
                    t.book.trees.size = p.firstTree + t.roots = N.treesAt ps[k]?. The last by the
                    promise's own clause on the book: K1.onQ_book
                    (Johnson/Desc/K1/Law/NewAtSending.lean)
  hbase_at_place    THE PREMISE hbase OF hS_at_place (Tw/K2C/TieThreeSeatsAt.lean), at ITS letter
                    base := N.treesAt ps[k]? (the layout's first tree; not the letter base of
                    wordsMade | k2Piece in the ties)
LEFT, BY NAME: h0 : p.firstTree = 0 (k2P_firstTree) · hen: the way in leaves the book and the roots
(the identity, at a segment's and at the head's code switch; K2.finishFrontQ_book,
Tw/K2C/BookKept.lean, at the finish) · hBook: atFirstBook accepts behind the way in, under the
promise, Rch and «no mark»: THE FIRST CLAUSE OF THE FOURTH TIE's OWN hBook. ITS PAYER STANDS:
atFirstBook_all | bookInOrder_field (Johnson/IMR/AtReach.lean: at every reached state; it
is FoldFacts' field bookInOrder): NO TWIN IS TYPED HERE.
LIMITS. hBook is a premise here. That p is the lot's IM.k2P is said of no seat here. No soundness is
claimed. On hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeSeatsAt
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K1.Law.NewAtSending
import Johnson.IMR.SeatKeeps
import Johnson.IMR.K2Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.K12.Door (atFirstBook bookInOrderB)

/-- Where the test on the book's order accepts, the book has as many trees as the state has counted
roots. -/
theorem bookTrees_roots {ft : ℕ} {t : Rec} (h : atFirstBook ft t = true) :
    t.book.trees.size = t.roots := by
  unfold atFirstBook bookInOrderB at h
  rw [Bool.and_eq_true] at h
  exact (beq_iff_eq.1 h.1).symm

/-- The lot's parameters of a code switch have firstTree = 0. -/
theorem k2P_firstTree {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain o pol lay KL = .ok Z) (a : VerifiableInference.Desc.Place) (nm : String)
    (st : K2.At) (n : P1K2.Nums) : (IM.k2P Z a nm st n).firstTree = 0 :=
  _root_.Meaning.K2.pub_firstTree h

section
variable {F : Frame} {P Cells Tok : Type} (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (z : P) (k : ℕ)

variable (p : K2.P2) (enter : Rec → Except String Rec) (Rch : ℕ → Rec × F.E.Str → Prop) (ft : ℕ)
  (h0 : p.firstTree = 0)
  (hen : ∀ s t, enter s = .ok t → t.book = s.book ∧ t.roots = s.roots)
  (hBook : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → atFirstBook ft t = true)

include h0 hen hBook

/-- **The three counts are one.** -/
theorem counts_one : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a →
    ¬ a.1.failed ≠ none → ∀ t, enter a.1 = .ok t →
      t.book.trees.size = p.firstTree + t.roots ∧ p.firstTree + t.roots = N.treesAt ps[k]? := by
  intro a ha hr hm t et
  have e1 := bookTrees_roots (hBook a ha hr hm t et)
  have e2 := (VerifiableInference.Desc.K1.onQ_book N Mg links ps k z a ha (not_not.1 hm)).2
  rw [← (hen a.1 t et).1] at e2
  rw [h0, Nat.zero_add]
  exact ⟨e1, e1.symm.trans e2⟩

/-- **hbase of hS_at_place**, at base := N.treesAt ps[k]?. -/
theorem hbase_at_place : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a →
    ¬ a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → p.firstTree + t.roots = N.treesAt ps[k]? :=
  fun a ha hr hm t et =>
    (counts_one N Mg links ps z k p enter Rch ft h0 hen hBook a ha hr hm t et).2

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.bookTrees_roots
#print axioms VerifiableInference.Desc.First.K2Caller.k2P_firstTree
#print axioms VerifiableInference.Desc.First.K2Caller.counts_one
#print axioms VerifiableInference.Desc.First.K2Caller.hbase_at_place
