-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookFitsPaid.lean: Book.BookFits (the book's two tables fit) AT THE
FIRST CHAIN's LAST RECORD, AND AT EVERY RECORD THAT ITS FOLD PASSES THROUGH, BEHIND A YES OF THE
FILE's DECISION: NO PREMISE BESIDE onlineDescription's RETURN AND THAT YES.
  k12_fits: kind K12's share of Johnson/IMR/BookSeat.lean's BookLaw at P := fun B _ => BookFits B:
    the block
    at the first chain's last test, at the numbers that the maker lays there and where it passes its
    own test on the plan, hands BookFits on: by fits_atFinish_plan
    (Johnson/Desc/K12/Coin/BookFitsFields.lean) and Johnson/IMR/SeatKeeps.lean's atFinish_planOk.
  descPure_bookFits: descPure_sentence at that P: the last record.
  descPure_bookFitsAt: Johnson/IMR/BookFitsSeat.lean's descPure_fitsAt, its one premise paid: every
    cut.
The two other fields are called as Johnson/IMR/BookFitsSeat.lean calls them: Book.recvP_fits,
K2.fits_same.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: the files at the last chain's door (the test
bookFitsB on the first chain's last record's book).
No soundness.
-/
import Johnson.IMR.BookFitsSeat
import Johnson.Desc.K12.Coin.BookFitsFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Book (BookFits)
open ProofFile (Pub)

/-- **Kind K12's share.** -/
theorem k12_fits (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hp : (K12.atFinish (H2U.p12OfMade m)).planOk = true)
    (h : (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s') (k : BookFits s.book) :
    BookFits s'.book :=
  K12.Coin.fits_atFinish_plan (H2U.p12OfMade m) (atFinish_planOk hp) s s' rs gs h k

/-- **A YES OF THE FILE's DECISION: THE BOOK's TWO TABLES FIT AT THE FIRST CHAIN's LAST RECORD.** -/
theorem descPure_bookFits {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      BookFits e₁.book :=
  descPure_sentence (P := fun B _ => BookFits B)
    ⟨fun d d' sent ids e k => Book.recvP_fits 0 d d' sent ids e k,
      fun _ _ _ hs k => K2.fits_same hs k, k12_fits⟩ Book.bookFits_empty h hr

/-- **AND AT EVERY RECORD THAT THE FIRST CHAIN's FOLD PASSES THROUGH.** -/
theorem descPure_bookFitsAt {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)) (t : S) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn), c.blocksInOrder = l₁ ++ l₂ →
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) → BookFits t.book :=
  descPure_fitsAt k12_fits h hr

#print axioms k12_fits
#print axioms descPure_bookFits
#print axioms descPure_bookFitsAt

end Meaning.K2
