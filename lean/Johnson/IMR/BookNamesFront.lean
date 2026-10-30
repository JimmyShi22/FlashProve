-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookNamesFront.lean: FOUR SENTENCES ON THE BOOK ((I1), (I2), (I3), PlacesStay: BELOW),
AT ONE CHAIN c, IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, AT THE PROOF FILE's SEAT:

  descPure_bookNamesFront: NO PREMISE BUT onlineDescription's RETURN: there are Z, A, B, c with
    F = fileDescBy … c such that
    (a) AT EVERY RECORD r that a fold from the first record (at any request) over a front part of
      frontOf c returns:
      (I1) Book.BookFits r.book: the book's two tables fit;
      (I3) Book.NumberedC 0 (coreS r): as many roots as trees; tree j bears the number j and the
        source "own j";
      (I2) r.book.place.size = r.st.oracles.size;
    (b) OVER ANY STRETCH of frontOf c, from any record: PlacesStay: every older place stays.
  ONE WALK, at the four relations together (SeatKeeps.and, Johnson/IMR/SeatKeeps.lean): so one c.
  NO YES OF THE WHOLE FILE IS ASKED, AND NOTHING OF KINDS K12 AND K13.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: the row on the book's names.
Not claimed: in which trees a link's messages lie; anything on the frame's lists. No soundness.
-/
import Johnson.IMR.SizeSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Book (BookFits)
open ProofFile (Pub)

theorem descPure_bookNamesFront {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      (∀ (p : ProofFile.InstPub) (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₁ (ProofFile.startS Z p) rs cols = .ok r →
          BookFits r.1.book ∧ Book.NumberedC 0 (coreS r.1) ∧
            r.1.book.place.size = r.1.st.oracles.size) ∧
      ∀ (l₁ l₂ l₃ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ ++ l₃ →
        ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₂ s rs cols = .ok r → PlacesStay s.book r.1.book := by
  have K1 : SeatKeeps (PR fun B _ => BookFits B) := seatKeeps_front
    (fun d d' sent ids e k => Book.recvP_fits 0 d d' sent ids e k)
    (fun _ _ _ hs k => K2.fits_same hs k)
  have K3 : SeatKeeps (PR numberedP) := seatKeeps_front
    (fun d d' sent ids e k => Book.recvP_numbered 0 d d' sent ids e k) numbered_sameNumbers
  obtain ⟨Z, A, B, c, hZ, e, hf, k⟩ :=
    descPure_stretch (((K1.and K3).and (seatKeeps_has k2Has)).and seatKeeps_places)
      (fun _ _ => ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩)
      (fun _ _ _ _ _ _ _ => ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩) h
  refine ⟨Z, A, B, c, hZ, e, hf, fun p l₁ l₂ hl ft rs cols r hr => ?_,
    fun l₁ l₂ l₃ hl ft s rs cols r hr => (k l₁ l₂ l₃ hl ft s rs cols r hr).2⟩
  obtain ⟨⟨⟨a1, a3⟩, a2⟩, -⟩ := k [] l₁ l₂ (by rw [hl]; rfl) ft _ rs cols r hr
  have e1 := (start_empty hZ p).1
  have e2 := (start_empty hZ p).2
  refine ⟨a1 ?_, (numberedP_iff (coreS r.1)).2 (a3 ?_), a2 ?_⟩
  · show BookFits (ProofFile.startS Z p).book
    rw [e1]
    exact Book.bookFits_empty
  · show numberedP (ProofFile.startS Z p).book (ProofFile.startS Z p).roots
    rw [e1, e2]
    exact empty_numbered
  · show (ProofFile.startS Z p).book.place.size = (ProofFile.startS Z p).st.oracles.size
    rw [e1, start_none hZ p]
    rfl

#print axioms descPure_bookNamesFront

end Meaning.K2
