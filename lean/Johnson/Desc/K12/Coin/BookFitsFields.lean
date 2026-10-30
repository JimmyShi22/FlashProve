-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BookFitsFields.lean: **"EVERY MESSAGE STANDS IN ITS TREE's LIST OF PARTS AT
ITS OWN PART NUMBER" (`BookFits`, Johnson/Desc/Book/BookFits.lean) IS A SENTENCE SUCH AS THE WALK OF
THE WHOLE SEATED FIRST CHAIN ASKS**: the three things that the walk's frame asks of a sentence P on
the book and the count of roots (`BookLaw P`, Johnson/IMR/BookSeat.lean: recv · same · k12),
at P := fun B _ => BookFits B, each in that frame's own letters; this file imports nothing of
Johnson/IMR/. Statements and proofs; each is a call of a law that lay.
  `fits_recv`: the plain ground's receiving at the first tree's number 0 hands it on (`recvP_fits`,
    Johnson/Desc/Book/BookFitsGround.lean).
  `fits_same`: it rides over a book with the same places and, tree by tree, the same parts
    (`K2.SameNumbers`, Johnson/Top/H0/Tw/K2C/BookKept.lean).
  `fits_atFinish`: a yes of the DECISION of the proximity test's block at the first chain's finish
    hands it on (`k12_bookFits`, BookFitsThrough.lean), where the place has one answer to a sample;
    that the masks come early is had from the yes. `fits_atFinish_plan`: "one answer" from the
    block's test on the plan.
THE THIRD PARTS FROM THE FRAME's LETTER IN ONE PREMISE: the frame's field k12 asks it from the
decision's yes ALONE, at the maker's numbers; "one answer to a sample" is had from the test on the
plan, or from a yes of the STEP; from the decision's yes alone I have it not.
What for: so that "the book fits" at the first chain's last record follows from the description's
return and a yes of its run, and no new item enters the promise.
Limits. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.BookFitsThrough
import Johnson.Desc.Book.BookFitsGround
import Johnson.Desc.K12.Law.EarlyStep
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.SeatLaws
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Book (BookFits recvP_fits)
open H2K.JointK

theorem fits_recv {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : Ground.recvP 0 d sent = some (ids, d')) (hB : BookFits d.book) :
    BookFits d'.book := recvP_fits 0 d d' sent ids h hB

theorem fits_same (A B : TreeBook) (h : First.K2.SameNumbers A B) (hA : BookFits A) :
    BookFits B := by
  intro i q hq
  rw [h.2.1] at hq
  obtain ⟨t₀, h0, hp⟩ := hA i q hq
  have hlt : q.1 < B.trees.size := by
    rw [h.1]
    exact (Array.getElem?_eq_some_iff.1 h0).1
  obtain ⟨T₀, e0, _, _, _, ep⟩ := h.2.2 q.1 B.trees[q.1] (Array.getElem?_eq_getElem hlt)
  rw [h0] at e0
  obtain rfl := Option.some.inj e0
  exact ⟨B.trees[q.1], Array.getElem?_eq_getElem hlt, by rw [ep]; exact hp⟩

theorem fits_atFinish (p : P12) (ha : p.answers = 1) (s s' : First.S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (atFinish p).decide s rs gs = .ok s')
    (hB : BookFits s.book) : BookFits s'.book := by
  obtain ⟨o, t', _, _, _, hk, rfl⟩ := Seat.atFinish_ok p s s' rs gs h
  exact k12_bookFits p (early_of_decide p _ t' rs gs hk) ha _ t' rs gs hk hB

theorem fits_atFinish_plan (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (s s' : First.S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (atFinish p).decide s rs gs = .ok s') (hB : BookFits s.book) : BookFits s'.book :=
  fits_atFinish p (answers_of_planOk p hp) s s' rs gs h hB

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.fits_recv
#print axioms VerifiableInference.Desc.K12.Coin.fits_same
#print axioms VerifiableInference.Desc.K12.Coin.fits_atFinish
#print axioms VerifiableInference.Desc.K12.Coin.fits_atFinish_plan
