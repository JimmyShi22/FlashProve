-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/FitsAtPlace.lean: code switching: AN ACCEPT OF A SEATED SWITCH HANDS THE
BOOK's INVARIANT BookFits (Johnson/Desc/Book/BookFits.lean) ON, AT EACH OF THE WAYS IN AND OUT OF
THE 25 PLACES; and the ways in leave the book as it is. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. The second tie (k02_t2S, Johnson/P1K2R/TieTwoS.lean) takes two premises on the book: hbk (the
way in leaves the book) and hBF (BookFits in front of and behind an accept). Behind an accept the
state is not known to be «reached» there: so the second half of hBF is had from the first, by the
texts.
  BookDoor enter leave   the way in and the way out each leave the book as it is
  bookDoor_finish · bookDoor_head · bookDoor_guards · bookDoor_opened · bookDoor_head_opened
                    at the ways of the finish, of the output head's segment, of a bare link, of a
                    link's first place with the frame's «opened» behind, and of the head's with it
                    (the three of k02_sits_pAt, K2Caller/SitsAtP.lean, among them)
  fits_at_place     a step of the seated sub-protocol hands BookFits on
  fits_behind_out   the same at an accept of the sub-protocol's own piece
CALLED: yes_fits (K2C/FitsRide.lean) · finishFrontQ_book · finishBehindQ_book · headOpenQ_book
(K2C/BookKept.lean) · opened_keeps (Johnson/Top/H0/Walk/FrameOpened.lean) · guards_same ·
leaveOpened_is (Johnson/P1K2R/SitsDoor.lean) · bind_guards (P1K2R/HandsEnds.lean) · k2_step_two
(K2C/HandsLink.lean) · yes_of_out (P1K2R/TieTwoAt.lean).
LIMITS. BookFits IN FRONT, at a reached state, is not here. A frame fact. No soundness is claimed.

-/
import Johnson.Top.H0.Tw.K2C.FitsRide
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Top.H0.Tw.K2C.HandsLink
import Johnson.Top.H0.Walk.FrameOpened
import Johnson.P1K2R.SitsDoor
import Johnson.P1K2R.HandsEnds
import Johnson.P1K2R.TieTwoAt
import Johnson.Desc.K12.Law.Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 HeadPar codeSwitchKind headOpenQ finishFrontQ finishBehindQ yes_fits
  k2_step_two headOpenQ_book finishFrontQ_book finishBehindQ_book)
open H2K.JointK (Sits)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open Johnson.Desc.First.Walk.Tied (opened_keeps)

/-- The way in and the way out each leave the book as it is. -/
def BookDoor (enter : S → Except String S) (leave : S → S → Except String S) : Prop :=
  (∀ s t, enter s = .ok t → t.book = s.book) ∧ ∀ s t s', leave s t = .ok s' → s'.book = t.book

theorem book_id {s t : S} (h : (Except.ok s : Except String S) = .ok t) : t.book = s.book := by
  cases h
  rfl

theorem bookDoor_finish : BookDoor finishFrontQ fun s t => (finishBehindQ t).bind (guards s) :=
  ⟨fun _ _ h => (finishFrontQ_book h).1, fun _ _ _ h => (finishBehindQ_book (bind_guards h)).1⟩

theorem bookDoor_head (HP : HeadPar) :
    BookDoor (fun s => .ok s) fun s t => (headOpenQ HP t).bind (guards s) :=
  ⟨fun _ _ h => book_id h, fun _ _ _ h => (headOpenQ_book (bind_guards h)).1⟩

theorem bookDoor_guards : BookDoor (fun s => .ok s) fun s t => guards s t :=
  ⟨fun _ _ h => book_id h, fun _ _ _ h => by rw [guards_same h]⟩

theorem bookDoor_opened {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) :
    BookDoor (fun s => .ok s) fun s t => leaveOpened f s t :=
  ⟨fun _ _ e => book_id e, fun _ _ _ e => (opened_keeps h hf (leaveOpened_is e)).2.1⟩

theorem bookDoor_head_opened {built : Array OnBytes.Model.Stages.LinkH}
    {first : OnBytes.Params.First} {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame}
    {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f)
    (HP : HeadPar) :
    BookDoor (fun s => .ok s) fun s t => (headOpenQ HP t).bind (leaveOpened f s) :=
  ⟨fun _ _ e => book_id e, fun _ _ _ e => by
    obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    rw [(opened_keeps h hf (leaveOpened_is h2)).2.1, (headOpenQ_book h1).1]⟩

/-- **A step of the seated sub-protocol hands BookFits on.** -/
theorem fits_at_place {Cl : Type} {ft : Nat} {B : Block S Cl} {p : P2}
    {enter : S → Except String S} {leave : S → S → Except String S}
    (hS : Sits B (codeSwitchKind p : Block S Unit) enter leave) (hD : BookDoor enter leave) {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n₁ : Nat} (hy : B.step ft s rs cols = .ok (s', n₁))
    (hB : BookFits s.book) : BookFits s'.book := by
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols n₁ hy
  obtain ⟨r₁, r₂, gs, _, hd⟩ := k2_step_two e2
  rw [hD.2 s t' s' e3]
  refine yes_fits hd ?_
  rw [hD.1 s t e1]
  exact hB

end P1K2

namespace P1K2
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind ownPiece)
open H2K.JointK (Sits)
open ProofFile (Cl)

variable {P W : Type} {C : CK} {F : Frame}

/-- **The same at an accept of the sub-protocol's own piece.** -/
theorem fits_behind_out {q : Piece C F (P × S) Cl W} {B : Block S Cl}
    {ext : S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W} {err : Err (uLT C q.ds)}
    {a b : S × F.E.Str} {τ : Iop.Tr (uLT C q.ds)} {p : P2} {enter : S → Except String S}
    {leave : S → S → Except String S} (hS : Sits B (codeSwitchKind p : Block S Unit) enter leave)
    (hD : BookDoor enter leave) (hb : (ownPiece q B ext err).ior.red.out a τ = some b)
    (hB : BookFits a.1.book) : BookFits b.1.book := by
  obtain ⟨rs, cols, n₁, hy⟩ := yes_of_out hb
  exact fits_at_place hS hD hy hB

end P1K2

#print axioms P1K2.bookDoor_finish
#print axioms P1K2.bookDoor_head
#print axioms P1K2.bookDoor_guards
#print axioms P1K2.bookDoor_opened
#print axioms P1K2.bookDoor_head_opened
#print axioms P1K2.fits_at_place
#print axioms P1K2.fits_behind_out
