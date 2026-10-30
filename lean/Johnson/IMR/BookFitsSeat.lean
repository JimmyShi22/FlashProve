-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookFitsSeat.lean: TWO MORE RIDERS OF Johnson/IMR/BookSeat.lean's WALK OF THE
FIRST CHAIN AT THE PROOF FILE's SEAT:

  (1) Book.BookFits (Johnson/Desc/Book/BookFits.lean: every message stands in its tree's list of
    parts at its own part number: the book's two tables fit) AT EVERY RECORD THAT THE FIRST CHAIN's
    FOLD PASSES THROUGH: descPure_fitsAt: Johnson/IMR/BookSeat.lean's descPure_sentenceAt at the
      sentence
    fun B _ => BookFits B: recv by the library's Book.recvP_fits, the start by its
    bookFits_empty, same by K2.fits_same (Johnson/Top/H0/Tw/K2C/FitsRide.lean). UNDER k12 AT IT:
    kind K12's block at the first chain's last test, at the numbers that the maker lays there and
    where it passes its own test on the plan.
  (2) PlacesStay: a RELATION on books: every older place is as it was: seatKeeps_places,
    seatBack_places, and descPure_placesStay: of two cuts of the first chain's flat list, one in
    front of the other: what the book says of a message at the record of the first it says at the
    record of the second. The sendings by Book.recvP_seat's clause "places"; kind K2 by
    K2.yes_book and K2.sendP_book (Johnson/Top/H0/Tw/K2C/BookKept.lean). UNDER k12 AT IT.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: the row on the book's names.
Not claimed: anything on which trees a link's messages lie in. No soundness.
-/
import Johnson.IMR.BookSeat
import Johnson.Top.H0.Tw.K2C.FitsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC CoreStill CoreRecv coreStill_same)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Book (BookFits)
open ProofFile (Pub)

/-! ## (1) The book's two tables fit -/

/-- **A YES OF THE FILE's DECISION: THE BOOK's TWO TABLES FIT AT EVERY RECORD THAT THE FIRST CHAIN's
FOLD PASSES THROUGH: UNDER KIND K12's SHARE AT IT.** -/
theorem descPure_fitsAt
    (k12 : ∀ (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))), (K12.atFinish (H2U.p12OfMade m)).planOk = true →
      (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s' → BookFits s.book →
      BookFits s'.book)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)) (t : S) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn), c.blocksInOrder = l₁ ++ l₂ →
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) → BookFits t.book :=
  descPure_sentenceAt (P := fun B _ => BookFits B)
    ⟨fun d d' sent ids e k => Book.recvP_fits 0 d d' sent ids e k,
      fun _ _ _ hs k => K2.fits_same hs k, k12⟩ Book.bookFits_empty h hr

/-! ## (2) Every older place stays -/

/-- Every older place is as it was. -/
def PlacesStay (A B : TreeBook) : Prop := ∀ j, j < A.place.size → B.place[j]? = A.place[j]?

theorem PlacesStay.refl (A : TreeBook) : PlacesStay A A := fun _ _ => rfl

theorem PlacesStay.size {A B : TreeBook} (h : PlacesStay A B) : A.place.size ≤ B.place.size := by
  by_cases e : A.place.size = 0
  · omega
  · have lt : A.place.size - 1 < A.place.size := by omega
    have k := h _ lt
    rw [Array.getElem?_eq_getElem lt] at k
    have := (Array.getElem?_eq_some_iff.1 k).1
    omega

theorem PlacesStay.trans {A B C : TreeBook} (h : PlacesStay A B) (k : PlacesStay B C) :
    PlacesStay A C := fun j hj => (k j (Nat.lt_of_lt_of_le hj h.size)).trans (h j hj)

/-- **The relation.** -/
abbrev PS : S → S → Prop := ByC (fun a b => PlacesStay a.book b.book) coreS

theorem ps_same (a b : Core) (h1 : b.book = a.book) (_ : b.roots = a.roots) :
    PlacesStay a.book b.book := by
  rw [h1]
  exact PlacesStay.refl _

theorem ps_recv {L : Type} (ft : Nat) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat) (h : Ground.recvP ft d sent = some (ids, d')) :
    PlacesStay d.book d'.book := by
  obtain ⟨-, lay, -, S⟩ := Book.recvP_seat ft d d' sent ids h
  exact S.places

theorem coreRecv_places : CoreRecv 0 fun a b => PlacesStay a.book b.book where
  refl := fun _ => PlacesStay.refl _
  trans := fun h k => h.trans k
  newGroup := fun d d' c m n h =>
    ps_same _ _ (coreStill_same.newGroup d d' c m n h).1 (coreStill_same.newGroup d d' c m n h).2
  admit := fun d d' o r h =>
    ps_same _ _ (coreStill_same.admit d d' o r h).1 (coreStill_same.admit d d' o r h).2
  join := fun d d' g o k h =>
    ps_same _ _ (coreStill_same.join d d' g o k h).1 (coreStill_same.join d d' g o k h).2
  addRow := fun d d' g r h =>
    ps_same _ _ (coreStill_same.addRow d d' g r h).1 (coreStill_same.addRow d d' g r h).2
  takeMask := fun d d' o n h =>
    ps_same _ _ (coreStill_same.takeMask d d' o n h).1 (coreStill_same.takeMask d d' o n h).2
  closeLedger := fun d d' o h =>
    ps_same _ _ (coreStill_same.closeLedger d d' o h).1 (coreStill_same.closeLedger d d' o h).2
  spendAsMask := fun d d' o h =>
    ps_same _ _ (coreStill_same.spendAsMask d d' o h).1 (coreStill_same.spendAsMask d d' o h).2
  elsewhere := fun d d' m o t h =>
    ps_same _ _ (coreStill_same.elsewhere d d' m o t h).1
      (coreStill_same.elsewhere d d' m o t h).2
  recv := fun d d' sent ids h => ps_recv 0 d d' sent ids h

theorem ps_fn {f : S → Except String S}
    (h : ∀ s t, f s = .ok t → t.book = s.book ∧ t.roots = s.roots) : Fn PS f :=
  fun s t k => ps_same _ _ (h s t k).1 (h s t k).2

theorem k2_places (p : K2.P2) : Whole PS (K2.codeSwitchKind p : Block S Unit) :=
  ⟨fun s _ _ s' h => by
      obtain ⟨r₁, r₂, x, ids, sd, an, took, d', -, hx, hb, -⟩ := K2.yes_book h
      obtain ⟨d₁, h1, e1, -⟩ := K2.sendP_book hx
      have a : PlacesStay s.book d₁.book := ps_recv _ _ _ _ _ h1
      intro j hj
      show s'.book.place[j]? = s.book.place[j]?
      rw [hb.2.1, e1]
      exact a j hj,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem seatKeeps_places : SeatKeeps PS where
  refl := fun _ => PlacesStay.refl _
  trans := fun _ _ _ h k => h.trans k
  frames := fun _ h => framesOf_core ps_same h
  k1First := fun q gp h0 => firstAtS_core coreRecv_places q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core coreRecv_places q gp l p m a h0
  reads := fun h => whole_core ps_same (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_core ps_same (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_core ps_same (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_core ps_same (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_core ps_same (seatedClaims_quiet h)
  k7 := fun W l => whole_core ps_same (k7Of_quiet W l)
  k8 := fun p => whole_core ps_same (k8Whole_quiet p)
  closeOf := closeOf_core ps_same
  batch := fun p _ hcl => batch_core ps_same (fun h k => h.trans k) p hcl
  k11 := fun Q => whole_core ps_same (headMerge11_quiet Q)
  k2 := fun p _ => k2_places p
  front := fun _ => ps_fn fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => ps_fn fun _ _ h => K2.headOpenQ_book h
  finFront := ps_fn fun _ _ h => K2.finishFrontQ_book h
  finBehind := ps_fn fun _ _ h => K2.finishBehindQ_book h

theorem seatBack_places
    (k12 : ∀ (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))), (K12.atFinish (H2U.p12OfMade m)).planOk = true →
      (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s' → PlacesStay s.book s'.book) :
    SeatBack PS where
  k12 := fun m hp => ⟨fun s rs gs s' h => k12 m s s' rs gs hp h, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => atM3_core coreRecv_places.toCoreStill p
  k13M4 := fun p Q h0 => atM4_core coreRecv_places p Q h0

/-- **A YES OF THE FILE's DECISION: OF TWO CUTS OF THE FIRST CHAIN's FLAT LIST, ONE IN FRONT OF THE
OTHER: EVERY PLACE OF THE BOOK AT THE FIRST STANDS AT THE SECOND: UNDER KIND K12's SHARE AT IT.** -/
theorem descPure_placesStay
    (k12 : ∀ (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))), (K12.atFinish (H2U.p12OfMade m)).planOk = true →
      (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s' → PlacesStay s.book s'.book)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ (l₁ l₂ l₃ : List (Block S ProofFile.Cl)) (t u : S) (rs rs' : List Fmt.RoundView)
        (cols cols' : List VerifiableInference.Desc.OpenedColumn), c.blocksInOrder = l₁ ++ l₂ ++ l₃ →
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) →
        foldBlocks 0 l₂ t rs cols = .ok (u, rs', cols') → PlacesStay t.book u.book := by
  obtain ⟨Z, A, B, c, hZ, rfl, k⟩ := descPure_flat seatKeeps_places (seatBack_places k12)
    (fun _ _ => trivial) h
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := fun b hb =>
    ((FileDescription.planOk_parts_of_run hr).blocks₁ b hb).1
  refine ⟨Z, A, B, c, hZ, rfl, fun l₁ l₂ l₃ t u rs rs' cols cols' hl _ h2 => ?_⟩
  exact Keeps.foldBlocks_keeps PS seatKeeps_places.refl seatKeeps_places.trans 0 l₂
    (fun b hb => k b (by rw [hl]; simp [hb]) (hp b (by rw [hl]; simp [hb]))) t rs cols _ h2

#print axioms descPure_fitsAt
#print axioms seatKeeps_places
#print axioms descPure_placesStay

end Meaning.K2
