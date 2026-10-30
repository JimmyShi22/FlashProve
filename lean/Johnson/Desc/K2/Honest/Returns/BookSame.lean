-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/BookSame.lean: WHERE NO ORACLE MESSAGE IS SENT THE BOOK OF TREES
STAYS AS IT IS, WHOLE: of two cuts of one fold, up to the place behind the last segment, at which
the state counts as many oracle messages, the later state's book IS the earlier's: also each tree's
count of the lists at which it has been opened, which the library's `SameNumbers` lets turn. Under
the opening alone. A tool for `AllOpen`'s clause "a tree of one list has not been opened"
(Returns/ReadOpen.lean). A definition and an abbreviation; statements with their proofs.

  `bookSame a b` a relation on the walk's three (statement, book, count of roots): b's book has at
                    least as many places as a's; and if just as many, it is a's book
  `bookSame_same`, `bookSame_refl`, `bookSame_trans` where the book is the same · reflexive ·
                    transitive: THE BOOK's OWN NUMBER OF PLACES IS THE CLOCK
  `lay_none`, `bookSame_recv`, `coreRecv_bookSame` a receiving of no message lays no tree; so a
                    receiving keeps the relation; so do the ground's eight other calls, which leave
                    the book
  `BS`, `bs_fn` the relation on the walk's states (an abbreviation); a change of the state that
                    leaves book and count of roots keeps it
  `k2_bookSame` THE CODE SWITCH KEEPS IT IDLY: its yes sends at least the carrying message, so the
                    number of places grows
  `seatKeeps_bookSame` so every sub-protocol in front keeps it. THE LIBRARY's `seatKeeps_places`
                    (Johnson/IMR/BookFitsSeat.lean): its lines stand here again at this relation
  `book_same_between` THE TOP: from the fold's returns at two cuts k₀ ≤ k, k up to the front's
                    length, with one count of oracle messages
  `counts_rise` of two such cuts the later state counts at least as many oracle messages: the
                    relation's first half

By, all the library's: `recvP_seat` (Johnson/Desc/Book/BookFitsGround.lean), `Seated`
(Johnson/Desc/Book/Seated.lean) · `layTrees_eq`, `laid` (OnBytes/Iop/LayTreesLaws.lean) ·
`CoreRecv`, `coreStill_same` (Johnson/Desc/CoreKeeps.lean) · `yes_book`, `sendP_book`
(Johnson/Top/H0/Tw/K2C/BookKept.lean) · `framesOf_core`, `firstAtS_core`, `laterAt_core`,
`whole_core`, `closeOf_core`, `batch_core` (Johnson/Goal/Meaning/CoreSeated.lean) and the kinds'
laws "quiet" that `seatKeeps_places` calls · `open_between`, `open_has`
(Johnson/IMR/WalkGivesAt.lean). A near relative, not called: `fn_book` (Johnson/IMR/RootsSeat.lean):
`bs_fn`'s premise at another relation. Near relatives of `counts_rise`, not called: `Grows`
(Johnson/Desc/Grows.lean) with `seatKeeps_grows` (Johnson/IMR/GrowsSeat.lean): no message is lost,
under a premise on the code switch; here there is none.

Limits. Nothing where a message is sent in between. Nothing behind the place behind the last
segment. Nothing on adopting. That a fold returns is shown of no proof here. This file's imports are
heavy. Nothing on any property.


-/
import Johnson.IMR.AtReach
import OnBytes.Iop.LayTreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC CoreStill CoreRecv coreStill_same)
open VerifiableInference.Desc.K1.RelCore (coreS)
open Meaning.K2
open ProofFile (Pub Cl)

/-- **At least as many places; and if just as many, the same book.** -/
def bookSame (a b : Core) : Prop :=
  a.book.place.size ≤ b.book.place.size ∧
    (b.book.place.size = a.book.place.size → b.book = a.book)

theorem bookSame_same (a b : Core) (h1 : b.book = a.book) (_ : b.roots = a.roots) :
    bookSame a b := ⟨by rw [h1], fun _ => h1⟩

theorem bookSame_refl (a : Core) : bookSame a a := bookSame_same a a rfl rfl

theorem bookSame_trans {a b c : Core} (h : bookSame a b) (k : bookSame b c) : bookSame a c := by
  refine ⟨Nat.le_trans h.1 k.1, fun e => ?_⟩
  have h1 := h.1
  have k1 := k.1
  exact (k.2 (by omega)).trans (h.2 (by omega))

/-- A sending of no message lays no tree. -/
theorem lay_none (codes : Codes) (L : TreeLay) (h : layTrees codes #[] = some L) :
    L.shapes.size = 0 := by
  rw [OnBytes.LayTreesLaws.layTrees_eq] at h
  simp [OnBytes.LayTreesLaws.laid] at h
  subst h
  rfl

theorem bookSame_recv {L : Type} (ft : Nat) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat) (h : Ground.recvP ft d sent = some (ids, d')) :
    bookSame (Ground.coreOf d) (Ground.coreOf d') := by
  obtain ⟨-, lay, hl, Se⟩ := Book.recvP_seat ft d d' sent ids h
  refine ⟨?_, fun e => ?_⟩
  · show d.book.place.size ≤ d'.book.place.size
    rw [Se.count]
    exact Nat.le_add_right _ _
  · have e' : d'.book.place.size = d.book.place.size := e
    have h0 : sent.size = 0 := by
      rw [Se.count] at e'
      omega
    obtain rfl : sent = #[] := Array.eq_empty_of_size_eq_zero h0
    have hz := lay_none _ lay hl
    have ht : d'.book.trees = d.book.trees := by
      apply Array.ext_getElem?
      intro j
      by_cases lt : j < d.book.trees.size
      · exact Se.trees j lt
      · rw [Array.getElem?_eq_none (by rw [Se.size, hz]; omega),
          Array.getElem?_eq_none (by omega)]
    have hp : d'.book.place = d.book.place := by
      apply Array.ext_getElem?
      intro j
      by_cases lt : j < d.book.place.size
      · exact Se.places j lt
      · rw [Array.getElem?_eq_none (by rw [e']; omega), Array.getElem?_eq_none (by omega)]
    show d'.book = d.book
    cases hb : d'.book with
    | mk t p =>
      cases hb0 : d.book with
      | mk t0 p0 =>
        rw [hb, hb0] at ht hp
        simp only at ht hp
        rw [ht, hp]

theorem coreRecv_bookSame : CoreRecv 0 bookSame where
  refl := bookSame_refl
  trans := fun h k => bookSame_trans h k
  newGroup := fun d d' c m n h =>
    bookSame_same _ _ (coreStill_same.newGroup d d' c m n h).1
      (coreStill_same.newGroup d d' c m n h).2
  admit := fun d d' o r h =>
    bookSame_same _ _ (coreStill_same.admit d d' o r h).1 (coreStill_same.admit d d' o r h).2
  join := fun d d' g o k h =>
    bookSame_same _ _ (coreStill_same.join d d' g o k h).1 (coreStill_same.join d d' g o k h).2
  addRow := fun d d' g r h =>
    bookSame_same _ _ (coreStill_same.addRow d d' g r h).1 (coreStill_same.addRow d d' g r h).2
  takeMask := fun d d' o n h =>
    bookSame_same _ _ (coreStill_same.takeMask d d' o n h).1
      (coreStill_same.takeMask d d' o n h).2
  closeLedger := fun d d' o h =>
    bookSame_same _ _ (coreStill_same.closeLedger d d' o h).1
      (coreStill_same.closeLedger d d' o h).2
  spendAsMask := fun d d' o h =>
    bookSame_same _ _ (coreStill_same.spendAsMask d d' o h).1
      (coreStill_same.spendAsMask d d' o h).2
  elsewhere := fun d d' m o t h =>
    bookSame_same _ _ (coreStill_same.elsewhere d d' m o t h).1
      (coreStill_same.elsewhere d d' m o t h).2
  recv := fun d d' sent ids h => bookSame_recv 0 d d' sent ids h

/-- The relation on the walk's states. -/
abbrev BS : S → S → Prop := ByC bookSame coreS

theorem bs_fn {f : S → Except String S}
    (h : ∀ s t, f s = .ok t → t.book = s.book ∧ t.roots = s.roots) : Fn BS f :=
  fun s t k => bookSame_same _ _ (h s t k).1 (h s t k).2

/-- **The code switch keeps it idly: its yes sends.** -/
theorem k2_bookSame (p : K2.P2) : Whole BS (K2.codeSwitchKind p : Block S Unit) :=
  ⟨fun s _ _ s' h => by
      obtain ⟨r₁, r₂, x, ids, sd, an, took, d', -, hx, hb, -⟩ := K2.yes_book h
      obtain ⟨d₁, h1, e1, -⟩ := K2.sendP_book hx
      obtain ⟨-, lay, -, Se⟩ := Book.recvP_seat _ _ _ _ _ h1
      have hc : s'.book.place.size =
          s.book.place.size + (_root_.Tw.K2.switchNotices x.T x.others).size := by
        rw [hb.2.1, e1]
        exact Se.count
      have hpos : 0 < (_root_.Tw.K2.switchNotices x.T x.others).size := by
        simp [_root_.Tw.K2.switchNotices]
      exact ⟨by show s.book.place.size ≤ s'.book.place.size; omega,
        fun e => by
          have e' : s'.book.place.size = s.book.place.size := e
          omega⟩,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem seatKeeps_bookSame : SeatKeeps BS where
  refl := fun _ => bookSame_refl _
  trans := fun _ _ _ h k => bookSame_trans h k
  frames := fun _ h => framesOf_core bookSame_same h
  k1First := fun q gp h0 => firstAtS_core coreRecv_bookSame q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core coreRecv_bookSame q gp l p m a h0
  reads := fun h => whole_core bookSame_same (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_core bookSame_same (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_core bookSame_same (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_core bookSame_same (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_core bookSame_same (seatedClaims_quiet h)
  k7 := fun W l => whole_core bookSame_same (k7Of_quiet W l)
  k8 := fun p => whole_core bookSame_same (k8Whole_quiet p)
  closeOf := closeOf_core bookSame_same
  batch := fun p _ hcl => batch_core bookSame_same (fun h k => bookSame_trans h k) p hcl
  k11 := fun Q => whole_core bookSame_same (headMerge11_quiet Q)
  k2 := fun p _ => k2_bookSame p
  front := fun _ => bs_fn fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => bs_fn fun _ _ h => K2.headOpenQ_book h
  finFront := bs_fn fun _ _ h => K2.finishFrontQ_book h
  finBehind := bs_fn fun _ _ h => K2.finishBehindQ_book h

/-- **Of two cuts with one count of oracle messages: one book.** -/
theorem book_same_between {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    {k₀ k : Nat} (h₀ : k₀ ≤ k) (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub}
    {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take k₀) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R₁, C₁))
    (hc : t.st.oracles.size = t₀.st.oracles.size) : t.book = t₀.book := by
  have K : BS t₀ t := open_between seatKeeps_bookSame O trivial (fun _ _ _ => trivial) h₀ hk f₀ f
  refine K.2 ?_
  show t.book.place.size = t₀.book.place.size
  rw [open_has O hk f, open_has O (Nat.le_trans h₀ hk) f₀]
  exact hc

/-- **The counts of oracle messages only rise along a fold.** -/
theorem counts_rise {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    {k₀ k : Nat} (h₀ : k₀ ≤ k) (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub}
    {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take k₀) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R₁, C₁)) :
    t₀.st.oracles.size ≤ t.st.oracles.size := by
  have K : BS t₀ t := open_between seatKeeps_bookSame O trivial (fun _ _ _ => trivial) h₀ hk f₀ f
  have k1 : t₀.book.place.size ≤ t.book.place.size := K.1
  rwa [open_has O hk f, open_has O (Nat.le_trans h₀ hk) f₀] at k1

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.bookSame_same
#print axioms VerifiableInference.Desc.K2.Honest.Returns.bookSame_refl
#print axioms VerifiableInference.Desc.K2.Honest.Returns.bookSame_trans
#print axioms VerifiableInference.Desc.K2.Honest.Returns.lay_none
#print axioms VerifiableInference.Desc.K2.Honest.Returns.bookSame_recv
#print axioms VerifiableInference.Desc.K2.Honest.Returns.coreRecv_bookSame
#print axioms VerifiableInference.Desc.K2.Honest.Returns.bs_fn
#print axioms VerifiableInference.Desc.K2.Honest.Returns.k2_bookSame
#print axioms VerifiableInference.Desc.K2.Honest.Returns.seatKeeps_bookSame
#print axioms VerifiableInference.Desc.K2.Honest.Returns.book_same_between
#print axioms VerifiableInference.Desc.K2.Honest.Returns.counts_rise
