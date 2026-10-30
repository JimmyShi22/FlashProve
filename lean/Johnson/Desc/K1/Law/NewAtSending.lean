-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/NewAtSending.lean: THE CALL new_of:
WHAT A SENDING OF KIND K1 GIVES AT ITS NEW TENANTS, AT THE TABLE OF JOINTS' THREE LETTERS held,
no collision, shown: behind a yes of the sending's piece at which every message that has an
out-of-domain (OOD) sample (our files call it the record) is sealed at its word off the strings.
GENERAL IN THE SENDING (the place P, the radii, the base, the two rounds' data, the price, the
block): for the first segment's opening, the fifty later places and W's sending alike.

OBJECT. sendPiece c base d₁ d₂ P.coordinates e (Johnson/Desc/K1/Law/GoodSend3.lean), c any block
over the chain's state with two declared rounds whose yes books the place's messages (Booked).
USER. The proof of k01_fifty (Johnson/Desc/K1/Law/K01Law.lean), for fOf | fIn | hf | hseal |
hshown of k01_later_tied (Johnson/Desc/K1/Law/LaterOne.lean): new_of_onQ at links := linksFull,
ps := flatPlacesOf linksFull true, k := noL l d, m := l, t := momL d, P := parL Z G l d,
rad := radRec (recL l d) P, B := blkL Z G l d X arrs, (base, d₁, d₂, e) := L l d.
IT CALLS, AND RETYPES NONE: fOfAt | fInAt | hf_at (WordsAtPlace.lean) · Sound.words_congr
(WordsCongr.lean) · MemsAt · sealed_at
(K1/Law/SealedNoColl.lean) · shown_send (SentShown.lean) · smpHeld_of_sealed
(HeldAtSending.lean) at oracleNoNew and seedReadsBack · K13.Law.piece_step · step_ok.
Main names:
  BookHolds bk     every place of the book names a tree that the book holds
  PlanAt ...       **THE PLAN's SIDE, IN ONE STRUCTURE**: ten fields, each a test on the plan
  planSeats_of     its field seats from the row's laterSeatsB, where every message has a sample
  shown_at_new · sealed_at_new     the two halves, at the fillings' own terms
  new_of           **the call**, at a letter On for the promise in front
  onQ_book · new_of_onQ            **at the table's own promise, at any block under the lot's own**
PREMISES THAT STAY, BY NAME.
  hheld · hshown · hnoColl   three equations on Mg (MgK1's fields; at the composed meaning: rfl).
  PlanAt           mems (MemsAt) · seats · one · pad · row · part · tree · fits (SeatFits) · listed
                   (ListedAt) · told.
  hbase            the piece's base is the plan's number of trees in front of the place.
  hBk · hB2 · hu   on the block's text.
  hholds           BookHolds OF THE BOOK IN FRONT: NO CLAUSE OF THE PROMISE SAYS IT: bookAt counts
                   the trees, the places and the messages; the item "K12.bookInOrder" speaks of the
                   trees' numbers and the count of roots.
  htie             SmpTie at the members at the new seats: ON THE LETTER smp.
IS IT EMPTY HERE? No member of PlanAt is shown; whether hholds and htie can be met is not shown.
What is not claimed. That a message is sealed (the law of a sending gives it, but for the priced
seeds). Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.WordsAtPlace
import Johnson.Desc.K1.Law.WordsCongr
import Johnson.Desc.K1.Law.HeldAtSending
import Johnson.Desc.K1.Law.SealedNoColl
import Johnson.Desc.K1.Law.SentShown
import Johnson.Desc.K1.Law.MemsAt
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Tidy.Fits
import Johnson.Desc.First.Borders
import Johnson.Desc.K13.Law.AtTable
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open Johnson.Pack (portOmZ sigOf)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (Frame Piece strsOf Sending Mem SitsAt MsgT shownJT noCollJT
  SeatFits ListedAt)

variable {Xi Pp Cl Cells Tok : Type} {F : Frame}

/-- Every place of the book names a tree that the book holds. -/
def BookHolds (bk : TreeBook) : Prop :=
  ∀ (o : ℕ) (x : ℕ × ℕ), bk.place[o]? = some x → x.1 < bk.trees.size

/-- **THE PLAN's SIDE OF A SENDING, IN ONE STRUCTURE.** seats: the tenants that the table's numbers
give the place. -/
structure PlanAt (F : Frame) (cs : Codes) (G : FileDescription Xi) (ms : List Mem) (P : Par)
    (rad : ℕ → ℕ) (base : ℕ) (d₁ d₂ : RDT) (seats : List (ℕ × ℕ)) : Prop where
  /-- the list of members and the place fit -/
  mems : MemsAt cs ms P rad base
  /-- each of the table's tenants is the seat, behind base trees, of a message of the place that has
  an OOD sample -/
  seats : ∀ u ∈ seats, ∃ j : Fin (shapesOf P).length, sampledAt P j ∧ u = seatOfMsg P base j.val
  /-- such a message has one answer; its pad can be laid; it has a row -/
  one : ∀ j : Fin (shapesOf P).length, sampledAt P j → (shapeAt P j).answers = 1
  pad : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    (OnBytes.Send.pad P.codes (shapeAt P j)).isSome = true
  row : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    0 < (shapeAt P j).mainRows ∨ 0 < (shapeAt P j).maskRows
  /-- the place's seats part -/
  part : ∀ i i' : ℕ, i < P.sent.size → i' < i →
    ((layOf P).tree.getD i' 0, (layOf P).part.getD i' 0) ≠
      ((layOf P).tree.getD i 0, (layOf P).part.getD i 0)
  /-- the place's trees are among the first round's -/
  tree : ∀ j : Fin (shapesOf P).length, (layOf P).tree.getD j.val 0 < d₁.trees.length
  /-- the members' seats fit the description -/
  fits : ∀ x ∈ ms, SeatFits G cs x.1.l x.1.seat
  /-- the stretch's trees are listed, and told as the data has them -/
  listed : ListedAt F base [d₁, d₂]
  told : ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, G.oracleAt (base + n) = some o →
    o.logLength = sh.a ∧ o.words = sh.W

/-- The field seats, from the row's test on the plan (laterSeatsB, unfolded), where every message of
the place has an OOD sample. -/
theorem planSeats_of {P : Par} {base : ℕ} {seats : List (ℕ × ℕ)}
    (h : First.sameMembers ((List.range P.sent.size).map fun i =>
      (base + (layOf P).tree.getD i 0, (layOf P).part.getD i 0)) seats = true)
    (hs : ∀ j : Fin (shapesOf P).length, sampledAt P j) :
    ∀ u ∈ seats, ∃ j : Fin (shapesOf P).length, sampledAt P j ∧ u = seatOfMsg P base j.val := by
  intro u hu
  unfold First.sameMembers at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have h1 : u ∈ (List.range P.sent.size).map fun i =>
      (base + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) := by simpa using h.2 u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
  exact ⟨⟨i, by simpa [shapesOf] using List.mem_range.1 hi⟩, hs _, rfl⟩

section
variable {cs : Codes} {G : FileDescription Xi} {ms : List Mem} {P : Par} {rad : ℕ → ℕ} {base : ℕ}
  {d₁ d₂ : RDT} {seats : List (ℕ × ℕ)} (H : PlanAt F cs G ms P rad base d₁ d₂ seats)
include H

/-- **"shown" at the place's tenants**, behind a yes of the sending's piece. -/
theorem shown_at_new (c : Block S Cl) (e : ℕ) {W : Type} (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) [d₁, d₂])) (x : S × F.E.Str)
    (hx : (sendPiece (W := W) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ = some x)
    (u : ℕ × ℕ) (hu : u ∈ seats) : shownJT cs G ms u.1 u.2 (strsOf F x.2) := by
  obtain ⟨j, hj, rfl⟩ := H.seats u hu
  refine shown_send c base d₁ d₂ P.coordinates e G cs ms
    (ms.filter fun m => (List.finRange (shapesOf P).length).any fun i =>
      m.1.seat m.2 == seatOfMsg P base i.val) ?_ ?_ H.listed H.told _ _
    (H.mems.sits j hj) ?_ a τ x hx
  · intro m hm
    obtain ⟨i, _, hi⟩ := List.any_eq_true.1 (List.mem_filter.1 hm).2
    exact ⟨(layOf P).tree.getD i.val 0, by rw [eq_of_beq hi]; rfl, H.tree i⟩
  · exact fun m hm => H.fits m (List.mem_filter.1 hm).1
  · intro m hm hs
    refine List.mem_filter.2 ⟨hm, List.any_eq_true.2 ⟨j, List.mem_finRange j, ?_⟩⟩
    have hs' : m.1.seat m.2 = seatOfMsg P base j.val := hs
    rw [hs', beq_self_eq_true]

/-- **"held" and "no collision" at the place's tenants**, behind a yes of the sending's piece at
which every message is sealed at its word off the strings. -/
theorem sealed_at_new
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (c : Block S Cl) (hl : c.rounds.length = 2)
    (hbooked : ∀ s s' r₁ r₂ gs, c.decide s [r₁, r₂] gs = .ok s' →
      Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (e : ℕ) {W : Type} (z : Pp) (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (x : S × F.E.Str)
    (hx : (sendPiece (W := W) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ = some x)
    (hbk : a.1.book.place.size = a.1.st.oracles.size) (hT : a.1.book.trees.size = base)
    (hold : BookHolds a.1.book)
    (htie : ∀ j : Fin (shapesOf P).length, ∀ m ∈ ms,
      SitsAt m (seatOfMsg P base j.val).1 (seatOfMsg P base j.val).2 →
      SmpTie cs smp (z, x.1) m x.1.st (x.1.st.oracles.size - (shapesOf P).length + j.val))
    (hS : ∀ j, sampledAt P j → Sealed P.codes (shapeAt P j) (rad j.val)
      (fOfAt G P rad base x.2 j) x.1.st (x.1.st.oracles.size - (shapesOf P).length + j.val))
    (u : ℕ × ℕ) (hu : u ∈ seats) :
    smpHeld x.1.st x.1.book u.1 u.2 = true ∧
      noCollJT cs G smp ms u.1 u.2 (z, x.1) (strsOf F x.2) := by
  have hsh := shown_at_new H c e a τ x hx u hu
  obtain ⟨j, hj, rfl⟩ := H.seats u hu
  obtain ⟨rs, cols, n, hst⟩ := K13.Law.piece_step _ hx
  obtain ⟨hfit, gs, hd⟩ := step_ok F.ft c _ _ rs cols n hst
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, hl]
  obtain ⟨r₁, r₂, er⟩ := List.length_eq_two.1 hlen
  rw [er] at hd
  have hB := hbooked _ _ _ _ _ hd
  refine ⟨?_, ?_⟩
  · have h1 := smpHeld_of_sealed oracleNoNew seedReadsBack P a.1.book x.1.book _ x.1.st hB hbk hold
      H.part j (rad j.val) _ (hS j hj) (H.one j hj) (H.pad j hj) (H.row j hj)
    rw [hT] at h1
    exact h1
  · have hc := H.mems.codes
    subst hc
    refine sealed_at _ G smp ms _ _ (z, x.1) (strsOf F x.2) fun m hm hs =>
      ⟨hsh.2 m hm hs, shapeAt P j, rad j.val, fOfAt G P rad base x.2 j, x.1.st, _,
        H.mems.shape j hj m hm hs, H.mems.radius j hj m hm hs, ?_, hS j hj, htie j m hm hs⟩
    exact Sound.words_congr G _ m.1.l m.1.seat (strsOf F x.2) m.2 (shapeAt P j) (rad j.val) _ _
      (H.mems.entry j hj m hm hs) hs ⟨0, Nat.zero_lt_succ 0⟩

end

/-- **THE CALL: new_of**: GENERAL IN THE SENDING. On: the promise in front. -/
theorem new_of (cs : Codes) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (Mg : Meaning Pp (Wit Cells Tok MsgT))
    (hheld : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t)
    (hshown : Mg.shown = shownJT cs G ms) (hnoColl : Mg.noColl = noCollJT cs G smp ms)
    (P : Par) (rad : ℕ → ℕ) (base : ℕ) (d₁ d₂ : RDT) (seats : List (ℕ × ℕ))
    (H : PlanAt F cs G ms P rad base d₁ d₂ seats) (c : Block S Cl) (hl : c.rounds.length = 2)
    (hbooked : ∀ s s' r₁ r₂ gs, c.decide s [r₁, r₂] gs = .ok s' →
      Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (e : ℕ) (z : Pp) (On : S × F.E.Str → Prop)
    (hOn : ∀ a, On a → a.1.failed = none → a.1.book.place.size = a.1.st.oracles.size ∧
      a.1.book.trees.size = base ∧ BookHolds a.1.book)
    (htie : ∀ a τ x, On a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ =
        some x →
      ∀ j : Fin (shapesOf P).length, ∀ m ∈ ms,
        SitsAt m (seatOfMsg P base j.val).1 (seatOfMsg P base j.val).2 →
        SmpTie cs smp (z, x.1) m x.1.st (x.1.st.oracles.size - (shapesOf P).length + j.val)) :
    (∃ (fOf : F.E.Str → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
      (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str),
      (∀ y τ, fOf ((sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates
        e).ior.imp y τ) = fIn y τ.1) ∧
      ∀ a τ x, On a → a.1.failed = none →
        (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a
          τ = some x →
        (∀ j, sampledAt P j → Sealed P.codes (shapeAt P j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf P).length + j.val)) →
        ∀ u ∈ seats, Mg.held u.1 u.2 (z, x.1) = true ∧
          Mg.noColl u.1 u.2 (z, x.1) (strsOf F x.2)) ∧
    ∀ a τ x, On a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ =
        some x →
      ∀ u ∈ seats, Mg.shown u.1 u.2 (strsOf F x.2) := by
  refine ⟨⟨fOfAt G P rad base, fun _ m => fInAt F G P rad base d₁ m,
    fun y τ => hf_at G P rad c base d₁ d₂ P.coordinates e H.tree y τ, ?_⟩, ?_⟩
  · intro a τ x ha hm hx hS u hu
    obtain ⟨b1, b2, b3⟩ := hOn a ha hm
    rw [hheld, hnoColl]
    exact sealed_at_new H smp c hl hbooked e z a τ x hx b1 b2 b3 (htie a τ x ha hm hx) hS u hu
  · intro a τ x _ _ hx u hu
    rw [hshown]
    exact shown_at_new H c e a τ x hx u hu

/-! ## At the table of joints' own promise -/

/-- The promise in front of block k, unmarked, holds the clause on the book. -/
theorem onQ_book {W : Type} (N : First.Numbers) (Mg : Meaning Pp W) (links : List First.ModelPart)
    (ps : List Place) (k : ℕ) (z : Pp) (a : S × F.E.Str)
    (ha : Sound.onQ N Mg links ps (fun s : S => (z, s)) k a) (hm : a.1.failed = none) :
    a.1.book.place.size = a.1.st.oracles.size ∧ a.1.book.trees.size = N.treesAt ps[k]? := by
  unfold Sound.onQ First.onAt at ha
  obtain ⟨_, hr⟩ := ha
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨_, c6⟩ := h1
    unfold First.bookAt at c6
    simp only [Bool.and_eq_true, beq_iff_eq] at c6
    exact ⟨c6.1.2, c6.1.1⟩

/-- **new_of AT THE TABLE's PROMISE, AT ANY BLOCK c UNDER THE LOT's OWN BLOCK B**: the form in
which the proof of k01_fifty calls it. hbase: the piece's base is the plan's number of trees in front.
hholds, htie: NAMED PREMISES. -/
theorem new_of_onQ (cs : Codes) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : First.Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT))
    (hheld : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t)
    (hshown : Mg.shown = shownJT cs G ms) (hnoColl : Mg.noColl = noCollJT cs G smp ms)
    (links : List First.ModelPart) (ps : List Place) (k m t : ℕ) (P : Par) (rad : ℕ → ℕ) (base : ℕ)
    (d₁ d₂ : RDT) (H : PlanAt F cs G ms P rad base d₁ d₂ (N.sent m t))
    (hbase : N.treesAt ps[k]? = base) (B : Block S Unit) (hB2 : B.rounds.length = 2)
    (hBk : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' →
      Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (c : Block S Cl) (hu : c.UnderR (B.retype : Block S Cl)) (e : ℕ) (z : Pp)
    (hholds : ∀ a : S × F.E.Str, Sound.onQ N Mg links ps (fun s : S => (z, s)) k a →
      a.1.failed = none → BookHolds a.1.book)
    (htie : ∀ a τ x, Sound.onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ =
        some x →
      ∀ j : Fin (shapesOf P).length, ∀ m' ∈ ms,
        SitsAt m' (seatOfMsg P base j.val).1 (seatOfMsg P base j.val).2 →
        SmpTie cs smp (z, x.1) m' x.1.st (x.1.st.oracles.size - (shapesOf P).length + j.val)) :
    (∃ (fOf : F.E.Str → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
      (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str),
      (∀ y τ, fOf ((sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates
        e).ior.imp y τ) = fIn y τ.1) ∧
      ∀ a τ x, Sound.onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
        (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a
          τ = some x →
        (∀ j, sampledAt P j → Sealed P.codes (shapeAt P j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf P).length + j.val)) →
        ∀ u ∈ N.sent m t, Mg.held u.1 u.2 (z, x.1) = true ∧
          Mg.noColl u.1 u.2 (z, x.1) (strsOf F x.2)) ∧
    ∀ a τ x, Sound.onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ =
        some x →
      ∀ u ∈ N.sent m t, Mg.shown u.1 u.2 (strsOf F x.2) :=
  new_of cs G smp ms Mg hheld hshown hnoColl P rad base d₁ d₂ (N.sent m t) H c
    (by rw [hu.1]; exact hB2) (fun s s' r₁ r₂ gs h => hBk s s' r₁ r₂ gs (hu.2 _ _ _ _ h)) e z
    (Sound.onQ N Mg links ps (fun s : S => (z, s)) k)
    (fun a ha hm => ⟨(onQ_book N Mg links ps k z a ha hm).1,
      (onQ_book N Mg links ps k z a ha hm).2.trans hbase, hholds a ha hm⟩) htie

end VerifiableInference.Desc.K1
