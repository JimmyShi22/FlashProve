-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/Proofs.lean: THE PROOFS of the eleven statements of
Johnson/Road/K4/Rec/Statement.lean: "at an unmarked statement inside the table of joints' promise at
a border, the open segment's part of the record reads as the plan says". GLUE: by unfolding the
promise and the items' tests. No draw, no count.

  `three_of_on`: three of the promise's tests. `pub_of_open`: an open public item's test says yes
  at the record. `sizes`: the book has as many
    places, and the statement as many messages, as the plan's number at the border. `inOrder_of`.
  `part_fields`: what `K9.segAt?` lays into the part.
  **`layoutIs`** · **`arraysAre`** · **`seatIs`** · **`rowBitsAre`** · **`placeBitsAre`** ·
  **`whereIs`** · **`maskIs`** · **`maskSeatIs`** · **`arrayInIs`** · **`moment1Is`** ·
  **`treesAre`**: each under the equations and the open items that its statement names.

OBJECT: none of its own. USER: none yet; meant: whoever turns a condition on the record's part into
a test on the plan. LETTERS, filled by nobody: N, Mg, Z, links, ps, k, m and the plan's data.

Limits. As the statements' file says: EVERY EQUATION IS A PREMISE; frame.sentIs AND ledger.treesAre
LIE IN NO COMPOSED FILLING YET AND HAVE RUN NOWHERE; where no unmarked record meets the promise all
hold for nothing. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on
soundness.
-/
import Johnson.Road.K4.Rec.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers start openSets pubSets pubHeld
  bookAt)
open VerifiableInference.Desc.First.FillSent (SentData treeLook sentIsB treesAreB whereIsP maskP
  link_of_sentIs whereIs_of_sentIs maskAt_of_sentIs trees_of_treesAre)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP maskSeatP arrayInP
  atMoment1P seatAt_is rowBits_is placeBits_is)
open VerifiableInference.Desc.K9 (segAt? seatAt maskSeat maskAt arrayIn atMoment1)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.K12.Door (atFirstSeats atFirstShapes)
open VerifiableInference.Desc.Sound (Frame onQ)

/-- What `K9.segAt?` lays into the part. -/
theorem part_fields {s : S} {A : Part9} (h : segAt? s = some A) :
    s.link? = some A.L ∧ s.fork? = some A.F ∧ A.d.st = s.st ∧ A.d.book = s.book := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        rw [← h]
        exact ⟨rfl, rfl, rfl, rfl⟩

section
variable {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {Z : P} {links : List ModelPart}
  {ps : List Place} {k : ℕ} {b : S × Fr.E.Str} {A : Part9}

/-- Three of the promise's six tests at an unmarked statement: "in order", the public items, the
book. -/
theorem three_of_on (h : AtBorder N Mg Z links ps k b A) :
    Mg.inOrder (Z, b.1) = true ∧
      pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) (Z, b.1) = true ∧
      bookAt N ps[k]? b.1 = true := by
  obtain ⟨hB, _⟩ := h.on.2.resolve_left fun x => x h.unmarked
  simp only [Bool.and_eq_true] at hB
  exact ⟨hB.1.1.2, hB.1.2, hB.2⟩

/-- An open public item's test says yes at the record. -/
theorem pub_of_open (h : AtBorder N Mg Z links ps k b A) {q : Pub}
    (hq : OpenAt Mg links ps k q) : Mg.pub q (Z, b.1) = true :=
  List.all_eq_true.mp (three_of_on h).2.1 q (List.mem_append_left _ hq)

/-- The book's places and the statement's messages are as many as the plan says. -/
theorem sizes (h : AtBorder N Mg Z links ps k b A) :
    b.1.book.place.size = N.msgsAt ps[k]? ∧ b.1.st.oracles.size = N.msgsAt ps[k]? := by
  have hb := (three_of_on h).2.2
  simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨hb.1.2.trans hb.2, hb.2⟩

/-- The statement is in order. -/
theorem inOrder_of (h : AtBorder N Mg Z links ps k b A) : Mg.inOrder (Z, b.1) = true :=
  (three_of_on h).1

end

theorem layoutIs : LayoutIs := by
  intro P W Fr N Mg Z links ps k m b A shape layout eL hO h
  have h1 := pub_of_open h hO
  rw [eL m (Z, b.1)] at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  have hL := (part_fields h.part).1
  have e : b.1.live = A.L.check := by
    unfold S.live
    rw [hL]
  rw [← e]
  exact ⟨h1.2, h1.1⟩

theorem arraysAre : ArraysAre := by
  intro P W Fr N Mg Z links ps k m b A arrs eF hO h
  have h1 := pub_of_open h hO
  rw [eF m (Z, b.1)] at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.2
  have hL : (Z, b.1).2.link? = some A.L := (part_fields h.part).1
  rw [hL] at h2
  simpa only [Option.any_some, beq_iff_eq] using h2

theorem seatIs : SeatIs := by
  intro P W Fr N Mg Z links ps k b A L eS hO h own o
  have h1 := pub_of_open h hO
  rw [eS (Z, b.1)] at h1
  rw [(part_fields h.part).2.2.2]
  exact seatAt_is h1 (sizes h).1 own o

theorem rowBitsAre : RowBitsAre := by
  intro P W Fr N Mg Z links ps k b A M eS hO h o part
  have h1 := pub_of_open h hO
  rw [eS (Z, b.1)] at h1
  rw [(part_fields h.part).2.2.1]
  exact rowBits_is h1 (sizes h).2 o part

theorem placeBitsAre : PlaceBitsAre := by
  intro P W Fr N Mg Z links ps k b A M cs eS eC hO h o part
  have h1 := pub_of_open h hO
  rw [eS (Z, b.1)] at h1
  rw [(part_fields h.part).2.2.1]
  exact placeBits_is h1 (sizes h).2 (eC (Z, b.1) (inOrder_of h)) o part

theorem whereIs : WhereIs := by
  intro P W Fr N Mg Z links ps k m b A d eS hO h
  have h1 := pub_of_open h hO
  rw [eS m (Z, b.1)] at h1
  have hL := (part_fields h.part).1
  exact ⟨link_of_sentIs hL h1, whereIs_of_sentIs hL h1⟩

theorem maskIs : MaskIs := by
  intro P W Fr N Mg Z links ps k m b A d shape layout eS eL hO hO' h
  have h1 := pub_of_open h hO
  rw [eS m (Z, b.1)] at h1
  have hL := (part_fields h.part).1
  exact maskAt_of_sentIs hL h1
    (layoutIs P W Fr N Mg Z links ps k m b A shape layout eL hO' h).2

theorem maskSeatIs : MaskSeatIs := by
  intro P W Fr N Mg Z links ps k m b A d shape layout L eS eL eB hO hO' hO'' h own
  have e1 : maskAt A.L.check.frame = maskP shape d m :=
    maskIs P W Fr N Mg Z links ps k m b A d shape layout eS eL hO hO' h
  unfold maskSeat maskSeatP
  rw [e1]
  congr 1
  funext o
  exact seatIs P W Fr N Mg Z links ps k b A L eB hO'' h own o

theorem arrayInIs : ArrayInIs := by
  intro P W Fr N Mg Z links ps k m b A d shape layout arrs L eS eL eF eB hO hO' hF hO'' h own t
  have e1 := arraysAre P W Fr N Mg Z links ps k m b A arrs eF hF h
  have e2 := (layoutIs P W Fr N Mg Z links ps k m b A shape layout eL hO' h).1
  have e3 := (whereIs P W Fr N Mg Z links ps k m b A d eS hO h).2
  have e4 := seatIs P W Fr N Mg Z links ps k b A L eB hO'' h own
  unfold arrayIn arrayInP
  simp only [e1, e2, e3, e4]

theorem moment1Is : Moment1Is := by
  intro P W Fr N Mg Z links ps k m b A d shape layout eS eL hO hO' h c X
  have e1 := (whereIs P W Fr N Mg Z links ps k m b A d eS hO h).1
  have e2 := (layoutIs P W Fr N Mg Z links ps k m b A shape layout eL hO' h).2
  unfold atMoment1 atMoment1P
  rw [e1, e2]
  try rfl

theorem treesAre : TreesAre := by
  intro P W Fr N Mg Z links ps k m b A d eT hO h
  have h1 := pub_of_open h hO
  rw [eT m (Z, b.1)] at h1
  exact trees_of_treesAre (part_fields h.part).2.1 h1

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.layoutIs
#print axioms OnBytes.Road.K4.Rec.arraysAre
#print axioms OnBytes.Road.K4.Rec.seatIs
#print axioms OnBytes.Road.K4.Rec.rowBitsAre
#print axioms OnBytes.Road.K4.Rec.placeBitsAre
#print axioms OnBytes.Road.K4.Rec.whereIs
#print axioms OnBytes.Road.K4.Rec.maskIs
#print axioms OnBytes.Road.K4.Rec.maskSeatIs
#print axioms OnBytes.Road.K4.Rec.arrayInIs
#print axioms OnBytes.Road.K4.Rec.moment1Is
#print axioms OnBytes.Road.K4.Rec.treesAre
