-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskFront.lean: the test `maskAtB` (MaskRow.lean) accepts at a border inside
an open segment: from the table's condition at that border, the two tests `atFirstSeats` and
`atFirstShapes` on the verifier's state, and ONE new test on the open segment's frame. Definitions
with code (two, and a small frame and state for the tests), and theorems with their proofs.

Why. The law of the merge of the claims on the committed table asks `MaskAt` of the verifier's state
in front of the merge (the field mask of `MergeFront`, EntryFront.lean). Its test `maskAtB` reads
three things: which oracle message the open segment's frame names as the one that holds the
segment's mask rows; where the book of trees has that message; how many bits number that message's
mask rows. The second and the third follow from the table's condition at the border (`onQ`: where
the chain stands; the book has a place for every message; how many messages there are) and from the
two tests `atFirstSeats`, `atFirstShapes` (Johnson/Desc/K12/Door: three files that lie outside the
library's tree as yet, and are compiled in front of this one). The first is read off the frame in
the open segment's own copy of the state of the calls: off FOUR of its fields: shape, next, link and
own (`maskOracle`, `whereIs`). The fixed tests of the table's condition (`shapeAt`, `rowsHeld`,
`membersHeld`, `bookAt`, `samplesHeld`) and the two tests speak of none of the four; of the
meaning's own tests inside the condition nothing is said here. Of the field shape another file's
statement speaks (that the copy in use has the public shape: the field liveShape of `FoldFacts`): it
is not spent here. So the first stands here as a test of its own, and the theorems take its accept
as a premise.

Main names:
  `maskMsgB O s`: THE NEW TEST, with code: a segment is open, and its frame names the message O as
    the one that holds the segment's mask rows. It does not ask that the statement has a message O,
    and its accept says nothing of the public shape: "which of the segment's messages has mask rows"
    is asked of the frame's own shape at the frame's own number of the segment.
  `maskMsgB_gives`, `maskMsgB_of`: what its accept gives, and what gives it. `maskMsgB_one`: it
    accepts at one number at most.
  `maskNoOf shape l`, `maskOracle_eq`, `maskOracle_iff`: `maskOracle` answers o just where the frame
    stands inside a segment and o is, in the list of the segment's own messages that have been sent,
    at the number of the first of the segment's messages with mask rows.
  NEGATIVE TESTS: `maskMsgB_between` (with `maskMsgB_start`, a state that meets its premise): no
    segment is open; `maskMsgB_no_own`: the frame holds none of the segment's own messages;
    `maskMsgB_outside`: the frame does not stand inside a segment; `maskMsgB_no_rows`: by the
    frame's shape the segment has no message with mask rows (over `maskOracle_outside`,
    `maskOracle_no_rows`, `maskMsgB_of_none`).
  `toyFrame`, `toyOpen`, `toy_accepts`, `toy_rejects`: A SMALL STATE: one segment, one message, with
    one mask row, sent as number 7: the test accepts at 7 and rejects at 8.
  `segAt_reads`, `segAt_of_stand`: the open segment's part (`K9.segAt?`) holds the state's own
    context, statement and book; it is there wherever the state stands inside a segment (`standOf`).
  `standAt_link`: the table's listed stand `standAt` is "inside a segment of this sort" from piece 2
    on, at the output head's segment from piece 3 on.
  `maskAtB_of_parts`: `maskAtB` accepts at a state, from its parts.
  `stand_of_shapeAt`, `sizes_of_bookAt`: two fixed tests inside the table's condition, read.
  `maskAtB_at_border`: THE SAME AT BORDER k, for every statement that meets the table's condition
    there, bears no mark and lies in a family Rch of conditions. Rch is any family; three premises
    on it, at border k alone: `atFirstSeats`, `atFirstShapes` and the new test accept.
  `maskAtB_in_segment`: the same, with the listed stand had from `standAt_link`.

Limits. Three premises are shown of no family here: that `maskMsgB O` accepts at the states that the
verifier reaches, that `atFirstSeats` does, and that `atFirstShapes` does. `maskMsgB` has been
evaluated at no verifier's state of a run; the one state at which it is shown to accept is the small
one. No example at the release's own values is given: that the closed premises (the place at border
k; O below the table's number of messages; x at O in the list L, and among own; R against the list
M at O) can be met there is not shown. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.Model (LinkCtx)
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.K9 (seatAt)

/-! ## The new test -/

/-- **A segment is open, and its frame names the message O as the one that holds the segment's mask
rows.** A test with code on the verifier's state. It reads where the chain stands and the open
segment's frame, and no field of the statement: it does not ask that the statement has a message O.
-/
def maskMsgB (O : ℕ) (s : S) : Bool :=
  (s.link?.bind fun L => maskOracle L.check.frame) == some O

/-- What its accept gives. -/
theorem maskMsgB_gives {O : ℕ} {s : S} (h : maskMsgB O s = true) :
    ∃ L, s.link? = some L ∧ maskOracle L.check.frame = some O := by
  unfold maskMsgB at h
  exact Option.bind_eq_some_iff.1 (eq_of_beq h)

/-- It accepts at one number at most. -/
theorem maskMsgB_one {O O' : ℕ} {s : S} (h : maskMsgB O s = true) (h' : maskMsgB O' s = true) :
    O = O' := by
  unfold maskMsgB at h h'
  exact Option.some.inj ((eq_of_beq h).symm.trans (eq_of_beq h'))

/-- And what gives its accept. -/
theorem maskMsgB_of {O : ℕ} {s : S} {L : LinkCtx} (hL : s.link? = some L)
    (h : maskOracle L.check.frame = some O) : maskMsgB O s = true := by
  simp [maskMsgB, hL, h]

/-- The number, among segment l's messages in the request's shape, of the first with mask rows. -/
def maskNoOf (shape : ReqShape) (l : ℕ) : Option ℕ :=
  ((shape.link[l]?.map (·.messages)).getD []).findIdx? fun x => x.shape.maskRows != 0

/-- `maskOracle`, written over `maskNoOf`. -/
theorem maskOracle_eq (f : ReqFrame) :
    maskOracle f = (maskNoOf f.shape f.link).bind fun m => f.whereIs f.link m := rfl

/-- **What `maskOracle` reads of the frame**: it answers o just where the frame stands inside a
segment, and o is, in the list of the segment's own messages that have been sent, at the number of
the first of the segment's messages with mask rows. -/
theorem maskOracle_iff (f : ReqFrame) (o : ℕ) : maskOracle f = some o ↔
    f.next = .laterOrClose ∧ ∃ m, maskNoOf f.shape f.link = some m ∧ f.own[m]? = some o := by
  rw [maskOracle_eq]
  constructor
  · intro h
    obtain ⟨m, hm, hw⟩ := Option.bind_eq_some_iff.1 h
    unfold ReqFrame.whereIs at hw
    by_cases hn : f.next = .laterOrClose
    · exact ⟨hn, m, hm, by simpa [hn] using hw⟩
    · simp [hn] at hw
  · rintro ⟨hn, m, hm, ho⟩
    rw [hm]
    show f.whereIs f.link m = some o
    unfold ReqFrame.whereIs
    simp [hn, ho]

/-- NEGATIVE TEST: it rejects between two segments. -/
theorem maskMsgB_between (O : ℕ) {s : S} (h : s.here = .between) : maskMsgB O s = false := by
  simp [maskMsgB, S.link?, h]

/-- NEGATIVE TEST: it rejects at the bare state at the start. -/
theorem maskMsgB_start (O : ℕ) (codes : Codes) (check : OnBytes.Model.ChainCheck) :
    maskMsgB O (S.start codes check) = false :=
  maskMsgB_between O rfl

/-- NEGATIVE TEST: it rejects where a segment is open whose frame holds none of its own messages. -/
theorem maskMsgB_no_own (O : ℕ) {s : S} {L : LinkCtx} (hL : s.link? = some L)
    (h : L.check.frame.own = #[]) : maskMsgB O s = false := by
  cases e : maskMsgB O s with
  | false => rfl
  | true =>
    obtain ⟨L', hL', ho⟩ := maskMsgB_gives e
    obtain rfl : L' = L := Option.some.inj (hL'.symm.trans hL)
    obtain ⟨_, m, _, hm⟩ := (maskOracle_iff _ _).1 ho
    rw [h] at hm
    simp at hm

/-- Where the frame does not stand inside a segment, `maskOracle` answers nothing. -/
theorem maskOracle_outside {f : ReqFrame} (h : f.next ≠ .laterOrClose) : maskOracle f = none := by
  cases e : maskOracle f with
  | none => rfl
  | some o => exact absurd ((maskOracle_iff f o).1 e).1 h

/-- Where, by the frame's shape, the segment has no message with mask rows, it answers nothing. -/
theorem maskOracle_no_rows {f : ReqFrame} (h : maskNoOf f.shape f.link = none) :
    maskOracle f = none := by
  rewrite [maskOracle_eq, h]
  rfl

/-- Where a segment is open and `maskOracle` answers nothing at its frame, the test rejects. -/
theorem maskMsgB_of_none (O : ℕ) {s : S} {L : LinkCtx} (hL : s.link? = some L)
    (h : maskOracle L.check.frame = none) : maskMsgB O s = false := by
  simp [maskMsgB, hL, h]

/-- NEGATIVE TEST: it rejects where the open segment's frame does not stand inside a segment. -/
theorem maskMsgB_outside (O : ℕ) {s : S} {L : LinkCtx} (hL : s.link? = some L)
    (h : L.check.frame.next ≠ .laterOrClose) : maskMsgB O s = false :=
  maskMsgB_of_none O hL (maskOracle_outside h)

/-- NEGATIVE TEST: it rejects where, by the frame's shape, the segment has no message with mask
rows. -/
theorem maskMsgB_no_rows (O : ℕ) {s : S} {L : LinkCtx} (hL : s.link? = some L)
    (h : maskNoOf L.check.frame.shape L.check.frame.link = none) : maskMsgB O s = false :=
  maskMsgB_of_none O hL (maskOracle_no_rows h)

/-! ## A small state -/

/-- A small frame: one segment with one message, which has one mask row; the frame stands inside
that segment, and the message has been sent as number 7. -/
def toyFrame : ReqFrame :=
  { shape := { (default : ReqShape) with
      link := [{ plain := 0
                 messages := [{ shape := { maskRows := 1 }, leafClass := 0, moment := 0,
                                life := 0 }] }] }
    groups := #[], next := .laterOrClose, link := 0, own := #[7] }

/-- A state in which a segment is open at that frame; all else is as in s, F, tl. -/
def toyOpen (s : S) (F : OnBytes.Model.Fork) (tl : OnBytes.Model.HTailF2) : S :=
  { s with here := .lay { L := { check := { frame := toyFrame, rows := ⟨default⟩ } }, F := F,
                          tl := tl } }

/-- **The test accepts at the small state, at 7.** -/
theorem toy_accepts (s : S) (F : OnBytes.Model.Fork) (tl : OnBytes.Model.HTailF2) :
    maskMsgB 7 (toyOpen s F tl) = true :=
  maskMsgB_of (L := { check := { frame := toyFrame, rows := ⟨default⟩ } }) rfl
    ((maskOracle_iff _ _).2 ⟨rfl, 0, rfl, rfl⟩)

/-- NEGATIVE TEST: it rejects there at 8. -/
theorem toy_rejects (s : S) (F : OnBytes.Model.Fork) (tl : OnBytes.Model.HTailF2) :
    maskMsgB 8 (toyOpen s F tl) = false := by
  cases e : maskMsgB 8 (toyOpen s F tl) with
  | false => rfl
  | true => exact absurd (maskMsgB_one (toy_accepts s F tl) e) (by decide)

/-! ## The open segment's part -/

/-- The open segment's part holds the state's own context, statement and book. -/
theorem segAt_reads {s : S} {a9 : K9.Part} (h : K9.segAt? s = some a9) :
    s.link? = some a9.L ∧ a9.d.st = s.st ∧ a9.d.book = s.book := by
  unfold K9.segAt? at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨L, hL, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨F, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  exact ⟨hL, rfl, rfl⟩

/-- **The part is there wherever the state stands inside a segment.** At the output head's segment
"inside" says that the segment's context and ledger are laid. -/
theorem segAt_of_stand {s : S} {sub : ModelPart} (h : standOf s = .link sub) :
    ∃ a9, K9.segAt? s = some a9 := by
  have key : ∃ L F tl, s.link? = some L ∧ s.fork? = some F ∧ s.tl? = some tl := by
    cases e : s.here with
    | between => simp [standOf, e] at h
    | lay a =>
      exact ⟨a.L, a.F, a.tl, by simp [S.link?, e], by simp [S.fork?, e], by simp [S.tl?, e]⟩
    | att a =>
      exact ⟨a.L, a.F, a.tl, by simp [S.link?, e], by simp [S.fork?, e], by simp [S.tl?, e]⟩
    | head a =>
      cases ho : a.opened with
      | false => simp [standOf, S.inLink, S.fork?, e, ho] at h
      | true =>
        exact ⟨a.L, a.F, a.tl, by simp [S.link?, e, ho], by simp [S.fork?, e, ho],
          by simp [S.tl?, e, ho]⟩
    | fin a => simp [standOf, e] at h
    | mem a => simp [standOf, e] at h
  obtain ⟨L, F, tl, hL, hF, ht⟩ := key
  refine ⟨{ owed := K9.owedOf s, used := (K9.usedOf s).getD 0, laid := K9.laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } }, ?_⟩
  unfold K9.segAt?
  rw [hL, hF, ht]
  rfl

/-- **The table's listed stand is "inside a segment of this sort"** from piece 2 on; at the output
head's segment from piece 3 on. -/
theorem standAt_link {links : List ModelPart} {p : Place} {m : ℕ} {sub : ModelPart} (hl : p.link = some m)
    (hs : links[m]? = some sub) (h2 : 2 ≤ p.piece) (hh : sub = .head → 3 ≤ p.piece) :
    standAt links p = .link sub := by
  have h1 : ¬ p.piece ≤ 1 := by omega
  have hc : (sub == ModelPart.head && p.piece == 2) = false := by
    by_cases e : sub = .head
    · have h3 := hh e
      have e2 : (p.piece == 2) = false := beq_false_of_ne (by omega)
      rw [e2, Bool.and_false]
    · rw [beq_false_of_ne e, Bool.false_and]
  unfold standAt
  rw [hl]
  show (if p.piece ≤ 1 then Stand.between
    else if ((links[m]?).getD .layers == ModelPart.head && p.piece == 2) = true then Stand.headFront
    else Stand.link ((links[m]?).getD .layers)) = Stand.link sub
  rw [hs, Option.getD_some, if_neg h1, hc, if_neg Bool.false_ne_true]

/-! ## The test of MaskRow.lean, from its parts -/

/-- **`maskAtB` accepts at a state**: where the open segment's part is there; the message that holds
the segment's mask rows is number O; the book's places and the statement's messages' shapes are the
first of the lists L and M; the book has a place for every message; O is below the number of
messages; the list L has the place x at O, one of own; and R bits number the mask rows of the shape
that the list M has at O. -/
theorem maskAtB_of_parts {own : List (ℕ × ℕ)} {x : ℕ × ℕ} {R O : ℕ} {L : K12.Door.Laid}
    {M : List OracleShape} {s : S} {a9 : K9.Part} (h9 : K9.segAt? s = some a9)
    (hmsg : maskMsgB O s = true) (hseats : K12.Door.atFirstSeats L s = true)
    (hshapes : K12.Door.atFirstShapes M s = true)
    (hsize : s.book.place.size = s.st.oracles.size) (hO : O < s.st.oracles.size)
    (hx : L.places[O]? = some x) (hown : x ∈ own)
    (hR : (M[O]?).map (fun y => ceilLog2 y.maskRows) = some R) : maskAtB own x R s = true := by
  obtain ⟨hL, hst, hbk⟩ := segAt_reads h9
  have ho : maskOracle a9.L.check.frame = some O := by
    obtain ⟨L', hL', ho⟩ := maskMsgB_gives hmsg
    obtain rfl : L' = a9.L := Option.some.inj (hL'.symm.trans hL)
    exact ho
  have hp : s.book.place[O]? = some x := by
    unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at hseats
    simp only [Bool.and_eq_true] at hseats
    have e : s.book.place.toList = L.places.take s.book.place.size := eq_of_beq hseats.1.1.1
    have hlt : O < s.book.place.size := by
      rw [hsize]
      exact hO
    rw [← Array.getElem?_toList, e, List.getElem?_take_of_lt hlt]
    exact hx
  have hs : seatAt own a9.d.book O = some x := by
    unfold seatAt
    rw [hbk, hp]
    show (if own.contains x = true then some x else none) = some x
    rw [if_pos (List.contains_iff_mem.2 hown)]
  have hr : a9.d.st.rowBits O .mask = R := by
    rw [hst]
    have e := K12.Door.msgShape_at (show K12.Door.msgShapesB M s.st = true from hshapes) O hO
    rw [← e] at hR
    cases eo : s.st.oracles[O]? with
    | none =>
      rw [eo] at hR
      simp at hR
    | some y =>
      rw [eo] at hR
      have hR' : ceilLog2 y.shape.maskRows = R := Option.some.inj hR
      unfold OnBytes.Statement.rowBits
      rw [eo]
      exact hR'
  unfold maskAtB
  rw [h9]
  simp only [Option.any_some]
  rw [ho]
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hs, hr⟩

/-! ## At a border of the table -/

/-- The table's fixed test on where the chain stands, read. -/
theorem stand_of_shapeAt {links : List ModelPart} {p : Place} {s : S}
    (h : First.shapeAt links (some p) s = true) : standOf s = standAt links p := by
  unfold First.shapeAt at h
  simp only [Bool.and_eq_true] at h
  exact eq_of_beq h.1.1

/-- The table's fixed test on the book and the number of messages, read. -/
theorem sizes_of_bookAt {Nn : Numbers} {p : Option Place} {s : S} (h : bookAt Nn p s = true) :
    s.book.place.size = s.st.oracles.size ∧ s.st.oracles.size = Nn.msgsAt p := by
  unfold bookAt at h
  simp only [Bool.and_eq_true] at h
  exact ⟨eq_of_beq h.1.2, eq_of_beq h.2⟩

/-- **`maskAtB` ACCEPTS AT BORDER k**, at every statement that meets the table's condition there,
lies in the family Rch and bears no mark. p: the place of the sub-protocol behind the border; the
table's listed stand there is "a segment stands open". O: the number that the frame is to name,
below the table's number of messages at p. Of the family, at border k alone: `atFirstSeats`,
`atFirstShapes` and `maskMsgB O` accept at its unmarked states; the last is asked only where the
statement has the table's number of messages, which the table's condition says. -/
theorem maskAtB_at_border {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (own : List (ℕ × ℕ)) (x : ℕ × ℕ) (R O k : ℕ) (L : K12.Door.Laid)
    (M : List OracleShape) (p : Place) (sub : ModelPart) (hp : ps[k]? = some p)
    (hstand : standAt links p = .link sub) (hO : O < Nn.msgsAt (some p))
    (hx : L.places[O]? = some x) (hown : x ∈ own)
    (hR : (M[O]?).map (fun y => ceilLog2 y.maskRows) = some R)
    (hseats : ∀ a, Rch k a → a.1.2.failed = none → K12.Door.atFirstSeats L a.1.2 = true)
    (hshapes : ∀ a, Rch k a → a.1.2.failed = none → K12.Door.atFirstShapes M a.1.2 = true)
    (hmsg : ∀ a, Rch k a → a.1.2.failed = none →
      a.1.2.st.oracles.size = Nn.msgsAt (some p) → maskMsgB O a.1.2 = true) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → maskAtB own x R a.1 = true := by
  intro z a hon hr hf
  unfold Sound.onQ onAt at hon
  obtain ⟨_, hmk | ⟨hb, _⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨hsh, _⟩, _⟩, _⟩, _⟩, hbk⟩ := hb
    rw [hp] at hsh hbk
    have hst : standOf a.1 = standAt links p := stand_of_shapeAt hsh
    obtain ⟨hsize, hcount⟩ : a.1.book.place.size = a.1.st.oracles.size ∧
        a.1.st.oracles.size = Nn.msgsAt (some p) := sizes_of_bookAt hbk
    obtain ⟨a9, h9⟩ := segAt_of_stand (hst.trans hstand)
    exact maskAtB_of_parts h9 (hmsg _ hr hf hcount) (hseats _ hr hf) (hshapes _ hr hf) hsize
      (Nat.lt_of_lt_of_eq hO hcount.symm) hx hown hR

/-- **The same, with the listed stand had from `standAt_link`**: the sub-protocol behind border k is
piece 2 or a later one of segment m, of the sort sub; at the output head's segment piece 3 or a
later one. -/
theorem maskAtB_in_segment {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (own : List (ℕ × ℕ)) (x : ℕ × ℕ) (R O k : ℕ) (L : K12.Door.Laid)
    (M : List OracleShape) (p : Place) (m : ℕ) (sub : ModelPart) (hp : ps[k]? = some p)
    (hl : p.link = some m) (hs : links[m]? = some sub) (h2 : 2 ≤ p.piece)
    (hh : sub = .head → 3 ≤ p.piece) (hO : O < Nn.msgsAt (some p))
    (hx : L.places[O]? = some x) (hown : x ∈ own)
    (hR : (M[O]?).map (fun y => ceilLog2 y.maskRows) = some R)
    (hseats : ∀ a, Rch k a → a.1.2.failed = none → K12.Door.atFirstSeats L a.1.2 = true)
    (hshapes : ∀ a, Rch k a → a.1.2.failed = none → K12.Door.atFirstShapes M a.1.2 = true)
    (hmsg : ∀ a, Rch k a → a.1.2.failed = none →
      a.1.2.st.oracles.size = Nn.msgsAt (some p) → maskMsgB O a.1.2 = true) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → maskAtB own x R a.1 = true :=
  maskAtB_at_border Rch Nn Mg links ps own x R O k L M p sub hp (standAt_link hl hs h2 hh) hO hx
    hown hR hseats hshapes hmsg

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_gives
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_one
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_of
#print axioms VerifiableInference.Desc.First.MergeLaw.maskOracle_eq
#print axioms VerifiableInference.Desc.First.MergeLaw.maskOracle_iff
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_between
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_start
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_no_own
#print axioms VerifiableInference.Desc.First.MergeLaw.maskOracle_outside
#print axioms VerifiableInference.Desc.First.MergeLaw.maskOracle_no_rows
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_of_none
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_outside
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_no_rows
#print axioms VerifiableInference.Desc.First.MergeLaw.toy_accepts
#print axioms VerifiableInference.Desc.First.MergeLaw.toy_rejects
#print axioms VerifiableInference.Desc.First.MergeLaw.segAt_reads
#print axioms VerifiableInference.Desc.First.MergeLaw.segAt_of_stand
#print axioms VerifiableInference.Desc.First.MergeLaw.standAt_link
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAtB_of_parts
#print axioms VerifiableInference.Desc.First.MergeLaw.stand_of_shapeAt
#print axioms VerifiableInference.Desc.First.MergeLaw.sizes_of_bookAt
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAtB_at_border
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAtB_in_segment
