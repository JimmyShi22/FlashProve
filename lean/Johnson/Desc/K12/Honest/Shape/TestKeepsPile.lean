-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestKeepsPile.lean: four things that the proximity test at the finish
of the proof file's first chain leaves as they were: the rows on the table, the codes, an older
oracle message's shape, and an older oracle message's position under the book of trees (below: the
four). They are proved in three settings: where the sub-protocol `atFinish p`
(Johnson/Desc/K12/AtFinish.lean) accepts; from an accepting step of a sub-protocol whose accept
gives that accept; and at number 354 of the first chain's flat list, under the hypothesis `P5J.AtMg`
(Johnson/P5J/AtMg.lean; below: the head). General in the two states, the rounds and the columns; in
the first two settings also in the plan p, under one hypothesis on it. Theorems only. The verifier's
state alone: no prover, no random value, no frame for an honest side.

Why. The reader of the pending rows by the book (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean)
reads one message in the same way at two states at which the codes, the message's shape and its
position are the same, for two witnesses with the same cells and the same two components at that
position (`agree_across`, Johnson/Loose/H2K12/Rides354.lean). The four, as equations at the index
masks' message, are the fields `rows`, `codes`, `shape` and `seatSame` of that file's structure
`Across`. Its other fields are not proved here, and so `Across` is not.

Terms. s is the first chain's state (`S`, Johnson/Desc/First/State.lean) before the test, s' the
state after it. `s.st` is the statement (`Statement`, OnBytes/Iop/Ground.lean: codes, oracle
messages, groups). `s.book` is the book of trees (`TreeBook`, same file: the trees, and each oracle
message's place: where its tree is in the book, and its part there). "Older" is what s has. The rows
on the table are `S.rows`: the list `s.out.pending`; or, where `s.here` is `.mem a` and `a.lin` is
some l, the one row that is read off the claim of l. The position of the oracle message number o
under a book B is what `seatBy noFirst B o` (Johnson/Desc/Sound/TabAt.lean) returns: its tree's own
number (`Tree.number`) and its part there; nothing where B has no place for o, or no tree at that
place. The index masks' message is the oracle message number `s.out.indexMasks`. A sub-protocol
(`Block`, Johnson/Desc/Block.lean) accepts where its `decide` returns `.ok` with the next state. An
accepting step is `StepYes ft blk s s'` (Johnson/Top/H0/Walk/Reach.lean): `blk.step` returns `.ok`
with s', at as many rounds as blk declares and at columns all of which it reads. `atFinish p` is the
test's own block `proximityTestKind guardedProximityTestParts p` (`proximityTestKind`: Johnson/Desc/K12/Frame.lean; `guardedProximityTestParts`:
Johnson/Desc/K12/JoinGuarded.lean), made a block over `S` by `Block.inside`: `enterFinish` makes the
structure inside the test (`T12`, Johnson/Desc/K12/Join.lean) from s, and `leaveFinish` writes its
statement, book and count of roots back into s. The plan p (`P12`, Frame.lean) holds the numbers of
the place of the test; under the head it is `H2U.p12OfMade Zp.made` (Johnson/Desc/K12/AtPlan.lean).
The flat list is `cF.blocksInOrder` (`Chain.blocksInOrder`, Johnson/Desc/Block.lean), numbered from 0. The frame for
an honest side is Johnson/Desc/ProofFile/Honest/Frame.lean.

  `four_at_354`: under the head, from an accepting step of the sub-protocol at number 354: the four
    at the index masks' message, as equations, under two hypotheses on s: s has that message, and
    the message has a position. The number `s.out.indexMasks` is read at s on both sides of the
    equations
  `kept_at_354`: from the same step, at every number i, with no hypothesis on s: the first two as
    equations; the last two as implications: a message that s has at i is there in s' with the same
    shape, and a position that i has under `s.book` is its position under `s'.book`
  `four_of_step`: the conclusion of `four_at_354`, under the same two hypotheses on s, at every plan
    p with `p.answers = 1`, from an accepting step of a sub-protocol blk with `SitsAtFinish p blk`
    (TestKeepsFirst.lean): wherever blk accepts, `atFinish p` accepts at the same state, rounds and
    columns, with the same next state
  `four_of_yes`, `kept_of_yes`: the conclusions of `four_at_354` and `kept_at_354` where
    `atFinish p` accepts and `p.answers = 1`; both at every number i, the first under the two
    hypotheses at i
  `rows_of_yes`: where `atFinish p` accepts: `s'.rows = s.rows`
  `codes_of_yes`: where it accepts and `p.answers = 1` (so also in the next two entries):
    `s'.st.codes = s.st.codes`
  `shapeKept_of_yes`, `shape_of_yes`: a message that s has at a number is there in s' at that number
    with the same shape; the same as an equation between options, at a number below the count of
    messages in s
  `seat_of_yes`: a message that has a position under `s.book` has the same position under `s'.book`
  `laid_of_yes`, `out_of_yes`: what an accept of `atFinish p` unfolds to: s' is s with the
    statement, the book and the count of roots of a structure t' (`T12`); and, where
    `p.answers = 1`, the library's `OutK` holds between a structure that has the statement and the
    book of s, and t'
  `yes_at_354`: under the head, an accepting step at number 354 gives an accept of
    `atFinish (H2U.p12OfMade Zp.made)` from s to s', at some rounds and columns

By what. `Seat.inside_ok`, `Seat.enterFinish_ok` and `Seat.leaveFinish_ok`
(Johnson/Desc/K12/SeatLaws.lean) unfold the accept. The library's `k12_out`
(Johnson/Desc/K12/Law/OutK.lean) gives `OutK`; among its fields are the equation on the codes,
`ShapesKeep` and `BookKeeps` (both OnBytes/Slice/BlkSeat.lean): every place stays, and every older
tree keeps its number. `k12_out` asks for `p.early = true`, which `H2K.JointK.early_of_decide`
(Johnson/Desc/K12/Law/EarlyStep.lean) derives from the accept. `S.rows` reads the fields `here` and
`out` only, which `leaveFinish` does not write: `rows_of_yes` closes by `rfl`. `four_of_step`:
`stepYes_decide` (Johnson/Top/H0/Walk/ReachInv.lean). At number 354: `IM.at_354`
(Johnson/IMR/LastFour.lean), as in TestKeepsAt354.lean, and `answers_at_head` (TestKeepsAt354.lean).

Hypotheses of `four_at_354`. h: the head, `P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF`. hb: blk is the
element number 354 of `cF.blocksInOrder`. hy: `StepYes ft blk s s'`, at any ft. hi: `s.out.indexMasks` is
below `s.st.oracles.size`. hs: `seatBy noFirst s.book s.out.indexMasks` is some pair.

Limits.
- The two hypotheses on s cannot be dropped from the equations. The test sends new messages and
  trees, which are added after the older ones: at a number at which s has no message, or no
  position, s' may have one. That is a reading of the texts; no example is shown here.
- An older tree does not stay word for word: the count of the lists at which it was opened
  (`Tree.lists`, OnBytes/Iop/Ground.lean) rises where the test opens it. That too is a reading of
  the texts: no theorem here states it. Nothing is said here of which trees the test opens.
- One hypothesis on the plan: a sample has one answer (`p.answers = 1`); under the head it is proved
  (`answers_at_head`, TestKeepsAt354.lean).
- The theorems at number 354 are stated under the head, at the format's second hash function
  (`OnBytes.secondHashFunction`, OnBytes/Hash/SecondHashFunction.lean); no example of the head is shown here.
- That `atFinish p` accepts at any state, or that a step at number 354 accepts, is not shown here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.K12.Honest.Shape.TestKeepsAt354
import Johnson.Desc.Sound.TabAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (seatBy noFirst)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open H2K.Out (OutK k12_out)

/-! ## 1 From an accept of `atFinish p` -/

section Yes
variable (p : P12) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))

/-- Where `atFinish p` accepts at s and returns s': s' is s with the statement, the book and the
count of roots of a structure t'. -/
theorem laid_of_yes (h : (atFinish p).decide s rs gs = .ok s') :
    ∃ t' : T12, s' = { s with st := t'.st, book := t'.book, roots := t'.roots } := by
  obtain ⟨t, t', _, _, h3⟩ := (Seat.inside_ok enterFinish _ leaveFinish s s' rs gs).1 h
  exact ⟨t', (Seat.leaveFinish_ok s s' t').1 h3⟩

/-- And the library's `OutK` holds between a structure that has the statement and the book of s, and
t'. -/
theorem out_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') :
    ∃ t t' : T12, t.st = s.st ∧ t.book = s.book ∧ OutK t t' ∧
      s' = { s with st := t'.st, book := t'.book, roots := t'.roots } := by
  obtain ⟨t, t', h1, h2, h3⟩ := (Seat.inside_ok enterFinish _ leaveFinish s s' rs gs).1 h
  obtain ⟨o, _, _, _, rfl⟩ := Seat.enterFinish_ok s t h1
  exact ⟨_, t', rfl, rfl,
    k12_out p (H2K.JointK.early_of_decide p _ t' rs gs h2) ha _ t' rs gs h2,
    (Seat.leaveFinish_ok s s' t').1 h3⟩

/-- **The rows on the table stay.** -/
theorem rows_of_yes (h : (atFinish p).decide s rs gs = .ok s') : s'.rows = s.rows := by
  obtain ⟨t', rfl⟩ := laid_of_yes p s s' rs gs h
  rfl

/-- **The codes stay.** -/
theorem codes_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') :
    s'.st.codes = s.st.codes := by
  obtain ⟨t, t', e1, _, O, rfl⟩ := out_of_yes p s s' rs gs ha h
  show t'.st.codes = s.st.codes
  rw [← e1]
  exact O.codes

/-- **A message that s has is there in s' at the same number, with the same shape.** -/
theorem shapeKept_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') (o : Nat)
    (x : Oracle) (hx : s.st.oracles[o]? = some x) :
    ∃ x', s'.st.oracles[o]? = some x' ∧ x'.shape = x.shape := by
  obtain ⟨t, t', e1, _, O, rfl⟩ := out_of_yes p s s' rs gs ha h
  exact O.shapes o x (by rw [e1]; exact hx)

/-- The same as an equation between options, at a number at which s has a message. -/
theorem shape_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') (o : Nat)
    (ho : o < s.st.oracles.size) :
    (s'.st.oracles[o]?).map (·.shape) = (s.st.oracles[o]?).map (·.shape) := by
  have hx : s.st.oracles[o]? = some s.st.oracles[o] := Array.getElem?_eq_getElem ho
  obtain ⟨x', hx', e⟩ := shapeKept_of_yes p s s' rs gs ha h o _ hx
  rw [hx', hx, Option.map_some, Option.map_some, e]

/-- **A message that has a position under `s.book` has the same position under `s'.book`.** -/
theorem seat_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') (o : Nat)
    (q : Nat × Nat) (hq : seatBy noFirst s.book o = some q) :
    seatBy noFirst s'.book o = some q := by
  obtain ⟨t, t', _, e2, O, rfl⟩ := out_of_yes p s s' rs gs ha h
  unfold seatBy at hq
  obtain ⟨pl, hpl, h2⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 h2
  have hpl' := O.book.place o pl (by rw [e2]; exact hpl)
  obtain ⟨T', hT', _, en, _⟩ := O.book.tree pl.1 T (by rw [e2]; exact hT)
  show seatBy noFirst t'.book o = _
  unfold seatBy
  rw [hpl', Option.bind_some, hT', Option.map_some]
  show some (T'.number, pl.2) = some (T.number, pl.2)
  rw [en]

/-- **The four with no hypothesis on s.** The last two are implications. i: a message's number; any
number is allowed. -/
theorem kept_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') (i : Nat) :
    s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
    (∀ x, s.st.oracles[i]? = some x → ∃ x', s'.st.oracles[i]? = some x' ∧ x'.shape = x.shape) ∧
    ∀ q, seatBy noFirst s.book i = some q → seatBy noFirst s'.book i = some q :=
  ⟨rows_of_yes p s s' rs gs h, codes_of_yes p s s' rs gs ha h,
    shapeKept_of_yes p s s' rs gs ha h i, seat_of_yes p s s' rs gs ha h i⟩

/-- **The four as equations**, where s has a message number i and that message has a position. -/
theorem four_of_yes (ha : p.answers = 1) (h : (atFinish p).decide s rs gs = .ok s') (i : Nat)
    (hi : i < s.st.oracles.size) (hs : (seatBy noFirst s.book i).isSome = true) :
    s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
    (s'.st.oracles[i]?).map (·.shape) = (s.st.oracles[i]?).map (·.shape) ∧
    seatBy noFirst s'.book i = seatBy noFirst s.book i := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨rows_of_yes p s s' rs gs h, codes_of_yes p s s' rs gs ha h,
    shape_of_yes p s s' rs gs ha h i hi, ?_⟩
  rw [hq]
  exact seat_of_yes p s s' rs gs ha h i q hq

end Yes

/-! ## 2 From an accepting step of a sub-protocol -/

/-- The four at the index masks' message, as equations, from an accepting step of a sub-protocol
whose accept gives an accept of `atFinish p` (`SitsAtFinish`, TestKeepsFirst.lean). hi, hs: the two
hypotheses on s. -/
theorem four_of_step {Cl : Type} (p : P12) (ha : p.answers = 1) (ft : Nat) (blk : Block S Cl)
    (hb : SitsAtFinish p blk) (s s' : S) (h : StepYes ft blk s s')
    (hi : s.out.indexMasks < s.st.oracles.size)
    (hs : (seatBy noFirst s.book s.out.indexMasks).isSome = true) :
    s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
    (s'.st.oracles[s.out.indexMasks]?).map (·.shape) =
      (s.st.oracles[s.out.indexMasks]?).map (·.shape) ∧
    seatBy noFirst s'.book s.out.indexMasks = seatBy noFirst s.book s.out.indexMasks := by
  obtain ⟨rs, gs, hd⟩ := stepYes_decide h
  exact four_of_yes p s s' rs gs ha (hb s s' rs gs hd) _ hi hs

/-! ## 3 At number 354, under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}

/-- An accepting step at number 354 gives an accept of `atFinish (H2U.p12OfMade Zp.made)`. -/
theorem yes_at_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some blk) (ft : Nat) (s s' : S) (hy : StepYes ft blk s s') :
    ∃ rs gs, (atFinish (H2U.p12OfMade Zp.made)).decide s rs gs = .ok s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨R, c, -, e⟩ := hy
  obtain ⟨⟨rs, gs, hd⟩, -, -⟩ := IM.at_354 h.scope h.reads O hb e
  exact ⟨rs, gs, hd⟩

/-- **The four at the index masks' message, as equations, from an accepting step at number 354.**
hi, hs: the two hypotheses on s. -/
theorem four_at_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some blk) (ft : Nat) (s s' : S) (hy : StepYes ft blk s s')
    (hi : s.out.indexMasks < s.st.oracles.size)
    (hs : (seatBy noFirst s.book s.out.indexMasks).isSome = true) :
    s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
    (s'.st.oracles[s.out.indexMasks]?).map (·.shape) =
      (s.st.oracles[s.out.indexMasks]?).map (·.shape) ∧
    seatBy noFirst s'.book s.out.indexMasks = seatBy noFirst s.book s.out.indexMasks := by
  obtain ⟨rs, gs, hd⟩ := yes_at_354 h hb ft s s' hy
  exact four_of_yes _ s s' rs gs (answers_at_head h) hd _ hi hs

/-- **The four with no hypothesis on s, from an accepting step at number 354.** The last two are
implications. -/
theorem kept_at_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some blk) (ft : Nat) (s s' : S) (hy : StepYes ft blk s s') (i : Nat) :
    s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
    (∀ x, s.st.oracles[i]? = some x → ∃ x', s'.st.oracles[i]? = some x' ∧ x'.shape = x.shape) ∧
    ∀ q, seatBy noFirst s.book i = some q → seatBy noFirst s'.book i = some q := by
  obtain ⟨rs, gs, hd⟩ := yes_at_354 h hb ft s s' hy
  exact kept_of_yes _ s s' rs gs (answers_at_head h) hd i

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.laid_of_yes
#print axioms ProofFile.Honest.Sh.out_of_yes
#print axioms ProofFile.Honest.Sh.rows_of_yes
#print axioms ProofFile.Honest.Sh.codes_of_yes
#print axioms ProofFile.Honest.Sh.shapeKept_of_yes
#print axioms ProofFile.Honest.Sh.shape_of_yes
#print axioms ProofFile.Honest.Sh.seat_of_yes
#print axioms ProofFile.Honest.Sh.kept_of_yes
#print axioms ProofFile.Honest.Sh.four_of_yes
#print axioms ProofFile.Honest.Sh.four_of_step
#print axioms ProofFile.Honest.Sh.yes_at_354
#print axioms ProofFile.Honest.Sh.four_at_354
#print axioms ProofFile.Honest.Sh.kept_at_354
