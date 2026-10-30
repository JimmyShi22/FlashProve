-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PlanTestsM3.lean: THE FIVE TESTS ON THE PLAN THAT KIND K13's CLAUSE "inside
the promise the two pins fix what the rows on the table read" SPENDS (`det_by_book`,
Johnson/Desc/K13/Law/DetByBook.lean: its premises hL, hshape, hcode, hlen, hbelow), AS TESTS WITH
CODE, each with the lemma "the test's yes gives the premise, to the letter". Definitions and
statements with their proofs. It names no block and no filling.
The letters. L: the plan's list of the messages' seats (tree, part) and of the trees' shapes
(`K12.Door.Laid`). M: the plan's list of the messages' shapes. ms: the members of the sendings. cs:
the plan's code table. N: what the table of joints reads of the plan (`First.Numbers`).
Main names:
  `planIndexSeatB L N` (hL): the plan's list of seats has `N.index` at `N.indexNo`.
  `planIndexShapeB ms M N` (hshape): every member that sits at `N.index` has the shape that the
    plan's list of shapes has at `N.indexNo`.
  `planIndexCodeB M cs N` (hcode): that shape's mask code is in the code table.
  (hlen is a test already: `cs.lengthsOk`.)
  `PlanBelow L N` (hbelow): AT EVERY PLACE p, IN THE LIST OF PLACES OR NOT: the seats of the
    messages that the plan counts in front of p name trees that it counts in front of p. A Prop: p
    ranges over a type without end. `below_of_plan`: it gives hbelow.
  `planBelowB L n told`, `planBelow_withTold`: **AT NUMBERS THAT ARE FILLED OFF WHAT THE BLOCKS TELL
    (`Numbers.withTold`, Johnson/Desc/First/BookNumbers.lean) IT IS A TEST WITH
    CODE**: there both counts are read at one border, and a place that is not in the list reads
    as the last border: so n + 1 borders are all.
  `planM3B`, `PlanM3`, `planM3_of`: the five together.
What is not claimed. That any of these tests says yes at a plan: NONE HAS RUN. That the numbers of
the filling of record are of the form `withTold`: at numbers of another make `PlanBelow` is owed
otherwise. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S Numbers treesTold msgsTold borderOf)
open VerifiableInference.Desc.Sound (Mem SitsAt)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB placesBelowB)

/-- (hL) The plan's list of seats has the index masks' seat at that message's number. -/
def planIndexSeatB (L : Laid) (N : Numbers) : Bool := L.places[N.indexNo]? == some N.index

theorem planIndexSeat_gives {L : Laid} {N : Numbers} (h : planIndexSeatB L N = true) :
    L.places[N.indexNo]? = some N.index := eq_of_beq h

/-- (hshape) Every member at the index masks' seat has the plan's shape of that message. -/
def planIndexShapeB (ms : List Mem) (M : List OracleShape) (N : Numbers) : Bool :=
  ms.all fun m => !(m.1.seat m.2 == N.index) || (M[N.indexNo]? == some (m.1.l.get m.2).1)

theorem planIndexShape_gives {ms : List Mem} {M : List OracleShape} {N : Numbers}
    (h : planIndexShapeB ms M N = true) :
    ∀ m ∈ ms, SitsAt m N.index.1 N.index.2 → M[N.indexNo]? = some (m.1.l.get m.2).1 := by
  intro m hm hs
  have h1 := List.all_eq_true.1 h m hm
  have hs' : m.1.seat m.2 = N.index := hs
  rw [hs', beq_self_eq_true, Bool.not_true, Bool.false_or] at h1
  exact eq_of_beq h1

/-- (hcode) That shape's mask code is in the code table. -/
def planIndexCodeB (M : List OracleShape) (cs : Codes) (N : Numbers) : Bool :=
  (M[N.indexNo]?).all fun sh => decide (sh.maskCode < cs.mask.size)

theorem planIndexCode_gives {M : List OracleShape} {cs : Codes} {N : Numbers}
    (h : planIndexCodeB M cs N = true) :
    ∀ sh, M[N.indexNo]? = some sh → sh.maskCode < cs.mask.size := by
  intro sh hsh
  unfold planIndexCodeB at h
  rw [hsh] at h
  exact of_decide_eq_true h

/-- (hbelow) At every place: the seats of the messages in front name trees in front. -/
def PlanBelow (L : Laid) (N : Numbers) : Prop :=
  ∀ p, placesBelowB L (N.msgsAt p) (N.treesAt p) = true

/-- It gives `det_by_book`'s premise hbelow, to the letter. -/
theorem below_of_plan {L : Laid} {N : Numbers} (h : PlanBelow L N) {Pp : Type} :
    ∀ (x : Pp × S) p, First.bookAt N p x.2 = true → seatsCarriedB L x.2.book = true →
      placesBelowB L x.2.book.place.size x.2.book.trees.size = true := by
  intro x p hb _
  unfold First.bookAt at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  rw [hb.1.1, hb.1.2, hb.2]
  exact h p

/-- The same at the first n + 1 borders, off what the blocks tell. -/
def planBelowB (L : Laid) (n : ℕ) (told : List (List Oracle)) : Bool :=
  (List.range (n + 1)).all fun b => placesBelowB L (msgsTold told b) (treesTold told b)

/-- **At numbers that are filled off what the blocks tell it is that test.** -/
theorem planBelow_withTold {L : Laid} (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (h : planBelowB L ps.length told = true) : PlanBelow L (N.withTold ps told) := by
  intro p
  have hle : borderOf ps p ≤ ps.length := by
    cases p with
    | none => exact Nat.le_refl _
    | some q => exact List.idxOf_le_length
  exact List.all_eq_true.1 h _ (List.mem_range.2 (Nat.lt_succ_of_le hle))

/-- The five premises together. -/
structure PlanM3 (L : Laid) (M : List OracleShape) (ms : List Mem) (cs : Codes) (N : Numbers) :
    Prop where
  hL : L.places[N.indexNo]? = some N.index
  hshape : ∀ m ∈ ms, SitsAt m N.index.1 N.index.2 → M[N.indexNo]? = some (m.1.l.get m.2).1
  hcode : ∀ sh, M[N.indexNo]? = some sh → sh.maskCode < cs.mask.size
  hlen : cs.lengthsOk = true
  hbelow : PlanBelow L N

/-- The five tests together, at numbers off what the blocks tell. -/
def planM3B (L : Laid) (M : List OracleShape) (ms : List Mem) (cs : Codes) (N : Numbers)
    (ps : List Place) (told : List (List Oracle)) : Bool :=
  planIndexSeatB L (N.withTold ps told) && planIndexShapeB ms M (N.withTold ps told) &&
    planIndexCodeB M cs (N.withTold ps told) && cs.lengthsOk && planBelowB L ps.length told

theorem planM3_of {L : Laid} {M : List OracleShape} {ms : List Mem} {cs : Codes} {N : Numbers}
    {ps : List Place} {told : List (List Oracle)} (h : planM3B L M ms cs N ps told = true) :
    PlanM3 L M ms cs (N.withTold ps told) := by
  unfold planM3B at h
  simp only [Bool.and_eq_true] at h
  exact ⟨planIndexSeat_gives h.1.1.1.1, planIndexShape_gives h.1.1.1.2,
    planIndexCode_gives h.1.1.2, h.1.2, planBelow_withTold N ps told h.2⟩

end VerifiableInference.Desc.K13.Law
