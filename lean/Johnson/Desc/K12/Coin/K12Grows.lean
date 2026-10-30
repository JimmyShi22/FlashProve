-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/K12Grows.lean: **THE RECORD's HALF OF THE SECOND TIE AT THE PROXIMITY TEST's
BLOCK ON THE FIRST CHAIN**: "the block's yes hands the grown promise on": the four Bools of the
table's book-keeping that read the record and the plan's numbers alone (`shapeAt`, `rowsHeld`,
`membersHeld`, `bookAt`, Johnson/Desc/First/Borders.lean) and the layer's items, from the border in
front of the block to the border behind it. Statements and proofs. General in the table's letters:
the segments' sorts, the numbers N, the two places p, p', the open sets O, O'.
  `laidFrom_places_len`: what sendings lay has a place for each notice.
  `LaysOnly leave`: the way out lays the kind's statement, book and count of roots into the record
    and turns nothing else. `laysOnly_finish`, `laysOnly_bind`; `LaysOnly.back`: it is a `LaysBack`.
  `GoOn …`: THE PREMISE ON THE PLAN: the plan's numbers of trees and messages at the two places, and
    the plan's lists, go on with what the test's sendings lay.
  `k12_grownAt`: the plan's four tests · the place behind stands at the finish · no class of rows is
    open behind · `GoOn` · B sits on the kind's block behind (enterFinish, leave) · `LaysOnly leave`
    · B's step says yes from s to s': THEN neither record is marked; `shapeAt` at p', `rowsHeld` and
    `membersHeld` at O' hold of s' outright; `bookAt` at p, "K12.bookInOrder", "K12.seatsCarried" of
    s give `bookAt` at p' and the two of s'.
THE RIDER. A block that says no to all has the clause for nothing, as at every block. One that says
yes to all does not sit on the kind's block (`sits_yesAll`, LeadsSits.lean).
Limits. First arm. `GoOn` at the seated plan, and that the seated entry's way out is a `LaysOnly`,
are premises. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.HandsOnBools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers Item ModelPart shapeAt rowsHeld membersHeld bookAt rowSegs
  standAt standOf Stand)
open VerifiableInference.Desc.K12.Door (shapesIn shapesIn_length)
open H2K.JointK

/-- What sendings lay has a place for each notice. -/
theorem laidFrom_places_len (codes : Codes) : ∀ (sends : List (Array OracleNotice)) (base : ℕ)
    (A : Laid), laidFrom codes base sends = some A → A.places.length = (noticesOf sends).length
  | [], _, A, h => by
    cases h
    rfl
  | sent :: rest, base, A, h => by
    obtain ⟨lay, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    have ih := laidFrom_places_len codes rest _ R hR
    simp only [noticesOf, List.flatMap_cons, List.length_append, List.length_map,
      Array.length_toList, placesOf, List.length_range] at ih ⊢
    rw [ih]

/-- The way out lays the kind's statement, book and count of roots, and turns nothing else. -/
def LaysOnly (leave : First.S → T12 → Except String First.S) : Prop :=
  ∀ s t' s', leave s t' = .ok s' → s' = { s with st := t'.st, book := t'.book, roots := t'.roots }

theorem laysOnly_finish : LaysOnly leaveFinish :=
  fun s t' s' h => (Seat.leaveFinish_ok s s' t').1 h

theorem laysOnly_bind {leave : First.S → T12 → Except String First.S} (h : LaysOnly leave)
    (g : First.S → First.S → Except String First.S) (hg : ∀ s m s', g s m = .ok s' → s' = m) :
    LaysOnly fun s t => (leave s t).bind (g s) := by
  intro s t' s' hb
  obtain ⟨m, h1, h2⟩ := H2K.FoldLaw.bind_ok hb
  obtain rfl := hg s m s' h2
  exact h s t' _ h1

theorem LaysOnly.back {leave : First.S → T12 → Except String First.S} (h : LaysOnly leave) :
    LaysBack leave := by
  intro s t' s' e
  rw [h s t' s' e]
  exact ⟨rfl, rfl, rfl⟩

/-- **The premise on the plan**, at the record's codes and count of trees. -/
def GoOn (N : Numbers) (p p' : Place) (π : P12) (L : Laid) (s : First.S) : Prop :=
  ∀ first rest A, π.nums.stages = first :: rest →
    laidFrom s.st.codes s.book.trees.size (sendsFrom π 0 rest) = some A →
    N.treesAt (some p') = N.treesAt (some p) + A.shapes.length ∧
    N.msgsAt (some p') = N.msgsAt (some p) + A.places.length ∧
    (L.places.drop s.book.place.size).take A.places.length = A.places ∧
    (L.shapes.drop s.book.trees.size).take A.shapes.length = A.shapes

/-- **The record's half of the second tie at the proximity test's block.** -/
theorem k12_grownAt {Cl : Type} (links : List ModelPart) (N : Numbers) (p p' : Place) (O' : List Item)
    (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (ho : π.nums.ownMask = false)
    (he : π.early = true) (ha : π.answers = 1) (hp' : standAt links p' = .fin)
    (hO' : rowSegs O' = []) (B : Block First.S Cl)
    (leave : First.S → T12 → Except String First.S)
    (hS : Sits B (proximityTestKind guardedProximityTestParts π : Blk') enterFinish leave) (hl : LaysOnly leave) (L : Door.Laid)
    (ft : ℕ) (s s' : First.S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ)
    (hG : GoOn N p p' π (Door.toTree L) s) (hY : B.step ft s rs cols = .ok (s', n)) :
    (s.failed = none ∧ s'.failed = none) ∧
    shapeAt links (some p') s' = true ∧ rowsHeld N O' s' = true ∧ membersHeld N O' s' = true ∧
    (bookAt N (some p) s = true → bookAt N (some p') s' = true) ∧
    (Door.atFirstBook π.nums.firstTree s = true → Door.atFirstBook π.nums.firstTree s' = true) ∧
    (Door.atFirstSeats L s = true → Door.atFirstSeats L s' = true) := by
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols n hY
  have hYes : StepYes ft (proximityTestKind guardedProximityTestParts π : Blk') enterFinish leave s s' :=
    ⟨t, t', rs, cols, n, e1, e2, e3⟩
  have hs' := hl s t' s' e3
  obtain ⟨o, hh, hw, hf, ht⟩ := Seat.enterFinish_ok s t e1
  have hf0 : s.failed = none := Option.isNone_iff_eq_none.1 hf
  have hH := hands_on π hp ho he ha ft leave hl.back s s' hYes
  refine ⟨⟨hf0, by rw [hs']; exact hf0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : standOf s' = .fin := by
      rw [hs']
      show (match s.here with
        | .between => Stand.between
        | .lay _ => .link .layers
        | .att _ => .link .attention
        | .head _ => if s.inLink then .link .head else .headFront
        | .fin _ => .fin
        | .mem _ => .mem) = _
      rw [hh]
    have h2 : s'.noneWaits = true := by
      rw [hs']
      exact hw
    have h3 : s'.link? = none := by
      rw [hs']
      show (match s.here with
        | .lay a => some a.L
        | .att a => some a.L
        | .head a => if a.opened then some a.L else none
        | _ => none) = _
      rw [hh]
    simp [shapeAt, h1, hp', h2, h3]
  · simp [rowsHeld, hO']
  · simp [membersHeld, hO']
  · intro hb
    simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hb ⊢
    obtain ⟨⟨b1, b2⟩, b3⟩ := hb
    have hm := mask_of_yes π hp ho _ t' ft n rs cols e2
    obtain ⟨gs, hd⟩ := step_decide (proximityTestKind guardedProximityTestParts π : Blk') ft _ t' rs cols n e2
    obtain ⟨first, rest, hs, A, a1, a2, a3⟩ := k12_appends π he ha _ t' _ gs hm hd
    obtain ⟨first', rest', hs2, hsh⟩ := k12_shapes π he ha _ t' _ gs hm hd
    rw [hs] at hs2
    obtain ⟨_, rfl⟩ := List.cons.inj hs2
    subst ht
    obtain ⟨g1, g2, _, _⟩ := hG first rest A hs a1
    have c1 := size_of_shapes a3
    have c2 : t'.book.place.size = s.book.place.size + A.places.length := by
      have := congrArg List.length a2
      rwa [List.length_append, Array.length_toList, Array.length_toList] at this
    have c3 : t'.st.oracles.size = s.st.oracles.size + (noticesOf (sendsFrom π 0 rest)).length := by
      have := congrArg List.length hsh
      rwa [List.length_append, shapesIn_length, shapesIn_length] at this
    have c4 := laidFrom_places_len _ _ _ A a1
    rw [hs']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show t'.book.trees.size = _
      rw [c1, g1, ← b1]
    · show t'.book.place.size = t'.st.oracles.size
      rw [c2, c3, c4, b2]
    · show t'.st.oracles.size = _
      rw [c3, g2, ← b3, c4]
  · exact fun h => (bookStep_iff _ _ _).2 (hH.1 ((bookStep_iff _ _ _).1 h))
  · exact fun h => (seatsPrefix_iff _ _).2 (hH.2.1 (Door.toTree L) ((seatsPrefix_iff _ _).1 h)
      fun first rest A hs hA => (hG first rest A hs hA).2.2)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.laidFrom_places_len
#print axioms VerifiableInference.Desc.K12.Coin.laysOnly_bind
#print axioms VerifiableInference.Desc.K12.Coin.k12_grownAt
