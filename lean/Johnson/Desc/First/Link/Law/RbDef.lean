-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RbDef.lean: A LIGHT FILE, OVER THE TABLE OF CONDITIONS BETWEEN BLOCKS
ALONE (Johnson/Desc/First/Borders.lean): the relation «what the table's promise reads of the
verifier's state is as it was», and the rule by which the table's test on where the chain stands
passes from a place to the next. Cut out of RbRuns.lean and ShapeRides.lean, which import it: so
that every kind's files can call these. Not a letter of a statement turns.

What is said.
  `Rq s s'`: the statement's groups, the book's places, the number of its trees and the number of
    oracle messages are as they were: what the tests on the open rows, the members and the book
    read. `Rb s s'`: the mark, the statement, the book, the number of roots, the stand and the open
    link's number are as they were. `Rb.refl`, `Rb.trans`, `Rb.rq`. `rb_putTl`, `rb_putFork`,
    `rb_putLink`, `rb_head`: four writings that stand in Rb. `shape_step`: **the table's test on the
    state's shape passes from a place to the next**, if the state behind stands where the state in
    front stood; the table asks one stand at the two places, which are of one link; no count of rows
    waits behind, or one may wait there; and the open link's number is as it was. `stand_putLink`,
    `link_putLink`. `NextIn links p p'`: what is asked of two neighbouring places.

Limits. Definitions and small rules. The rows that are owed a count are NOT in Rb. Nothing on
soundness.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart shapeAt standOf standAt mayWait)

/-- What a block whose row closes and opens no class of rows and no pin leaves: the statement's
groups, the book's places, the number of its trees, the number of oracle messages. -/
structure Rq (s s' : S) : Prop where
  groups : s'.st.groups = s.st.groups
  place : s'.book.place = s.book.place
  trees : s'.book.trees.size = s.book.trees.size
  oracles : s'.st.oracles.size = s.st.oracles.size

/-- **What the four Bools read of the verifier's state, but for the rows owed, is as it was.** -/
structure Rb (s s' : S) : Prop where
  failed : s'.failed = s.failed
  st : s'.st = s.st
  book : s'.book = s.book
  roots : s'.roots = s.roots
  stand : standOf s' = standOf s
  num : s'.link?.map (·.link) = s.link?.map (·.link)

theorem Rb.refl (s : S) : Rb s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Rb.trans {s t u : S} (a : Rb s t) (b : Rb t u) : Rb s u :=
  ⟨b.failed.trans a.failed, b.st.trans a.st, b.book.trans a.book, b.roots.trans a.roots,
    b.stand.trans a.stand, b.num.trans a.num⟩

theorem Rb.rq {s s' : S} (a : Rb s s') : Rq s s' :=
  ⟨by rw [a.st], by rw [a.book], by rw [a.book], by rw [a.st]⟩

theorem rb_putTl (s : S) (tl : HTailF2) : Rb s (s.putTl tl) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true <;>
      constructor <;> simp [S.putTl, standOf, S.inLink, S.fork?, S.link?, ho]
  | _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rb_putFork (s : S) (G : Fork) : Rb s (s.putFork G) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true <;>
      constructor <;> simp [S.putFork, standOf, S.inLink, S.fork?, S.link?, ho]
  | _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A writing of the link's context that keeps the link's number. -/
theorem rb_putLink (s : S) (L0 L : LinkCtx) (h : s.link? = some L0) (hl : L.link = L0.link) :
    Rb s (s.putLink L) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true
    · have e : x.L = L0 := by simpa [S.link?, ho] using h
      constructor <;> simp [S.putLink, standOf, S.inLink, S.fork?, S.link?, ho, hl, e]
    · simp [S.link?, ho] at h
  | lay x =>
    have e : x.L = L0 := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl, by show some L.link = some x.L.link; rw [hl, e]⟩
  | att x =>
    have e : x.L = L0 := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl, by show some L.link = some x.L.link; rw [hl, e]⟩
  | _ => exact nomatch h

theorem rb_head (s : S) (a : First.HeadOwn) (G : Fork) (h : s.here = .head a) :
    Rb s { s with here := .head { a with F := G } } := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold standOf S.inLink S.fork?
    rw [h]
    by_cases ho : a.opened = true <;> simp [ho]
  · unfold S.link?
    rw [h]

/-- **The test on the state's shape passes from a place to the next.** -/
theorem shape_step (links : List ModelPart) (p p' : Place) (a b : S)
    (h : shapeAt links (some p) a = true) (hst : standOf b = standOf a)
    (hat : standAt links p' = standAt links p) (hpl : p'.link = p.link)
    (hw : b.noneWaits = true ∨ mayWait links p' = true)
    (hl : b.link?.map (·.link) = a.link?.map (·.link)) : shapeAt links (some p') b = true := by
  have h' : (standOf a == standAt links p && (a.noneWaits || mayWait links p) &&
      a.link?.all fun L => p.link == some L.link) = true := h
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 h'
  obtain ⟨h1, _⟩ := Bool.and_eq_true_iff.1 h12
  show (standOf b == standAt links p' && (b.noneWaits || mayWait links p') &&
      b.link?.all fun L => p'.link == some L.link) = true
  rw [hst, hat, h1, hpl]
  have e2 : (b.noneWaits || mayWait links p') = true := by
    rcases hw with e | e <;> simp [e]
  rw [e2]
  have e3 : (b.link?.all fun L => p.link == some L.link) = true := by
    cases hb : b.link? with
    | none => rfl
    | some Lb =>
      rw [hb] at hl
      cases ha : a.link? with
      | none =>
        rw [ha] at hl
        exact nomatch hl
      | some La =>
        rw [ha] at hl h3
        have e : Lb.link = La.link := Option.some.inj hl
        show (p.link == some Lb.link) = true
        rw [e]
        exact h3
  rw [e3]
  rfl

/-- A writing of the link's context turns «here» alone, and keeps which sort of part stands
there. -/
theorem stand_putLink (s : S) (L : LinkCtx) :
    standOf (s.putLink L) = standOf s ∧ (s.putLink L).rowsOwed = s.rowsOwed ∧
      (s.putLink L).st = s.st ∧ (s.putLink L).book = s.book := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true <;>
      simp [S.putLink, standOf, S.inLink, S.fork?, ho]
  | _ => exact ⟨rfl, rfl, rfl, rfl⟩

/-- What is read behind a writing of the link's context, where one is there. -/
theorem link_putLink (s : S) (L0 L : LinkCtx) (h : s.link? = some L0) :
    (s.putLink L).link? = some L := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putLink, S.link?, ho]
    · simp [S.link?, ho] at h
  | lay x => rfl
  | att x => rfl
  | _ => exact nomatch h

/-- What is asked of two neighbouring places. -/
structure NextIn (links : List ModelPart) (p p' : Place) : Prop where
  stand : standAt links p' = standAt links p
  link : p'.link = p.link

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.Rb.rq
#print axioms VerifiableInference.Desc.LinkJoin.rb_putLink
#print axioms VerifiableInference.Desc.LinkJoin.rb_head
#print axioms VerifiableInference.Desc.LinkJoin.shape_step
#print axioms VerifiableInference.Desc.LinkJoin.stand_putLink
#print axioms VerifiableInference.Desc.LinkJoin.link_putLink
