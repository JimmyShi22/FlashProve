-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeTwoOfSits.lean: THE DOOR'S TWO CLAUSES ON THE OWN GROUP (`ownTwoB`,
Johnson/Desc/Last/OwnTwo.lean: two members, each with one sample row) FROM "WHICH MESSAGES SIT
WHERE" (`ownSitsB V`, Johnson/Desc/Last/OwnSits.lean: a test) AND WHAT THE FIRST
TABLE'S PROMISE HOLDS ANYWAY. Statements and proofs; no definition.

Main names (namespace `VerifiableInference.Desc.Last`).
  `place_of_oracleNo`: the number that `oracleNo book j t` gives (Johnson/Desc/SmpRows.lean) has the
    place (j, t) in the book. `rows_at_place`: where the verifier's state holds a tenant's
    out-of-domain (OOD) sample (`smpHeld`) and the book fits (`bookFitsB`: two messages have two
    places: `places_inj`, Johnson/Desc/Book/BookFits.lean), the message that has the tenant's place
    has as many sample rows as its shape counts answers.
  **`ownTwoB_of_sits`**: `ownTwoB s` from: hs: `ownSitsB V s` · hb: `bookFitsB s.book` · hI, hW:
    `smpHeld` at the plan's two places · aI, aW: the plan's two shapes count one answer.

Every "there is": x (`rows_at_place`): tied by `oracles[i]? = some x`.
Limits. A joining on one state: none of the six is shown here. So no item of the promise need say
"one sample row each". NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeWhichMembers
import Johnson.Desc.Last.OwnTwo
import Johnson.Desc.Last.OwnSits
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Sound (bookFitsB bookFitsB_iff)
open VerifiableInference.Desc.Book (places_inj)

/-- The number that `oracleNo` gives has that place in the book. -/
theorem place_of_oracleNo {book : TreeBook} {j t i : ℕ} (h : oracleNo book j t = some i) :
    book.place[i]? = some (j, t) := by
  unfold oracleNo at h
  have := List.find?_some h
  simpa using this

/-- **Where the verifier's state holds a tenant's OOD sample and the book fits, the message that
has the tenant's place has as many sample rows as its shape counts answers.** -/
theorem rows_at_place {st : Statement} {book : TreeBook} {q : ℕ × ℕ} {i : ℕ}
    (hb : bookFitsB book = true) (h : smpHeld st book q.1 q.2 = true)
    (hi : book.place[i]? = some q) :
    ∃ x, st.oracles[i]? = some x ∧ x.sampleRows.size = x.shape.answers := by
  obtain ⟨i', x, ho, hx, hr⟩ := rows_of_held h
  obtain rfl : i' = i := places_inj ((bookFitsB_iff book).1 hb) (place_of_oracleNo ho) hi
  exact ⟨x, hx, hr⟩

/-- **THE DOOR's TWO CLAUSES ON THE OWN GROUP, FROM "WHICH MESSAGES SIT WHERE"**: `ownTwoB` from
`ownSitsB V`, the book's fit, the two tenants' OOD samples held, and one answer at each of the
plan's two shapes. -/
theorem ownTwoB_of_sits {V : OwnSeats} {s : First.S} (hs : ownSitsB V s = true)
    (hb : bookFitsB s.book = true) (hI : smpHeld s.st s.book V.index.1 V.index.2 = true)
    (hW : smpHeld s.st s.book V.w.1 V.w.2 = true) (aI : V.indexShape.answers = 1)
    (aW : V.wShape.answers = 1) : ownTwoB s = true := by
  unfold ownTwoB
  cases hf : firstOfS s with
  | none => rfl
  | some f =>
    obtain ⟨_, _, e1, e2, _⟩ := firstOfS_at hf
    obtain ⟨G, i₁, i₂, hG, hm, p1, p2, s1, s2⟩ := (ownSitsB_iff V s).1 hs f hf
    rw [e2] at p1 p2
    rw [e1] at s1 s2
    obtain ⟨x₁, g1, r1⟩ := rows_at_place hb hI p1
    obtain ⟨x₂, g2, r2⟩ := rows_at_place hb hW p2
    rw [g1] at s1
    rw [g2] at s2
    have t1 : x₁.shape = V.indexShape := Option.some.inj s1
    have t2 : x₂.shape = V.wShape := Option.some.inj s2
    show (match f.st.groups[f.own]? with
      | some G => G.members.size == 2 && G.members.toList.all fun i =>
          match f.st.oracles[i]? with
          | some x => x.sampleRows.size == 1
          | none => false
      | none => false) = true
    rw [hG]
    have hsz : G.members.size = 2 := by rw [← Array.length_toList, hm]; rfl
    rw [e1]
    simp only [hm, hsz, List.all_cons, List.all_nil, g1, g2, r1, r2, t1, t2, aI, aW,
      beq_self_eq_true, Bool.and_true]

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.place_of_oracleNo
#print axioms VerifiableInference.Desc.Last.rows_at_place
#print axioms VerifiableInference.Desc.Last.ownTwoB_of_sits
