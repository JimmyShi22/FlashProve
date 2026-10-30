-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Plain.lean: a guard: the two premises "every written round is Plain" and
"the written rounds'
entries are the kind's ROUNDS" can be met together, at every place.

Main names:
  `EntOk`, `entries_ok`, `entriesOf_ok`, `rounds_ok`: each of the kind's entries draws no position
    and no matrix entry, has
    logN = 0, and counts no more elements "never 0" than it draws.
  `plainOf`, `plain_exists`.

Limits: a witness that the premises do not fight. That a file's written rounds at the kind's stretch
are these is not said.
Sources: OnBytes/Tie/Pv/Lookup/Forest/FoPeelMeets.lean (Plain); Att/K5Shape.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelT
import Johnson.Desc.First.Att.K5Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Flat OnBytes.Maker Fo.Peel
open VerifiableInference.Desc.Part

def EntOk (e : Fmt.Entry) : Prop := e.poss = 0 ∧ e.logN = 0 ∧ e.trits = 0 ∧ e.drawNZ ≤ e.drawE

theorem entries_ok (k : MaskedSum.Call) : ∀ e ∈ MaskedSum.entries k, EntOk e := by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl := List.mem_singleton.1 he
      exact ⟨rfl, rfl, rfl, Nat.zero_le _⟩
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 he
      exact ⟨rfl, rfl, rfl, Nat.zero_le _⟩
  · cases hk : k.ends with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨rfl, rfl, rfl, le_rfl⟩
      · obtain rfl := List.mem_singleton.1 he
        exact ⟨rfl, rfl, rfl, le_rfl⟩

theorem entriesOf_ok : ∀ (l : List Stage) (lead : ℕ), ∀ e ∈ entriesOf lead l, EntOk e
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, e, h => entriesOf_ok l (lead + n) e h
  | .sum vs x :: l, lead, e, h => by
    rcases List.mem_append.1 (show e ∈ MaskedSum.entries ⟨lead, vs, some x⟩ ++ entriesOf 0 l from h) with h | h
    · exact entries_ok _ e h
    · exact entriesOf_ok l 0 e h
  | .batch rows :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, rfl, rfl, Nat.zero_le _⟩
    · exact entriesOf_ok l 0 e h
  | .point n :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, rfl, rfl, Nat.zero_le _⟩
    · exact entriesOf_ok l 0 e h

theorem rounds_ok (p : Par) : ∀ e ∈ (rounds p).map (·.entry), EntOk e := by
  intro e he
  unfold rounds at he
  rw [List.map_map] at he
  obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
  have := entriesOf_ok _ _ e0 h0
  show EntOk (if e0.drawE == 0 then e0 else { e0 with work := p.work })
  split
  · exact this
  · exact this

/-- The written round's data made of an entry. -/
def plainOf (e : Fmt.Entry) : RDT :=
  { entry := e, kind := .elems, items := List.replicate (e.msg / 24) .e, trees := [], opens := [], stored := [] }

theorem plain_exists (p : Par) :
    ∃ ds : List RDT, (∀ d ∈ ds, Plain (toRD d)) ∧ ds.map (·.entry) = (rounds p).map (·.entry) := by
  refine ⟨((rounds p).map (·.entry)).map plainOf, fun d hd => ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    obtain ⟨a1, a2, a3, a4⟩ := rounds_ok p e he
    exact ⟨fun it hi => List.eq_of_mem_replicate hi, List.length_replicate, a1, a2, a3,
      (show Fmt.Kind.elems ≠ Fmt.Kind.sealed by decide), (show Fmt.Kind.elems ≠ Fmt.Kind.seeds by decide), a4⟩
  · rw [List.map_map]
    exact List.map_id _

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.plain_exists
