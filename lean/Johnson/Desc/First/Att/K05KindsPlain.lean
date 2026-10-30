-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KindsPlain.lean: there are written rounds that are Plain, have the kind's
entries, and bear the format's own kinds of their
names: so the three premises hd, he, hkind of K05_below_fmt (Att/K05Kinds.lean) can be met together.
(plain_exists, Att/K05Plain.lean,
picks the kind "elems" everywhere: at "PSC epsilon" and "PSC values" that is not the format's.)

Main names:
  `KindGood`, `good_eps` … `good_zero`, `kind_entries`, `kind_entriesOf`, `kind_rounds`: the format
    knows each of the kind's six names, and
    its kind is neither "sealed" nor "seeds".
  `plainFmt`, `plain_exists_fmt`.

Limits: that a file's written rounds are these is not said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Kinds
import Johnson.Desc.First.Att.K05Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Flat OnBytes.Maker Fo.Peel
open VerifiableInference.Desc.Part

/-- The format knows the name, and its kind is neither "sealed" nor "seeds". -/
def KindGood (name : String) : Prop := ∃ k, Fmt.kindOf name = some k ∧ k ≠ .sealed ∧ k ≠ .seeds

theorem good_eps : KindGood "PSC epsilon" := ⟨.join, by decide, by decide, by decide⟩
theorem good_round : KindGood "PSC round" := ⟨.elems, by decide, by decide, by decide⟩
theorem good_Y : KindGood "PSC Y" := ⟨.elems, by decide, by decide, by decide⟩
theorem good_values : KindGood "PSC values" := ⟨.nothing, by decide, by decide, by decide⟩
theorem good_bat : KindGood "BAT-sigma" := ⟨.elems, by decide, by decide, by decide⟩
theorem good_zero : KindGood "ZERO" := ⟨.elems, by decide, by decide, by decide⟩

theorem kind_entries (k : MaskedSum.Call) : ∀ e ∈ MaskedSum.entries k, KindGood e.name := by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl := List.mem_singleton.1 he
      exact good_eps
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 he
      exact good_round
  · cases hk : k.ends with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact good_Y
      · obtain rfl := List.mem_singleton.1 he
        exact good_values

theorem kind_entriesOf : ∀ (l : List Stage) (lead : ℕ), ∀ e ∈ entriesOf lead l, KindGood e.name
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, e, h => kind_entriesOf l (lead + n) e h
  | .sum vs x :: l, lead, e, h => by
    rcases List.mem_append.1 (show e ∈ MaskedSum.entries ⟨lead, vs, some x⟩ ++ entriesOf 0 l from h) with h | h
    · exact kind_entries _ e h
    · exact kind_entriesOf l 0 e h
  | .batch rows :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact good_bat
    · exact kind_entriesOf l 0 e h
  | .point n :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact good_zero
    · exact kind_entriesOf l 0 e h

theorem kind_rounds (p : Par) : ∀ e ∈ (rounds p).map (·.entry), KindGood e.name := by
  intro e he
  unfold rounds at he
  rw [List.map_map] at he
  obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
  have := kind_entriesOf _ _ e0 h0
  show KindGood (if e0.drawE == 0 then e0 else { e0 with work := p.work }).name
  split
  · exact this
  · exact this

/-- The written round's data made of an entry, with the format's kind of its name. -/
def plainFmt (e : Fmt.Entry) : RDT :=
  { entry := e, kind := kindFmt e, items := List.replicate (e.msg / 24) .e, trees := [], opens := [], stored := [] }

theorem plain_exists_fmt (p : Par) :
    ∃ ds : List RDT, (∀ d ∈ ds, Plain (toRD d)) ∧ ds.map (·.entry) = (rounds p).map (·.entry) ∧
      ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind := by
  refine ⟨((rounds p).map (·.entry)).map plainFmt, fun d hd => ?_, ?_, fun d hd => ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    obtain ⟨a1, a2, a3, a4⟩ := rounds_ok p e he
    obtain ⟨k, k1, k2, k3⟩ := kind_rounds p e he
    have ek : kindFmt e = k := by
      unfold kindFmt
      rw [k1]
      rfl
    exact ⟨fun it hi => List.eq_of_mem_replicate hi, List.length_replicate, a1, a2, a3,
      (show kindFmt e ≠ Fmt.Kind.sealed by rw [ek]; exact k2), (show kindFmt e ≠ Fmt.Kind.seeds by rw [ek]; exact k3), a4⟩
  · rw [List.map_map]
    exact List.map_id _
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    obtain ⟨k, k1, _, _⟩ := kind_rounds p e he
    show Fmt.kindOf e.name = some (kindFmt e)
    unfold kindFmt
    rw [k1]
    rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.plain_exists_fmt
