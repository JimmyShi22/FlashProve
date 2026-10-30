-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/Entries.lean: the kind "lookup" (K3): facts on the rounds
that the verifier's text hears at a lookup, as entries of the plan (`entriesV`,
Johnson/Desc/First/Look/Via/Rounds.lean), and on a list of the plan's entries that passes the
verifier's test on them (`entriesFit`, same file). Theorems on public data.

Terms. Honest/K3/GLOSSARY.md. In this file: f is a lookup's face; es is a list of the plan's
entries. `KindGood` (Johnson/Desc/First/Att/K05KindsPlain.lean): the format
knows the name, and its kind is neither "sealed" nor "seeds".

What is shown.
  `good_shift`, `good_lkp`, `good_join`, `good_line`: four names of rounds pass `KindGood`.
  `entriesV_tame`: every round of the verifier's list has logN = 0, asks no more elements other
    than 0 than elements, and has a name that passes `KindGood`. No hypothesis.
  `fit_at`, `fit_mem`: a list that passes the test is the verifier's list but for the work bits: by
    number, and by membership.
Helpers: `tame_sum`, `tame_level`, `tame_run`, `fit_eq`.

Hypotheses that remain. `hes`: the list passes the verifier's test.

Users. The files of this folder.

Limits. No sampled value is read. Nothing is said of how a round's challenges are distributed.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages
import Johnson.Desc.First.Att.K05KindsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc.Part (MaskedSum.entries MaskedSum.entry)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.K3 (entriesV entriesFit drawEntry)
open VerifiableInference.Desc.First.ProdV (levelEntries runEntries)
open VerifiableInference.Desc.First.Att.P (KindGood kind_entries good_zero)

/-! ## 1 Four names -/

theorem good_shift : KindGood "LKP shift" := ⟨.elems, by decide, by decide, by decide⟩
theorem good_lkp : KindGood "LKP" := ⟨.elems, by decide, by decide, by decide⟩
theorem good_join : KindGood "JOIN" := ⟨.elems, by decide, by decide, by decide⟩
theorem good_line : KindGood "LINE" := ⟨.elems, by decide, by decide, by decide⟩

/-! ## 2 The verifier's list -/

/-- The rounds of a masked sumcheck. -/
theorem tame_sum (k : Call) :
    ∀ e ∈ MaskedSum.entries k, e.logN = 0 ∧ e.drawNZ ≤ e.drawE ∧ KindGood e.name := by
  intro e he
  have hk := kind_entries k e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with h | h
  · rcases List.mem_append.1 h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨rfl, Nat.zero_le _, hk⟩
    · obtain ⟨_, _, e2⟩ := List.mem_map.1 h
      subst e2
      exact ⟨rfl, Nat.zero_le _, hk⟩
  · cases hc : k.ends with
    | none => simp [hc] at h
    | some e' =>
      simp only [hc, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · subst h
        exact ⟨rfl, Nat.le_refl _, hk⟩
      · subst h
        exact ⟨rfl, Nat.le_refl _, hk⟩

/-- The rounds of a level of a product tree. -/
theorem tame_level (m : Nat) :
    ∀ e ∈ levelEntries m, e.logN = 0 ∧ e.drawNZ ≤ e.drawE ∧ KindGood e.name := by
  intro e he
  unfold levelEntries at he
  rcases List.mem_append.1 he with h | h
  · exact tame_sum _ e h
  · obtain rfl := List.mem_singleton.1 h
    exact ⟨rfl, Nat.zero_le _, good_line⟩

/-- The rounds of a run of levels. -/
theorem tame_run (m0 n : Nat) :
    ∀ e ∈ runEntries m0 n, e.logN = 0 ∧ e.drawNZ ≤ e.drawE ∧ KindGood e.name := by
  intro e he
  unfold runEntries at he
  obtain ⟨i, _, h⟩ := List.mem_flatMap.1 he
  exact tame_level _ e h

/-- Every round of the verifier's list: logN is 0; no more never-0 elements than elements; a
name whose kind is neither sealed nor seeds. -/
theorem entriesV_tame (f : LFace) :
    ∀ e ∈ entriesV f, e.logN = 0 ∧ e.drawNZ ≤ e.drawE ∧ KindGood e.name := by
  intro e he
  unfold entriesV at he
  simp only [List.mem_append] at he
  rcases he with (((((((((hA | hB) | hC) | hD) | hE) | hF) | hG) | hH) | hI) | hJ) | hK
  · split at hA
    · obtain rfl := List.mem_singleton.1 hA
      exact ⟨rfl, Nat.zero_le _, good_shift⟩
    · exact absurd hA List.not_mem_nil
  · obtain rfl := List.mem_singleton.1 hB
    exact ⟨rfl, Nat.zero_le _, good_lkp⟩
  · exact tame_sum _ e hC
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 hD
    exact tame_sum _ e h
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 hE
    exact tame_sum _ e h
  · obtain rfl := List.mem_singleton.1 hF
    exact ⟨rfl, Nat.zero_le _, good_join⟩
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 hG
    exact tame_run _ _ e h
  · exact tame_run _ _ e hH
  · exact tame_sum _ e hI
  · obtain rfl := List.mem_singleton.1 hJ
    exact ⟨rfl, Nat.zero_le _, good_zero⟩
  · exact tame_sum _ e hK

/-! ## 3 A list that passes the verifier's test -/

/-- The test, as an equation. -/
theorem fit_eq (f : LFace) (es : List Fmt.Entry) (hes : entriesFit f es = true) :
    (es.map fun e => { e with work := 0 }) = entriesV f := eq_of_beq hes

/-- CONDITIONAL on the verifier's test: the plan's entry at a number is the verifier's but for the
work bits. -/
theorem fit_at (f : LFace) (es : List Fmt.Entry) (hes : entriesFit f es = true) (n : Nat)
    (en : Fmt.Entry) (h : (entriesV f)[n]? = some en) :
    ∃ e, es[n]? = some e ∧ { e with work := 0 } = en := by
  rw [← fit_eq f es hes, List.getElem?_map] at h
  obtain ⟨e, he, e2⟩ := Option.map_eq_some_iff.1 h
  exact ⟨e, he, e2⟩

theorem fit_mem (f : LFace) (es : List Fmt.Entry) (hes : entriesFit f es = true) :
    ∀ e ∈ es, { e with work := 0 } ∈ entriesV f := by
  intro e he
  rw [← fit_eq f es hes]
  exact List.mem_map.2 ⟨e, he, rfl⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.good_shift
#print axioms ProofFile.Honest.K3.Good.good_lkp
#print axioms ProofFile.Honest.K3.Good.good_join
#print axioms ProofFile.Honest.K3.Good.good_line
#print axioms ProofFile.Honest.K3.Good.tame_sum
#print axioms ProofFile.Honest.K3.Good.tame_level
#print axioms ProofFile.Honest.K3.Good.tame_run
#print axioms ProofFile.Honest.K3.Good.entriesV_tame
#print axioms ProofFile.Honest.K3.Good.fit_eq
#print axioms ProofFile.Honest.K3.Good.fit_at
#print axioms ProofFile.Honest.K3.Good.fit_mem
