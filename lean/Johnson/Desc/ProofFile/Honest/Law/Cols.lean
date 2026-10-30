-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Cols.lean: the columns that the functions of Honest/Frame.lean put
into a view. Theorems on `readsOf` and `fillCols` alone: no description and no prover is named.

  `readsOf_wants`    what `readsOf` lists is, in key, position and declared width, what `groupsOf`
                     (Johnson/Desc/Block.lean) lists, concatenated
  `fillCols_kept`    where `fillCols` returns, there is one column for each read, with the read's
                     key, position and declared width
  `readsOf_words`, `fillCols_words`   every word of such a column is below the prime, if the stored
                     tables' words and the words that are fallen back on are

Limits.
  * Each lemma on `fillCols` starts from a call that has returned: none says that one does.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

theorem readsOf_wants (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (readsOf chain ft stored tree ds Rs).map (fun q => (q.key, q.pos, q.width)) =
      (groupsOf ft ds Rs).flatMap id
  | [], _ => by simp [readsOf, groupsOf]
  | _ :: _, [] => by simp [readsOf, groupsOf]
  | d :: ds, R :: Rs => by
    have ih := readsOf_wants chain ft stored tree ds Rs
    simp only [readsOf, groupsOf, List.map_append, List.flatMap_append, ih]
    congr 1
    congr 1
    · simp only [List.map_flatMap, List.flatMap_map, List.map_map, id]
      exact List.flatMap_congr fun s _ => List.map_congr_left fun x _ => rfl
    · simp only [List.map_flatMap, List.flatMap_map, List.map_map, id]
      exact List.flatMap_congr fun o _ => List.map_congr_left fun x _ => rfl

theorem fillCols_kept : ∀ (q : List Read) (back c : List OpenedColumn), fillCols q back = .ok c →
    (c.map fun x => (x.1, x.2.1, x.2.2.length)) = q.map fun r => (r.key, r.pos, r.width)
  | [], _, c, h => by
    simp only [fillCols] at h
    cases h
    rfl
  | r :: rs, back, c, h => by
    cases hw : r.words with
    | some w =>
      simp only [fillCols, hw] at h
      split at h
      · cases h
      rename_i hlen
      cases hrec : fillCols rs back.tail with
      | error e => simp [hrec, Except.map] at h
      | ok l =>
        simp only [hrec, Except.map] at h
        cases h
        have hl : w.length = r.width := by simpa using hlen
        simp only [List.map_cons, fillCols_kept rs back.tail l hrec, hl]
    | none =>
      cases hh : back.head? with
      | none => simp [fillCols, hw, hh] at h
      | some c0 =>
        simp only [fillCols, hw, hh] at h
        split at h
        · cases h
        rename_i hk
        split at h
        · cases h
        rename_i hlen
        cases hrec : fillCols rs back.tail with
        | error e => simp [hrec, Except.map] at h
        | ok l =>
          simp only [hrec, Except.map] at h
          cases h
          have hl : c0.2.2.length = r.width := by simpa using hlen
          have hk' : c0.1 = r.key ∧ c0.2.1 = r.pos := by simpa using hk
          simp only [List.map_cons, fillCols_kept rs back.tail l hrec, hl, hk'.1, hk'.2]

theorem readsOf_words (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table))
    (hs : ∀ i x u, stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    ∀ r ∈ readsOf chain ft stored tree ds Rs, ∀ u, r.words = some u → ∀ a ∈ u, a < fieldPrimeWord
  | [], _, r, hr => by simp [readsOf] at hr
  | _ :: _, [], r, hr => by simp [readsOf] at hr
  | d :: ds, R :: Rs, r, hr => by
    simp only [readsOf, List.mem_append, List.mem_flatMap, List.mem_map] at hr
    rcases hr with (⟨s, _, x, _, rfl⟩ | ⟨o, _, x, _, rfl⟩) | hr
    · intro u hu
      exact hs _ _ u hu
    · intro u hu a ha
      obtain ⟨pt, _, rfl⟩ := Option.map_eq_some_iff.1 hu
      exact col_lt pt.2 x a ha
    · exact readsOf_words chain ft stored tree hs ds Rs r hr

theorem fillCols_words : ∀ (q : List Read) (back c : List OpenedColumn),
    (∀ r ∈ q, ∀ u, r.words = some u → ∀ a ∈ u, a < fieldPrimeWord) →
    (∀ x ∈ back, ∀ a ∈ x.2.2, a < fieldPrimeWord) → fillCols q back = .ok c →
    ∀ x ∈ c, ∀ a ∈ x.2.2, a < fieldPrimeWord
  | [], _, c, _, _, h => by
    simp only [fillCols] at h
    cases h
    intro x hx
    cases hx
  | r :: rs, back, c, hq, hb, h => by
    have hbt : ∀ x ∈ back.tail, ∀ a ∈ x.2.2, a < fieldPrimeWord := fun x hx =>
      hb x (List.mem_of_mem_tail hx)
    have hqt : ∀ r' ∈ rs, ∀ u, r'.words = some u → ∀ a ∈ u, a < fieldPrimeWord := fun r' hr' =>
      hq r' (List.mem_cons_of_mem _ hr')
    cases hw : r.words with
    | some w =>
      simp only [fillCols, hw] at h
      split at h
      · cases h
      cases hrec : fillCols rs back.tail with
      | error e => simp [hrec, Except.map] at h
      | ok l =>
        simp only [hrec, Except.map] at h
        cases h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hq r List.mem_cons_self w hw
        · exact fillCols_words rs back.tail l hqt hbt hrec x hx
    | none =>
      cases hh : back.head? with
      | none => simp [fillCols, hw, hh] at h
      | some c0 =>
        have hc0 : c0 ∈ back := by
          cases back with
          | nil => simp at hh
          | cons b bs =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            exact List.mem_cons_self
        simp only [fillCols, hw, hh] at h
        split at h
        · cases h
        split at h
        · cases h
        cases hrec : fillCols rs back.tail with
        | error e => simp [hrec, Except.map] at h
        | ok l =>
          simp only [hrec, Except.map] at h
          cases h
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hb _ hc0
          · exact fillCols_words rs back.tail l hqt hbt hrec x hx

end ProofFile.Honest

#print axioms ProofFile.Honest.readsOf_wants
#print axioms ProofFile.Honest.fillCols_kept
#print axioms ProofFile.Honest.readsOf_words
#print axioms ProofFile.Honest.fillCols_words
