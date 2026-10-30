-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BordersSucc.lean: THE TABLE OF JOINTS' OPEN SETS, ONE BORDER ON. Small lemmas on
lists; no Mathlib. A file BESIDE the table: it turns nothing of it.

Why. The promise and the relation at border k read entry k of two computed lists
(Johnson/Desc/First/Borders.lean: `openSets`, `pubSets`). Whoever carries a clause across block k
wants entry k + 1 as ONE STEP from entry k, by the row of the block at place k.

What is said. `openSets_length`, `pubSetsBy_length`: one more entry than there are places.
`openSets_succ`: where the list of places has an entry k, the open set at border k + 1 is `stepOpen`
of the open set at border k by that place's row. `pubSetsBy_succ`, `pubSets_succ`: the like for the
open public items, by `pubStep`. `pubSets_empty`, `pubFit_empty`: at the empty filling of the door
(`More`) the open public sets and the test on them are the table's own.

Limits. Beyond the list of places the reading by `getD []` gives the empty set, in silence: these
lemmas speak only where `ps[k]?` is there.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

theorem openSets_length (links : List ModelPart) (ps : List Place) :
    ∀ O, (openSets links ps O).length = ps.length + 1 := by
  induction ps with
  | nil => intro _; rfl
  | cons p l ih =>
    intro O
    simp [openSets, ih]

theorem pubSetsBy_length (rows : Place → PubRow) (ps : List Place) :
    ∀ Q, (pubSetsBy rows ps Q).length = ps.length + 1 := by
  induction ps with
  | nil => intro _; rfl
  | cons p l ih =>
    intro Q
    simp [pubSetsBy, ih]

theorem openSets_zero (links : List ModelPart) (ps : List Place) (O : List Item) :
    (openSets links ps O)[0]?.getD [] = O := by
  cases ps <;> rfl

theorem pubSetsBy_zero (rows : Place → PubRow) (ps : List Place) (Q : List Pub) :
    (pubSetsBy rows ps Q)[0]?.getD [] = Q := by
  cases ps <;> rfl

/-- **The open set one border on**: a step by the row of the block between. -/
theorem openSets_succ (links : List ModelPart) (ps : List Place) :
    ∀ (O : List Item) (k : Nat) (p : Place), ps[k]? = some p →
      (openSets links ps O)[k + 1]?.getD [] =
        stepOpen ((openSets links ps O)[k]?.getD []) (rowOf links p) := by
  induction ps with
  | nil => intro _ k p h; cases h
  | cons q l ih =>
    intro O k p h
    cases k with
    | zero =>
      have e : q = p := by simpa using h
      subst e
      show (openSets links l (stepOpen O (rowOf links q)))[0]?.getD [] = _
      rw [openSets_zero]
      rfl
    | succ j =>
      have h' : l[j]? = some p := by simpa using h
      exact ih (stepOpen O (rowOf links q)) j p h'

/-- The like for the open public items, at any rows. -/
theorem pubSetsBy_succ (rows : Place → PubRow) (ps : List Place) :
    ∀ (Q : List Pub) (k : Nat) (p : Place), ps[k]? = some p →
      (pubSetsBy rows ps Q)[k + 1]?.getD [] =
        pubStep ((pubSetsBy rows ps Q)[k]?.getD []) (rows p) := by
  induction ps with
  | nil => intro _ k p h; cases h
  | cons q l ih =>
    intro Q k p h
    cases k with
    | zero =>
      have e : q = p := by simpa using h
      subst e
      show (pubSetsBy rows l (pubStep Q (rows q)))[0]?.getD [] = _
      rw [pubSetsBy_zero]
      rfl
    | succ j =>
      have h' : l[j]? = some p := by simpa using h
      exact ih (pubStep Q (rows q)) j p h'

/-- At the table's rows with a filling's. -/
theorem pubSets_succ (M : More) (links : List ModelPart) (ps : List Place) (k : Nat) (p : Place)
    (h : ps[k]? = some p) :
    (pubSets M links ps)[k + 1]?.getD [] =
      pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p) :=
  pubSetsBy_succ (pubRowM M links) ps (pubStartM M) k p h

/-- **AT THE EMPTY FILLING THE ROW IS THE TABLE's OWN.** -/
theorem pubRowM_empty (links : List ModelPart) (p : Place) : pubRowM {} links p = pubRowOf links p := by
  simp [pubRowM, PubRow.plus]

theorem pubStartM_empty : pubStartM {} = pubStart := by
  simp [pubStartM]

/-- **AT THE EMPTY FILLING THE OPEN PUBLIC SETS ARE THE TABLE's OWN**: what is shown of the table
without the door is not lost. -/
theorem pubSets_empty (links : List ModelPart) (ps : List Place) :
    pubSets {} links ps = pubSetsBy (pubRowOf links) ps pubStart := by
  unfold pubSets
  rw [pubStartM_empty]
  congr 1
  funext p
  exact pubRowM_empty links p

theorem pubFit_empty (links : List ModelPart) (ps : List Place) :
    pubFit {} links ps = pubFitBy (pubRowOf links) ps pubStart := by
  unfold pubFit
  rw [pubStartM_empty]
  congr 1
  funext p
  exact pubRowM_empty links p

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.openSets_length
#print axioms VerifiableInference.Desc.First.openSets_succ
#print axioms VerifiableInference.Desc.First.pubSets_succ
#print axioms VerifiableInference.Desc.First.pubSets_empty
#print axioms VerifiableInference.Desc.First.pubFit_empty
