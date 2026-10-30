-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/BordersKept.lean: THE TABLE OF JOINTS' OPEN PUBLIC SETS: WHAT IS OPEN AND IS
DROPPED BY NOBODY STAYS OPEN TO THE LAST BORDER. Small lemmas on lists; no Mathlib. A file BESIDE
the table (Johnson/Desc/First/Borders.lean): it turns nothing of it.

Why. Whoever spends a public item at the first chain's last border (`ocEnd_pub`,
Johnson/Desc/Sound/TieEnd.lean) owes that the item is in the last open set. For an item that comes
through the door (`Pub.more`, `More`) as an invariant, or is made at one place and never dropped,
that is a law on the table's fold, general in the lists.

Main names (namespace `VerifiableInference.Desc.First`).
  `mem_pubStep_of_kept`, `mem_pubStep_of_made`: one step. `pubSetsBy_last_of_kept`,
    `pubSetsBy_last_of_made`: at any rows: open at the first border (or made by a row of the list),
    dropped by no (later) row: in the last open set.
  `more_not_dropped`: the table's own rows drop no item of the door. `more_dropped_iff`: a row with
    a filling's drops such an item just where the filling's row names it.
  **`pubSets_last_of_start`**: x ∈ `M.start`, and no row of M at a place of the list drops x:
    `moreItem x` is open at the last border. **`pubSets_last_of_made`**: the like for an x that M's
    row at a place makes.

Limits. (1) M is the WHOLE merged filling: the premise "nobody drops x" speaks of every layer's
rows. (2) `more_not_dropped` walks the text of `pubRowOf`: it falls if a row of the table comes to
drop a `more`. (3) Nothing says that an item HOLDS: only that it is asked. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- A step keeps what the row does not drop. -/
theorem mem_pubStep_of_kept {Q : List Pub} {r : PubRow} {q : Pub} (h : q ∈ Q)
    (hd : q ∉ r.drops) : q ∈ pubStep Q r := by
  unfold pubStep
  refine List.mem_append_left _ (List.mem_filter.2 ⟨h, ?_⟩)
  simpa using hd

/-- A step opens what the row makes. -/
theorem mem_pubStep_of_made {Q : List Pub} {r : PubRow} {q : Pub} (h : q ∈ r.makes) :
    q ∈ pubStep Q r := by
  unfold pubStep
  by_cases c : q ∈ Q.filter fun x => !r.drops.contains x
  · exact List.mem_append_left _ c
  · refine List.mem_append_right _ (List.mem_filter.2 ⟨h, ?_⟩)
    cases hc : (Q.filter fun x => !r.drops.contains x).contains q with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.1 hc) c

/-- **AT ANY ROWS: what is open at the first border and is dropped by no row of the list stands in
the last open set.** -/
theorem pubSetsBy_last_of_kept (rows : Place → PubRow) (q : Pub) :
    ∀ (ps : List Place) (Q : List Pub), q ∈ Q → (∀ p ∈ ps, q ∉ (rows p).drops) →
      q ∈ (pubSetsBy rows ps Q)[ps.length]?.getD []
  | [], Q, h, _ => h
  | p :: l, Q, h, hd => by
    show q ∈ (pubSetsBy rows l (pubStep Q (rows p)))[l.length]?.getD []
    exact pubSetsBy_last_of_kept rows q l _
      (mem_pubStep_of_kept h (hd p (List.mem_cons_self ..)))
      fun p' hp' => hd p' (List.mem_cons_of_mem _ hp')

/-- **AT ANY ROWS: what a row of the list makes, and no later row drops, stands in the last open
set.** -/
theorem pubSetsBy_last_of_made (rows : Place → PubRow) (q : Pub) (a : List Place) (p : Place)
    (l : List Place) (Q : List Pub) (hm : q ∈ (rows p).makes)
    (hd : ∀ p' ∈ l, q ∉ (rows p').drops) :
    q ∈ (pubSetsBy rows (a ++ p :: l) Q)[(a ++ p :: l).length]?.getD [] := by
  induction a generalizing Q with
  | nil =>
    show q ∈ (pubSetsBy rows l (pubStep Q (rows p)))[l.length]?.getD []
    exact pubSetsBy_last_of_kept rows q l _ (mem_pubStep_of_made hm) hd
  | cons x a ih => exact ih (pubStep Q (rows x))

/-- The table's own rows drop no item of the door. -/
theorem more_not_dropped (links : List ModelPart) (p : Place) (x : MoreName) :
    moreItem x ∉ (pubRowOf links p).drops := by
  intro h
  unfold pubRowOf at h
  split at h
  · split at h
    · exact absurd h List.not_mem_nil
    · dsimp only at h
      repeat' split at h
      all_goals first
        | exact absurd h List.not_mem_nil
        | (simp only [moreItem, List.mem_cons, List.mem_append, List.not_mem_nil, reduceCtorEq,
            or_self] at h)
  · split at h <;> exact absurd h List.not_mem_nil

/-- A row with a filling's drops an item of the door just where the filling's row names it. -/
theorem more_dropped_iff (M : More) (links : List ModelPart) (p : Place) (x : MoreName) :
    moreItem x ∈ (pubRowM M links p).drops ↔ x ∈ (M.rows links p).drops := by
  unfold pubRowM PubRow.plus
  show moreItem x ∈ (pubRowOf links p).drops ++ (M.rows links p).drops.map moreItem ↔ _
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨y, hy, e⟩)
    · exact absurd h (more_not_dropped links p x)
    · have : y = x := by
        unfold moreItem at e
        injection e with e1 e2
        exact Prod.ext e1 e2
      rw [← this]
      exact hy
  · exact fun h => Or.inr ⟨x, h, rfl⟩

/-- **AN ITEM OF THE DOOR THAT IS OPEN AT THE START AND THAT NO ROW OF THE FILLING DROPS IS OPEN AT
THE LAST BORDER.** -/
theorem pubSets_last_of_start (M : More) (links : List ModelPart) (ps : List Place) (x : MoreName)
    (hs : x ∈ M.start) (hd : ∀ p ∈ ps, x ∉ (M.rows links p).drops) :
    moreItem x ∈ (pubSets M links ps)[ps.length]?.getD [] := by
  unfold pubSets
  refine pubSetsBy_last_of_kept _ _ ps _ ?_ fun p hp h =>
    hd p hp ((more_dropped_iff M links p x).1 h)
  unfold pubStartM
  exact List.mem_append_right _ (List.mem_map.2 ⟨x, hs, rfl⟩)

/-- **AN ITEM OF THE DOOR THAT THE FILLING's ROW AT A PLACE MAKES AND NO LATER ROW DROPS IS OPEN AT
THE LAST BORDER.** -/
theorem pubSets_last_of_made (M : More) (links : List ModelPart) (a : List Place) (p : Place)
    (l : List Place) (x : MoreName) (hm : x ∈ (M.rows links p).makes)
    (hd : ∀ p' ∈ l, x ∉ (M.rows links p').drops) :
    moreItem x ∈ (pubSets M links (a ++ p :: l))[(a ++ p :: l).length]?.getD [] := by
  unfold pubSets
  refine pubSetsBy_last_of_made _ _ a p l _ ?_ fun p' hp' h =>
    hd p' hp' ((more_dropped_iff M links p' x).1 h)
  unfold pubRowM PubRow.plus
  exact List.mem_append_right _ (List.mem_map.2 ⟨x, hm, rfl⟩)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.mem_pubStep_of_kept
#print axioms VerifiableInference.Desc.First.mem_pubStep_of_made
#print axioms VerifiableInference.Desc.First.pubSetsBy_last_of_kept
#print axioms VerifiableInference.Desc.First.pubSetsBy_last_of_made
#print axioms VerifiableInference.Desc.First.more_not_dropped
#print axioms VerifiableInference.Desc.First.more_dropped_iff
#print axioms VerifiableInference.Desc.First.pubSets_last_of_start
#print axioms VerifiableInference.Desc.First.pubSets_last_of_made
