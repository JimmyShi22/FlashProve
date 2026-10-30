-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CountsOfHeld.lean: THE KINDS OF A GROUP's OPEN ROWS, PLACE BY PLACE, AND SO THE TWO COUNTS (`TiedOwes`'
FIELDS «plain» AND «gens», TiedLaidIn.lean beside this file), FROM THE TABLE's PROMISE's OWN TEST `rowsHeld`
(Johnson/Desc/First/Borders.lean) AND ONE CLOSED TEST ON THE PLAN. Definitions and theorems.

Why. `rowsTied_of` numbers the rows that the group's test takes in: nP plain rows, the members' samples, nG generator rows.
That a reached state's group holds just nP plain and nG generator rows was shown of nothing, and nP, nG had no terms.
`rowsHeld N O s` says, of a segment m of which a class of rows is open: the group's list has as many rows as the open
classes count, and the row at each place of an open class is of the class's kind. It does not say that the classes'
runs of places cover the list: that is a fact on the plan's numbers.

What is said.
  `covers N m i`: the kind of an item's class, if the item is a class of rows of segment m that lies in the list and
    whose run of places holds the place i.
  `kindsDue N O m`: for each place below `rowsDue N O m`: the kind of the first open class that holds it.
  `coveredB N O m`: A CLOSED TEST ON THE PLAN: every place below `rowsDue N O m` is held by an open class.
  `plainDue`, `gensDue`: how many of `kindsDue` are plain, are generators: THE TERMS FOR nP AND nG.
  `held_at`: what `rowsHeld`'s yes says at a segment whose group is there.
  `kinds_of_held`: **`rowsHeld N O s`, m among the open segments, the group G there, `coveredB N O m` ⊢
    G.rows.toList.map (·.kind) = kindsDue N O m.**
  `plain_of_held`, `gens_of_held`: so (G.rows.filter (·.kind == .plain)).toList.length = plainDue N O m; the like.

Limits. `rowsHeld` is a premise: it stands in the table's promise (`held_of_onQ`, Close/Law/RowAsksOf.lean). `coveredB` is
evaluated nowhere here. Nothing on soundness.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes
open VerifiableInference.Desc.First (Numbers Item RowClass rowsHeld rowSegs rowsDue S)

/-- The kind of an item's class, if it is a class of segment m's that lies in the list and holds i. -/
def covers (N : Numbers) (m i : Nat) : Item → Option RowKind
  | .row m' c =>
    if m' == m && c.inList &&
        decide ((N.rowsAt m c).1 ≤ i ∧ i < (N.rowsAt m c).1 + (N.rowsAt m c).2) then some c.kind
    else none
  | _ => none

/-- The kinds that are due, place by place. -/
def kindsDue (N : Numbers) (O : List Item) (m : Nat) : List RowKind :=
  (List.range (rowsDue N O m)).map fun i => ((O.filterMap (covers N m i)).head?).getD .sample

/-- **A closed test on the plan**: every place of the list is held by an open class. -/
def coveredB (N : Numbers) (O : List Item) (m : Nat) : Bool :=
  (List.range (rowsDue N O m)).all fun i => ((O.filterMap (covers N m i)).head?).isSome

/-- The terms for the two counts. -/
def plainDue (N : Numbers) (O : List Item) (m : Nat) : Nat :=
  ((kindsDue N O m).filter (· == .plain)).length
def gensDue (N : Numbers) (O : List Item) (m : Nat) : Nat :=
  ((kindsDue N O m).filter (· == .generator)).length

variable {N : Numbers} {O : List Item} {s : S} {m : Nat} {G : Group}

/-- What the test's yes says at a segment whose group is there. -/
theorem held_at (h : rowsHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) :
    G.rows.size = rowsDue N O m ∧ ∀ m' c, Item.row m' c ∈ O → (m' == m && c.inList) = true →
      ∀ j < (N.rowsAt m c).2,
        (G.rows[(N.rowsAt m c).1 + j]?).any (fun r => r.kind == c.kind) = true := by
  unfold rowsHeld at h
  have h1 := List.all_eq_true.1 h m hm
  simp only [hG, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨-, h2⟩, h3⟩ := h1
  refine ⟨h2, fun m' c hit hc j hj => ?_⟩
  have h4 := List.all_eq_true.1 h3 _ hit
  simp only [hc, Bool.not_true, Bool.false_or] at h4
  exact List.all_eq_true.1 h4 j (List.mem_range.2 hj)

/-- The row at a place that an open class holds is of that class's kind. -/
theorem kind_at (h : rowsHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) {i : Nat} {k : RowKind}
    (hk : k ∈ O.filterMap (covers N m i)) : (G.rows[i]?).any (fun r => r.kind == k) = true := by
  obtain ⟨it, hit, hcv⟩ := List.mem_filterMap.1 hk
  cases it with
  | row m' c =>
    have hcv' : (if (m' == m && c.inList &&
        decide ((N.rowsAt m c).1 ≤ i ∧ i < (N.rowsAt m c).1 + (N.rowsAt m c).2)) = true
        then some c.kind else none) = some k := hcv
    by_cases hc : (m' == m && c.inList &&
        decide ((N.rowsAt m c).1 ≤ i ∧ i < (N.rowsAt m c).1 + (N.rowsAt m c).2)) = true
    · rw [if_pos hc] at hcv'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨c1, c2⟩, c3, c4⟩ := hc
      obtain rfl := Option.some.inj hcv'
      have e := (held_at h hm hG).2 m' c hit (by rw [c1, c2]; rfl) (i - (N.rowsAt m c).1)
        (by omega)
      rwa [show (N.rowsAt m c).1 + (i - (N.rowsAt m c).1) = i by omega] at e
    · rw [if_neg hc] at hcv'
      cases hcv'
  | _ => cases hcv

/-- **THE KINDS OF THE GROUP's OPEN ROWS, PLACE BY PLACE.** -/
theorem kinds_of_held (h : rowsHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) (hc : coveredB N O m = true) :
    G.rows.toList.map (·.kind) = kindsDue N O m := by
  have hz := (held_at h hm hG).1
  refine List.ext_getElem (by simp [kindsDue, hz]) fun i h1 h2 => ?_
  have hi : i < rowsDue N O m := by simpa [kindsDue] using h2
  have hs := List.all_eq_true.1 hc i (List.mem_range.2 hi)
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hs
  have hmem : k ∈ O.filterMap (covers N m i) := List.mem_of_mem_head? hk
  have e := kind_at h hm hG hmem
  have hiG : i < G.rows.size := hz ▸ hi
  rw [Array.getElem?_eq_getElem hiG] at e
  have e' : G.rows[i].kind = k := by simpa using e
  simp only [kindsDue, List.getElem_map, List.getElem_range, hk, Option.getD_some,
    Array.getElem_toList]
  exact e'

/-- **TiedOwes' FIELD «plain».** -/
theorem plain_of_held (h : rowsHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) (hc : coveredB N O m = true) :
    (G.rows.filter (·.kind == .plain)).toList.length = plainDue N O m := by
  unfold plainDue
  rw [← kinds_of_held h hm hG hc, Array.toList_filter, List.filter_map, List.length_map]
  rfl

/-- **TiedOwes' FIELD «gens».** -/
theorem gens_of_held (h : rowsHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) (hc : coveredB N O m = true) :
    (G.rows.filter (·.kind == .generator)).toList.length = gensDue N O m := by
  unfold gensDue
  rw [← kinds_of_held h hm hG hc, Array.toList_filter, List.filter_map, List.length_map]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.held_at
#print axioms VerifiableInference.Desc.LinkJoin.kind_at
#print axioms VerifiableInference.Desc.LinkJoin.kinds_of_held
#print axioms VerifiableInference.Desc.LinkJoin.plain_of_held
#print axioms VerifiableInference.Desc.LinkJoin.gens_of_held
