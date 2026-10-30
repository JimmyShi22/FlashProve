-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ShapeAtWritten.lean (it imports
Johnson/Desc/AtSeats/TreesOpened.lean): the data's side of
the field told of PlanAt (Johnson/Desc/K1/Law/NewAtSending.lean): AT THE THREE WRITTEN LISTS OF
ROUNDS THE SHAPE THAT THE DATA GIVE TO TREE j OF THE FIRST CHAIN (Three.shapeAt at the data's own
list of openings) HAS THE DEPTH AND THE WIDTH OF THAT TREE's LAYOUT. No evaluation here: membership
alone, from the two closed facts of TreesOpened.lean (every opening of such a tree bears the
layout's two numbers; each of the 83 is opened). A law file; no running text imports it.
  allOpens t₁ t₂: the data's list of openings at the written lists (the term "all" in
      Three.Whole.of), at any two numbers of trees
  mem_opensOf, opensOf_mem: what stands in Three.opensOf, both ways
  whole_zero, whole_ge: a tree of the first chain keeps its number through the file; a later chain's
      tree has a number from t₁ on
  as_laid_of: the walk's accept, as a sentence
  named_as_laid: every entry of allOpens that bears a number j < 83 bears laidFull[j], where 83 ≤ t₁
  opened_in_all: each j < 83 stands in allOpens
  shapeAt_of: what shapeAt returns is an entry's shape, where an entry bears the number
  shapeAt_written: laidFull[j]? = some ((shapeAt (allOpens t₁ t₂) j dflt).a, (…).W), at every dflt
  trees_of_round: so for the trees of a round's data of the first chain (Three.rdOf … 0 0 0 r
      sent): the i-th has laidFull[sent + i], where sent + i < 83

PREMISE. ht : 83 ≤ t₁: the first list counts 83 roots at least, so that no later chain's tree bears
a number below 83 (rootsIn dryProofFull.1 = 83 was compiled elsewhere, not shown here). What is
not claimed. That the rounds of a file in scope are the written lists. That the declared depth and
width are the layout's. That base + n is the tree's number. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.TreesOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Three Johnson.G
open OnBytes.Params (Rounds)

/-- The data's list of openings, at the written lists. -/
def allOpens (t₁ t₂ : Nat) : List (Nat × Fmt.Shape × Nat × Nat) :=
  opensOf t₁ t₂ 0 dryProofFull.1 ++
    (opensOf t₁ t₂ 1 dryProofFull.2.1 ++ opensOf t₁ t₂ 2 dryProofFull.2.2)

theorem mem_opensOf {t₁ t₂ here : Nat} {R : Rounds} {x : Nat × Fmt.Shape × Nat × Nat}
    (h : x ∈ opensOf t₁ t₂ here R) :
    ∃ r ∈ R, ∃ o ∈ r.1.opens, ∃ y, named here o.2 = some y ∧ x.1 = wholeNo t₁ t₂ y ∧
      x.2.1 = o.1 := by
  unfold opensOf at h
  obtain ⟨ri, hri, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨o, ho, e⟩ := List.mem_filterMap.1 hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 e
  have hr : ri.1 ∈ R := by
    have := List.mem_map_of_mem (f := Prod.fst) hri
    rwa [List.zipIdx_map_fst] at this
  exact ⟨ri.1, hr, o, ho, y, hy, rfl, rfl⟩

theorem opensOf_mem {t₁ t₂ here : Nat} {R : Rounds} {r : Fmt.Round × List Fmt.Stored} (hr : r ∈ R)
    {o : Fmt.Shape × Fmt.Src} (ho : o ∈ r.1.opens) {y : Nat × Nat} (hy : named here o.2 = some y) :
    ∃ x ∈ opensOf t₁ t₂ here R, x.1 = wholeNo t₁ t₂ y := by
  have hr' : r ∈ R.zipIdx.map Prod.fst := by rw [List.zipIdx_map_fst]; exact hr
  obtain ⟨ri, hri, rfl⟩ := List.mem_map.1 hr'
  refine ⟨(wholeNo t₁ t₂ y, o.1, here, ri.2), ?_, rfl⟩
  unfold opensOf
  exact List.mem_flatMap.2 ⟨ri, hri, List.mem_filterMap.2 ⟨o, ho, by rw [hy]; rfl⟩⟩

theorem whole_zero (t₁ t₂ n : Nat) : wholeNo t₁ t₂ (0, n) = n := by
  show 0 + n = n
  exact Nat.zero_add n

theorem whole_ge (t₁ t₂ : Nat) (y : Nat × Nat) (h : y.1 ≠ 0) : t₁ ≤ wholeNo t₁ t₂ y := by
  obtain ⟨c, n⟩ := y
  match c, h with
  | 1, _ => exact Nat.le_add_right _ _
  | c + 2, _ =>
    show t₁ ≤ t₁ + t₂ + n
    omega

theorem as_laid_of {tab : List (Nat × Nat)} {here : Nat} {R : Rounds}
    (h : asLaidB tab here R = true) {r : Fmt.Round × List Fmt.Stored} (hr : r ∈ R)
    {o : Fmt.Shape × Fmt.Src} (ho : o ∈ r.1.opens) {n : Nat} (hn : named here o.2 = some (0, n)) :
    tab[n]? = some (o.1.a, o.1.W) := by
  unfold asLaidB at h
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h r hr) o ho
  rw [hn] at h1
  exact eq_of_beq h1

theorem entry_as_laid {t₁ t₂ here : Nat} {R : Rounds} (h : asLaidB laidFull here R = true)
    (ht : 83 ≤ t₁) {x : Nat × Fmt.Shape × Nat × Nat} (hx : x ∈ opensOf t₁ t₂ here R)
    (hj : x.1 < 83) : laidFull[x.1]? = some (x.2.1.a, x.2.1.W) := by
  obtain ⟨r, hr, o, ho, y, hy, e1, e2⟩ := mem_opensOf hx
  by_cases h0 : y.1 = 0
  · obtain ⟨c, n⟩ := y
    obtain rfl : c = 0 := h0
    rw [e1, whole_zero, e2]
    exact as_laid_of h hr ho hy
  · have := whole_ge t₁ t₂ y h0
    omega

/-- Every entry that bears a number below 83 bears the layout's two numbers. -/
theorem named_as_laid (t₁ t₂ : Nat) (ht : 83 ≤ t₁) {x : Nat × Fmt.Shape × Nat × Nat}
    (hx : x ∈ allOpens t₁ t₂) (hj : x.1 < 83) : laidFull[x.1]? = some (x.2.1.a, x.2.1.W) := by
  have h := all_as_laid
  unfold allAsLaidB at h
  simp only [Bool.and_eq_true] at h
  unfold allOpens at hx
  rcases List.mem_append.1 hx with h1 | h23
  · exact entry_as_laid h.1.1 ht h1 hj
  · rcases List.mem_append.1 h23 with h2 | h3
    · exact entry_as_laid h.1.2 ht h2 hj
    · exact entry_as_laid h.2 ht h3 hj

theorem of_opensB {here n : Nat} {r : Fmt.Round × List Fmt.Stored} (h : opensB here n r = true) :
    ∃ o ∈ r.1.opens, named here o.2 = some (0, n) := by
  unfold opensB at h
  obtain ⟨o, ho, e⟩ := List.any_eq_true.1 h
  exact ⟨o, ho, eq_of_beq e⟩

/-- Each of the 83 stands in the data's list. -/
theorem opened_in_all (t₁ t₂ j : Nat) (hj : j < 83) : ∃ x ∈ allOpens t₁ t₂, x.1 = j := by
  have h := List.all_eq_true.1 trees_opened j (List.mem_range.2 hj)
  unfold openedB at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h3
  · obtain ⟨e, _, he⟩ := List.any_eq_true.1 h1
    have h2 := (Bool.and_eq_true_iff.1 he).2
    cases hh : (dryProofFull.1.drop e.1).head? with
    | none => rw [hh] at h2; cases h2
    | some r =>
      rw [hh, Option.any_some] at h2
      have hr : r ∈ dryProofFull.1 := List.mem_of_mem_drop (List.mem_of_head? hh)
      obtain ⟨o, ho, hn⟩ := of_opensB h2
      obtain ⟨x, hx, ex⟩ := opensOf_mem (t₁ := t₁) (t₂ := t₂) hr ho hn
      exact ⟨x, List.mem_append_left _ hx, by rw [ex, whole_zero]⟩
  · obtain ⟨r, hr, h2⟩ := List.any_eq_true.1 h3
    obtain ⟨o, ho, hn⟩ := of_opensB h2
    obtain ⟨x, hx, ex⟩ := opensOf_mem (t₁ := t₁) (t₂ := t₂) hr ho hn
    exact ⟨x, List.mem_append_right _ (List.mem_append_right _ hx), by rw [ex, whole_zero]⟩

/-- The shape that shapeAt returns is an entry's, where an entry bears the number. -/
theorem shapeAt_of {all : List (Nat × Fmt.Shape × Nat × Nat)} {j : Nat} {P : Fmt.Shape → Prop}
    (hex : ∃ x ∈ all, x.1 = j) (hall : ∀ x ∈ all, x.1 = j → P x.2.1) (dflt : Fmt.Shape) :
    P (shapeAt all j dflt) := by
  unfold shapeAt
  cases hf : all.find? (·.1 == j) with
  | none =>
    obtain ⟨x, hx, ex⟩ := hex
    have h1 := List.find?_eq_none.1 hf x hx
    exact absurd (beq_iff_eq.2 ex) h1
  | some x =>
    have hb : (x.1 == j) = true :=
      List.find?_some (p := fun y : Nat × Fmt.Shape × Nat × Nat => y.1 == j) hf
    exact hall x (List.mem_of_find?_eq_some hf) (eq_of_beq hb)

/-- **The data's shape of tree j has its layout's depth and width.** -/
theorem shapeAt_written (t₁ t₂ : Nat) (ht : 83 ≤ t₁) (j : Nat) (hj : j < 83) (dflt : Fmt.Shape) :
    laidFull[j]? =
      some ((shapeAt (allOpens t₁ t₂) j dflt).a, (shapeAt (allOpens t₁ t₂) j dflt).W) :=
  shapeAt_of (P := fun sh => laidFull[j]? = some (sh.a, sh.W)) (opened_in_all t₁ t₂ j hj)
    (fun x hx ex => by
      have h := named_as_laid t₁ t₂ ht hx (by rw [ex]; exact hj)
      rw [ex] at h
      exact h) dflt

/-- **So for the trees of a round's data of the first chain.** -/
theorem trees_of_round (t₁ t₂ : Nat) (ht : 83 ≤ t₁) (r : Fmt.Round × List Fmt.Stored)
    (sent i : Nat) (sh : Fmt.Shape)
    (h : (rdOf (allOpens t₁ t₂) t₁ t₂ 0 0 0 r sent).trees[i]? = some sh) (hi : sent + i < 83) :
    laidFull[sent + i]? = some (sh.a, sh.W) := by
  have h1 : ((List.range (r.1.items.countP (· == .root))).map fun i =>
      shapeAt (allOpens t₁ t₂) (0 + sent + i) (bareShape 0 (sent + i)))[i]? = some sh := h
  rw [List.getElem?_map] at h1
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h1
  obtain rfl : k = i := by
    have := List.getElem?_eq_some_iff.1 hk
    obtain ⟨hl, e⟩ := this
    rw [List.getElem_range] at e
    exact e.symm
  rw [Nat.zero_add]
  exact shapeAt_written t₁ t₂ ht (sent + k) hi _

end HashBuild

#print axioms HashBuild.mem_opensOf
#print axioms HashBuild.opensOf_mem
#print axioms HashBuild.named_as_laid
#print axioms HashBuild.opened_in_all
#print axioms HashBuild.shapeAt_written
#print axioms HashBuild.trees_of_round
