-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPlanDoor.lean: THE SMALLNESS TEST: WHAT THE TESTS OF
Johnson/Desc/First/K8/PlanDoor.lean GIVE.

  `hear_before`: the field `before` of `approximateRangeProofDrawKind seat p`, written out: by definition.
  `mem_drawIxs`: an index is among `drawIxs F` just if the flat list has an entry of the kind K8
    there.
  `mem_sentBy`: what the list `sentBy F i` holds.
  `names_of_door`: **a yes of `namesDoorB F`**, at an entry b of the kind K8 with the number i whose
    field `before` is that of `approximateRangeProofDrawKind seat p`: 4 ≤ i; there are the entries bM, four in front, and bR,
    right in front; each sends a tree; and every number from `treesFrom F (i - 4)` up to that plus
    the trees of bM's rounds, or from `treesFrom F (i - 1)` up to that plus the trees of bR's, is
    among `p.matsIn ++ p.readsIn`. The premise on `before` is, by definition, the field `before` of
    `LikeP seat p b` (Johnson/Desc/First/K8/LawSeatedPlan.lean).
  `walk_eq_lookups`, `drawRounds_eq`, `drawsDoorB_eq`: **THE ONE WALK SAYS WHAT `drawsB` SAYS**:
    `drawsDoorB F = drawsB F (drawIxs F)`, at every description.
  `draws_of_door`: **a yes of `drawsDoorB F`**: every declared round of the first chain that draws
    entries of a matrix is the round right behind the rounds of the entries in front of an entry of
    the kind K8.
Statements and proofs.
WHAT `names_of_door` DOES NOT HAND OVER. `planGives_of_ranges` (Johnson/Desc/First/K8/LawWalk.lean)
takes, beside the sentence in which `names_of_door` ends, four equations on counts of trees; two of
them together say that the two entries between the sendings send no tree. No test here asks that,
and none need: where the row is stated at the proof file's description these four are proved, in the
goals' scope, from the blocks that sit there, not taken as premises. Outside that scope a yes of
`namesDoorB` alone does not give `PlanGives`.
Limits. Those of PlanDoor.lean. The tests are shown true at no description here. WHICH of the two
lists of the place a sent tree is in is not said: the field `before` holds them in a row.

-/
import Johnson.Desc.First.K8.PlanDoor
import Johnson.Desc.First.K8.LawPlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- The field `before` of the kind's block, written out. -/
theorem hear_before {S Cl : Type} (seat : Seat S) (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).before = (p.matsIn ++ p.readsIn).map fun n => (1, n) := rfl

theorem mem_drawIxs {Xi : Type} (F : FileDescription Xi) (i : Nat) :
    i ∈ drawIxs F ↔ ∃ b, F.first.blocksInOrder[i]? = some b ∧ b.place.kind = KindName.K8 := by
  unfold drawIxs
  simp only [List.mem_map, List.mem_filter, beq_iff_eq, Prod.exists]
  constructor
  · rintro ⟨b, j, ⟨hm, hk⟩, rfl⟩
    exact ⟨b, (List.mem_zipIdx_iff_getElem?.1 hm), hk⟩
  · rintro ⟨b, hb, hk⟩
    exact ⟨b, i, ⟨List.mem_zipIdx_iff_getElem?.2 hb, hk⟩, rfl⟩

theorem mem_sentBy {Xi : Type} {F : FileDescription Xi} {i : Nat} {b : Block F.S₁ F.Cl}
    (hb : F.first.blocksInOrder[i]? = some b) (j : Nat) :
    j ∈ sentBy F i ↔ treesFrom F i ≤ j ∧ j < treesFrom F i + rootsOfRounds b.rounds := by
  unfold sentBy
  rw [hb]
  exact List.mem_range'_1

theorem sentBy_some {Xi : Type} {F : FileDescription Xi} {i : Nat} (h : (sentBy F i).isEmpty = false) :
    ∃ b, F.first.blocksInOrder[i]? = some b ∧ rootsOfRounds b.rounds ≠ 0 := by
  unfold sentBy at h
  cases hb : F.first.blocksInOrder[i]? with
  | none => simp [hb] at h
  | some b =>
    refine ⟨b, rfl, fun h0 => ?_⟩
    simp [hb, h0] at h

/-- **What a yes of the test on the names gives.** -/
theorem names_of_door {Xi : Type} {F : FileDescription Xi} (h : namesDoorB F = true) {i : Nat}
    {b : Block F.S₁ F.Cl} (hb : F.first.blocksInOrder[i]? = some b) (hk : b.place.kind = KindName.K8)
    {p : Par} (hp : b.before = (p.matsIn ++ p.readsIn).map fun n => (1, n)) :
    4 ≤ i ∧ ∃ bM bR, F.first.blocksInOrder[i - 4]? = some bM ∧ F.first.blocksInOrder[i - 1]? = some bR ∧
      rootsOfRounds bM.rounds ≠ 0 ∧ rootsOfRounds bR.rounds ≠ 0 ∧
      ∀ j, (treesFrom F (i - 4) ≤ j ∧ j < treesFrom F (i - 4) + rootsOfRounds bM.rounds) ∨
          (treesFrom F (i - 1) ≤ j ∧ j < treesFrom F (i - 1) + rootsOfRounds bR.rounds) →
        j ∈ p.matsIn ++ p.readsIn := by
  have hi : namesDoorAt F i = true :=
    List.all_eq_true.1 h i ((mem_drawIxs F i).2 ⟨b, hb, hk⟩)
  unfold namesDoorAt at hi
  rw [hb] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_append] at hi
  obtain ⟨⟨⟨h4, hM⟩, hR⟩, hall⟩ := hi
  obtain ⟨bM, eM, nM⟩ := sentBy_some hM
  obtain ⟨bR, eR, nR⟩ := sentBy_some hR
  have back : ∀ j, b.before.contains (1, j) = true → j ∈ p.matsIn ++ p.readsIn := by
    intro j hj
    rw [hp] at hj
    have hm := List.contains_iff_mem.1 hj
    obtain ⟨n, hn, e⟩ := List.mem_map.1 hm
    have : n = j := congrArg Prod.snd e
    exact this ▸ hn
  refine ⟨h4, bM, bR, eM, eR, nM, nR, fun j hj => ?_⟩
  rcases hj with hj | hj
  · exact back j (hall j (Or.inl ((mem_sentBy eM j).2 hj)))
  · exact back j (hall j (Or.inr ((mem_sentBy eR j).2 hj)))

/-- One walk with the numbers beside the entries finds what a look-up by number finds. -/
theorem walk_eq_lookups {α : Type} (p : α → Bool) : ∀ (ds : List α) (k : Nat),
    ((ds.zipIdx k).filter fun x => p x.1).map (·.2) =
      (List.range' k ds.length).filter fun j => ((ds[j - k]?).map p).getD false
  | [], k => by simp
  | d :: ds, k => by
    have ih := walk_eq_lookups p ds (k + 1)
    have ht : ((List.range' (k + 1) ds.length).filter fun j =>
        (((d :: ds)[j - k]?).map p).getD false) =
        (List.range' (k + 1) ds.length).filter fun j => ((ds[j - (k + 1)]?).map p).getD false := by
      refine List.filter_congr fun j hj => ?_
      have hk : k + 1 ≤ j := (List.mem_range'_1.1 hj).1
      have e : j - k = (j - (k + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
    rw [List.zipIdx_cons, List.length_cons, List.range'_succ, List.filter_cons, List.filter_cons,
      ht, ← ih]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    cases p d <;> simp

/-- `drawRounds` is the list that `drawsB` makes by looking each round up by its number. -/
theorem drawRounds_eq (ds : List Fmt.DeclaredRound) :
    drawRounds ds = (List.range ds.length).filter fun j =>
      ((ds[j]?).map fun d => d.entry.trits != 0).getD false := by
  have h := walk_eq_lookups (fun d : Fmt.DeclaredRound => d.entry.trits != 0) ds 0
  simp only [Nat.sub_zero] at h
  rw [List.range_eq_range']
  exact h

/-- **The one walk says what `drawsB` says**, at the entries of the kind K8. -/
theorem drawsDoorB_eq {Xi : Type} (F : FileDescription Xi) : drawsDoorB F = drawsB F (drawIxs F) := by
  unfold drawsDoorB drawsB
  rw [drawRounds_eq]

/-- **What a yes of the test on the draws gives.** -/
theorem draws_of_door {Xi : Type} {F : FileDescription Xi} (h : drawsDoorB F = true) {j : Nat}
    {d : Fmt.DeclaredRound} (hj : F.roundsDeclaredByBlocks.1[j]? = some d) (ht : d.entry.trits ≠ 0) :
    ∃ i b, F.first.blocksInOrder[i]? = some b ∧ b.place.kind = KindName.K8 ∧
      j = roundsIn (F.first.blocksInOrder.take i) := by
  have hm : j ∈ drawRounds F.roundsDeclaredByBlocks.1 := by
    unfold drawRounds
    refine List.mem_map.2 ⟨(d, j), List.mem_filter.2 ⟨List.mem_zipIdx_iff_getElem?.2 hj, ?_⟩, rfl⟩
    simp [ht]
  unfold drawsDoorB at h
  rw [beq_iff_eq.1 h] at hm
  obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
  obtain ⟨b, hb, hk⟩ := (mem_drawIxs F i).1 hi
  exact ⟨i, b, hb, hk, e.symm⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.names_of_door
#print axioms VerifiableInference.Desc.First.K8.draws_of_door
#print axioms VerifiableInference.Desc.First.K8.drawsDoorB_eq
