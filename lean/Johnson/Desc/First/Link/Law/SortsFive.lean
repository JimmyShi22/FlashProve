-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortsFive.lean: THE TEST `sortsB` (CoefsFit.lean) READS FIVE FIELDS OF
THE
APPROXIMATE RANGE PROOF's STRUCTURE: so `SortsAt sh s` (TotalMoves.lean) follows from a Bool on the
plan wherever the state's structure has the planned value's five. Definitions and theorems. It
changes no other file.

  `five tl`: the arrays' index · the number of matrices · the symbol arrays' numbers · the pieces of
    the two lookups on the digits.
  `sorts_five`: five tl' = five tl ⊢ sortsB sh tl' = sortsB sh tl.
  `sortsAt_of_five`: **readTl five s = some (five tlP) · sortsB sh tlP = true ⊢ SortsAt sh s.**
  `keeps4_five`: it reads none of the four fields that the lookup on the digits lays (`Keeps4`,
    Johnson/Desc/First/K8/LawWideK3.lean): so that kind's laws on such readings hold of it.
  `hear_leaves_five`: the block of the approximate range proof's draw leaves it.
  `three_of_seven`: three of the five stand among the seven fields of `Ready.seven`
    (Johnson/Desc/First/K8/Cond.lean); the pieces do not.
Limits. That a state's structure has a planned value's five is shown of no state here. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.TotalMoves
import Johnson.Desc.First.K8.LawWideK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (readTl Keeps4)

/-- What `sortsB` reads of the structure. -/
def five (tl : HTailF2) := (tl.ix, tl.NM, tl.gtTree, tl.z1.pieces, tl.z2.pieces)

theorem sorts_five {tl tl' : HTailF2} (h : five tl' = five tl) (sh : List Look) :
    sortsB sh tl' = sortsB sh tl := by
  simp only [five, Prod.mk.injEq] at h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  unfold sortsB tableAtB
  rw [a1, a2, a3, a4, a5]

/-- **From a Bool on the plan.** -/
theorem sortsAt_of_five {sh : List Look} {s : S} {tlP : HTailF2}
    (h : readTl five s = some (five tlP)) (hB : sortsB sh tlP = true) : SortsAt sh s := by
  intro tl ht
  unfold readTl at h
  rw [ht] at h
  rw [sorts_five (Option.some.inj h)]
  exact hB

theorem keeps4_five : Keeps4 five := fun _ _ _ _ _ => rfl

/-- The block of the draw leaves the five. -/
theorem hear_leaves_five {Cl : Type} (p : First.K8.Par) :
    (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).Leaves (readTl five) := by
  intro s rs gs s' hd
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s s' rs gs hd
  obtain ⟨tl, ht, hm⟩ := (First.K8.decide_atS_iff p s s' r gs).1 hd
  rw [hm.2.2.2.2.2.2.2.2]
  unfold readTl
  rw [First.K8.putTl_tl s tl _ ht, ht]
  rfl

/-- Three of the five stand among the seven. -/
theorem three_of_seven {tl tlP : HTailF2} (h : First.K8.Ready.seven tl = First.K8.Ready.seven tlP) :
    tl.ix = tlP.ix ∧ tl.NM = tlP.NM ∧ tl.gtTree = tlP.gtTree := by
  simp only [First.K8.Ready.seven, Prod.mk.injEq] at h
  exact ⟨h.2.1, h.2.2.2.2.1, h.1⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sorts_five
#print axioms VerifiableInference.Desc.LinkJoin.sortsAt_of_five
#print axioms VerifiableInference.Desc.LinkJoin.keeps4_five
#print axioms VerifiableInference.Desc.LinkJoin.hear_leaves_five
#print axioms VerifiableInference.Desc.LinkJoin.three_of_seven
