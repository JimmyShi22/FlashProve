-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/K8Ties.lean: THE SMALLNESS TEST's THREE TIES OF THE LINK's LAW, WHOLE, AT
THE SEAT, AT EVERY SORT OF LINK: at a link of the description's first chain whose hearing block
number i is of the kind K8: the run at the entry (i, «K8.equations») stands under `k8Run.2`; behind
the batching the runs at (i, «K8.lsTail») and (i, «K8.tests») stand under `k8LsTail` and `k8Tests
nU`: the fields tEq, tLs, tTests of `LayersTake`, `AttTake`, `HeadTake`
(Johnson/Desc/First/Link/Law/PayLayers.lean, PayAttention.lean, PayHead.lean) to the letter, WITH nU
NAMED: the lengths `ProofFile.k8NU G₀ X` at the record X that stands at the number l of the built links.
Theorems, after the pattern of Johnson/LPFK9R/MergeTie.lean.

What is said. `k8_member`: every block of the smallness test's lot is the kind's whole block at the
numbers of a built link X and its number l'. `k8_ties`: **the three ties.** Through `ties_at_seat`,
`lot_of_kind`, `k8_member` and the batching kind's law on the whole block's lists
(Johnson/Desc/First/Batch/Law/K8Under.lean).

Limits. Nine of 21 ties (three a sort of link). Under the seat's three yeses. Nothing on soundness.

-/
import Johnson.LPFK9R.TiesAtSeat
import Johnson.Desc.First.Batch.Law.K8Under

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At AtAfter Under UnderAfter)
open VerifiableInference.Desc.K9L (k8Run k8LsTail k8Tests k8_equations_under k8_lsTail_under
  k8_tests_under)
open ProofFile (Cl)

/-- Every block of the smallness test's lot is the kind's whole block at the numbers of a built link
and its number. -/
theorem k8_member {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S Cl}
    (hb : b ∈ (ProofFile.P1K8.lot Z).blocks G) :
    ∃ X l', G.built.toList[l']? = some X ∧
      b = VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z G X l') := by
  rcases IM.blocks_mem hb with ⟨x, hx, _⟩ | h
  · exact absurd hx (List.not_mem_nil)
  · obtain ⟨⟨X, l'⟩, hx, rfl⟩ := List.mem_map.1 h
    exact ⟨X, l', List.mem_zipIdx_iff_getElem?.1 hx, rfl⟩

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **THE SMALLNESS TEST's THREE TIES, WHOLE, AT THE SEAT.** -/
theorem k8_ties {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K8) (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ X, B.G₀.built.toList[l]? = some X ∧
      (∀ run, At Lk (i, "K8.equations") run → Under run k8Run.2) ∧
      (∀ run, AtAfter Lk (i, "K8.lsTail") run → UnderAfter run k8LsTail) ∧
      ∀ run, AtAfter Lk (i, "K8.tests") run → UnderAfter run (k8Tests (ProofFile.k8NU B.G₀ X)) := by
  obtain ⟨Lk, e1, L, hL, b', hb', ep, t1, t2⟩ :=
    ties_at_seat hB hb hc l sub hl i .K8 hk (by decide) (by decide) hi
  obtain rfl : L = ProofFile.P1K8.lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨X, l', hX, rfl⟩ := k8_member hb'
  have e : (some l' : Option ℕ) = some l := congrArg Place.link ep
  obtain rfl := Option.some.inj e
  refine ⟨Lk, e1, X, hX, fun run h => ?_, fun run h => ?_, fun run h => ?_⟩
  · obtain ⟨r', h1, hu⟩ := t1 "K8.equations" run h
    obtain ⟨r, h2, hv⟩ := k8_equations_under (ProofFile.k8ParW Z B.G₀ X l')
    obtain rfl : r' = r := Option.some.inj (h1.symm.trans h2)
    exact fun n s x s₁ hy => hv n s x s₁ (hu n s x s₁ hy)
  · obtain ⟨r', h1, hu⟩ := t2 "K8.lsTail" run h
    obtain ⟨r, h2, hv⟩ := k8_lsTail_under (ProofFile.k8ParW Z B.G₀ X l')
    obtain rfl : r' = r := Option.some.inj (h1.symm.trans h2)
    exact fun s s₁ hy => hv s s₁ (hu s s₁ hy)
  · obtain ⟨r', h1, hu⟩ := t2 "K8.tests" run h
    obtain ⟨r, h2, hv⟩ := k8_tests_under (ProofFile.k8ParW Z B.G₀ X l')
    obtain rfl : r' = r := Option.some.inj (h1.symm.trans h2)
    exact fun s s₁ hy => hv s s₁ (hu s s₁ hy)

end LPFK9

#print axioms LPFK9.k8_member
#print axioms LPFK9.k8_ties
