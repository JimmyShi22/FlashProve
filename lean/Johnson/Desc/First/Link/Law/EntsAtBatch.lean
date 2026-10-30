-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsAtBatch.lean: THE JOIN THAT THE SEVEN CLAUSES "ents…" OF WHAT IS
FIXED IN FRONT OF A BATCHING SHARE. Each says of one run's forms l: the test `entsAtB` (EntAtTests.lean)
says yes of l at the fixed structure and the snapshot's looks. That test falls in two: (A) the one
array i of the third vector is a table's vector's array, apart from the other sorts, and looks
it; (B) "the make": every entry that a form of l names stands at virtual row 0 of array i.
HERE: (A) IS NO NEW DEBT: it follows from the static clause. So each of the seven comes down to (B).
One definition, statements and proofs.

  `EntsMake i l`: (B).
  `vectorB_of_tableAt`: `TableAt` (SistersFull.lean) gives a yes of `vectorAtB`: the converse of
    `tableAt_of_vectorB`.
  `entsAtB_of_make`: a yes of `vectorAtB` at i, and the make ⊢ a yes of `entsAtB`.
  `EntsAt π nU q l`: the clause's body, in the letters of `EntsOk` (OkOne.lean, which
    is not imported here).
  `ents_of_static`: **the static clause at q; the fixed structure names i for the third vector; the
    third vector is planned with at least one entry; the make ⊢ `EntsAt π nU q l`.**
  `ents_nil`: forms that name no entry pass, whatever else.
Limits. The make is shown of no run here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntAtTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.K9L

/-- **The make**: every entry that a form of l names stands at virtual row 0 of array i. -/
def EntsMake (i : ℕ) (l : List Aff) : Prop :=
  ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.row = 0 ∧ x.tree = i

/-- The converse of `tableAt_of_vectorB`. -/
theorem vectorB_of_tableAt {nU : Array ℕ} {tl : HTailF2} {sh : List Look} {t : ℕ}
    (h : TableAt nU tl sh t) : vectorAtB nU tl sh t = true := by
  obtain ⟨⟨n0, a0, a1, a2⟩, b, c, d, e, f⟩ := h
  unfold vectorAtB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨?_, b⟩, c⟩, ?_⟩, ?_⟩, f⟩
  · refine List.any_eq_true.2 ⟨n0, List.mem_range.2 a0, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨a1, a2⟩
  · exact List.all_eq_true.2 fun mu hmu => decide_eq_true (d mu (List.mem_range.1 hmu))
  · refine List.all_eq_true.2 fun p hp => decide_eq_true ?_
    rcases List.mem_append.1 hp with k | k
    · exact e 0 p k
    · exact e 1 p k

theorem entsAtB_of_make {nU : Array ℕ} {tl : HTailF2} {sh : List Look} {i : ℕ} {l : List Aff}
    (hv : vectorAtB nU tl sh i = true) (hm : EntsMake i l) : entsAtB nU tl sh l = true := by
  unfold entsAtB
  refine List.all_eq_true.2 fun f hf => List.all_eq_true.2 fun x hx => ?_
  obtain ⟨r, t⟩ := hm f hf x hx
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true r, by rw [t]; exact hv⟩

section
variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **The clause's body.** -/
def EntsAt (nU : Array ℕ) (q : α × Option Pub9) (l : List Aff) : Prop :=
  ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v →
    entsAtB nU tlb (v.F.trees.toList.map look) l = true

/-- **FROM THE STATIC CLAUSE AND THE MAKE.** -/
theorem ents_of_static {nU : Array ℕ} {q : α × Option Pub9} {l : List Aff} {i : ℕ}
    (hs : ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π q.1).1 = some tlb → tlb.ix.U.getD 2 none = some i)
    (h0 : 0 < nU.getD 2 0) (hm : EntsMake i l) : EntsAt π nU q l :=
  fun tlb v e1 e2 =>
    entsAtB_of_make (vectorB_of_tableAt (tableAt_of_static (hs tlb v e1 e2) (hU tlb e1) h0)) hm

/-- Forms that name no entry pass. -/
theorem ents_nil {nU : Array ℕ} {q : α × Option Pub9} {l : List Aff}
    (h : ∀ f ∈ l, f.ents = #[]) : EntsAt π nU q l := by
  intro tlb v _ _
  unfold entsAtB
  refine List.all_eq_true.2 fun f hf => ?_
  rw [h f hf]
  rfl

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.vectorB_of_tableAt
#print axioms VerifiableInference.Desc.LinkJoin.entsAtB_of_make
#print axioms VerifiableInference.Desc.LinkJoin.ents_of_static
#print axioms VerifiableInference.Desc.LinkJoin.ents_nil
