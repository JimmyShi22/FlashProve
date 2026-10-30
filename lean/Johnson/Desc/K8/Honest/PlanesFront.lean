-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanesFront.lean: THE SMALLNESS TEST: THREE SMALL LAWS THAT THE TEST ON THE
PLANES' WEIGHTS (`planesWeightsHeld`, OnBytes/Model/Tail.lean) WANTS: every entry of the table of
equality weights is a word below the prime; and what a yes of the run "K8.equations" leaves in two
of the fields that it writes: the number of the claim on the key vectors is the number of claims in
front, and the factor of the first claim on the planes is the product of two of the lookup's drawn
elements. Lemmas on the verifier's own text; none of the library's goals.

  `OkList l`   every member of l is a word below the prime
  `okList_fold`, `okList_step`   one more coordinate keeps it
  **`eqTab_ok`**   OnBytes.okE ((eqTab z).getD i zeroE) = true, with no premise
  **`eq_join_bits`**   equations front tl funs F = .ok (tl', F1, cls) ⊢ ∃ g, tl.heard = some g ∧
                   tl'.joinObj9 = some front ∧ tl'.bitFactor9 = mulE g.leaves.eps g.leavesA
Limits. Nothing on values. Nothing on the ledger.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open _root_.Fo.Eq (at_ok eqKeys_cut eqCounts_cut)

/-- Every member is a word below the prime. -/
def OkList (l : List E) : Prop := ∀ a ∈ l, OnBytes.okE a = true

theorem okList_fold (zv : E) : ∀ (l : List E) (n : Array E), OkList n.toList →
    OkList (l.foldl (fun n a => (n.push (subE a (mulE a zv))).push (mulE a zv)) n).toList
  | [], _, h => h
  | a :: l, n, h => by
    refine okList_fold zv l _ fun b hb => ?_
    rw [Array.toList_push, Array.toList_push, List.append_assoc] at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact h b hb
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl
      · exact Part.MaskedSum.okE_sub _ _
      · exact Part.MaskedSum.okE_mul _ _

/-- One more coordinate keeps it. -/
theorem okList_step (t : Array E) (zv : E) : OkList (eqTabStep t zv).toList := by
  unfold eqTabStep
  rw [← Array.foldl_toList]
  exact okList_fold zv t.toList _ fun a ha => by simp at ha

/-- **Every entry of the table of equality weights is a word below the prime.** -/
theorem eqTab_ok (z : Array E) (i : Nat) : OnBytes.okE ((eqTab z).getD i zeroE) = true := by
  have h : OkList (eqTab z).toList := by
    unfold eqTab
    rw [← Array.foldl_toList]
    have key : ∀ (l : List E) (t : Array E), OkList t.toList →
        OkList (l.foldl eqTabStep t).toList := by
      intro l
      induction l with
      | nil => exact fun _ h => h
      | cons a l ih => exact fun t _ => ih _ (okList_step t a)
    refine key z.toList _ fun a ha => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rw [ha]
    exact Part.MaskedSum.okE_one
  rw [Array.getD_eq_getD_getElem?]
  cases e : (eqTab z)[i]? with
  | none => rfl
  | some a => exact h a (Array.mem_toList_iff.2 (Array.mem_of_getElem? e))

/-- **What a yes of the run leaves in two of the fields that it writes.** -/
theorem eq_join_bits {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ g : Forest.Heard, tl.heard = some g ∧ tl'.joinObj9 = some front ∧
      tl'.bitFactor9 = mulE g.leaves.eps g.leavesA := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, -⟩ := eq_parts h
  obtain ⟨tl1, -, t1, t2, t3, -, -, hW, etl, -⟩ :=
    eqTail_marks before tlb tl' funs front s2 (F1, arr) k9
  obtain ⟨-, e1, -⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
  have hJ : EqM.at (eqKeys tl) front F #[] = .ok ((tla, s1.1), s1.2) := (at_ok _ _ _ _).2 h8
  have hB : EqM.at (eqCounts tla) front s1.1 s1.2 = .ok ((tlb, s2.1), s2.2) :=
    (at_ok _ _ _ _).2 h9
  obtain ⟨g, -, j1, -, -, -, -, j6⟩ := eqKeys_cut tl tla F s1.1 #[] s1.2 hJ
  obtain ⟨g', -, k1, -, -, -, -, k6⟩ := eqCounts_cut tla tlb s1.1 s2.1 s1.2 s2.2 hB
  have eg : g' = g := by
    rw [j6] at k1
    exact Option.some.inj (k1.symm.trans j1)
  subst eg
  refine ⟨g', j1, ?_, ?_⟩
  · rw [etl, e1, k6, j6]
    show some (front + (#[] : Array Claim).size) = some front
    rfl
  · rw [etl, e1, k6]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.okList_fold
#print axioms VerifiableInference.Desc.First.K8.Honest.okList_step
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTab_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.eq_join_bits
