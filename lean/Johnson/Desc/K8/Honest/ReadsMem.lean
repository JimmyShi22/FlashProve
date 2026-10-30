-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/ReadsMem.lean: THE SMALLNESS TEST: WHICH READS LIE IN THE LIBRARY's LIST OF
READS (`readsList`, OnBytes/Tie/Pv/Tail/EndLoops.lean), and what follows for the premises of
Johnson/Desc/K8/Honest/EqTailReturns.lean. Lemmas; none of the library's goals.

  `mem_readsList`     a read (table, segment) lies in the list just if the table is in the list of
                      tables, on a matrix of the list, on vector 0 or 2, and the segment is one of
                      the table's
  `mat_lt_of_mem`     so its matrix is in the list
  `readReady_of_mem`  OF THE SIX CLAUSES OF `ReadReady` FOUR FOLLOW from the read's lying in the
                      list and from the clause on tables (`TailReady.table`'s own words); the two
                      that are left: the vector's array has columns; the last entry's row is below
                      2^32
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.EqTailReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)

/-- Which reads lie in the list. -/
theorem mem_readsList (tl : HTailF2) (funs : Array HFun) (x : HFun × Nat) :
    x ∈ readsList tl funs ↔
      x.1 ∈ funs.toList ∧ x.1.mat < tl.NM ∧ (x.1.tree = 0 ∨ x.1.tree = 2) ∧ x.2 < segs tl x.1 := by
  unfold readsList segs
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨mu, hmu, un, hun, Fn, hFn, hx⟩
    unfold segsOf at hx
    split at hx
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨sg, hsg, rfl⟩ := List.mem_map.1 hx
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨hFn, hmu, by simpa using hun, List.mem_range.1 hsg⟩
    · cases hx
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨x.1.mat, h2, x.1.tree, by simpa using h3, x.1, h1, ?_⟩
    unfold segsOf
    rw [if_pos (by simp)]
    exact List.mem_map.2 ⟨x.2, List.mem_range.2 h4, rfl⟩

theorem mat_lt_of_mem {tl : HTailF2} {funs : Array HFun} {x : HFun × Nat}
    (h : x ∈ readsList tl funs) : x.1.mat < tl.NM := ((mem_readsList tl funs x).1 h).2.1

/-- Of the six clauses of `ReadReady` four follow. -/
theorem readReady_of_mem {tl : HTailF2} {funs : Array HFun} {F : Fork} {x : HFun × Nat}
    (h : x ∈ readsList tl funs)
    (ht : ∀ Fn ∈ funs.toList, Fn.mat < tl.NM → (Fn.tree = 0 ∨ Fn.tree = 2) →
      (tl.ix.U.getD Fn.tree none).isSome = true ∧ Fn.len ≠ 0 ∧
        (tl.mats.getD Fn.mat {}).m % Fn.len = 0 ∧ Fn.phi.size = Fn.len)
    (hc : ∀ tU, tl.ix.U.getD x.1.tree none = some tU → colsOf F tU ≠ 0 ∧
      (0 < (tl.mats.getD x.1.mat {}).k →
        (x.1.start + ((tl.mats.getD x.1.mat {}).k - 1) * segs tl x.1 + x.2) / colsOf F tU
          < 2 ^ 32)) : ∃ tU, ReadReady tl F x.1 x.2 tU := by
  obtain ⟨h1, h2, h3, h4⟩ := (mem_readsList tl funs x).1 h
  obtain ⟨t1, t2, _, _⟩ := ht x.1 h1 h2 h3
  obtain ⟨tU, hU⟩ := Option.isSome_iff_exists.1 t1
  exact ⟨tU, hU, (hc tU hU).1, h2, t2, h4, (hc tU hU).2⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.mem_readsList
#print axioms VerifiableInference.Desc.First.K8.Honest.mat_lt_of_mem
#print axioms VerifiableInference.Desc.First.K8.Honest.readReady_of_mem
