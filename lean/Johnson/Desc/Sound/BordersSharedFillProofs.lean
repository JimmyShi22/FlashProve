-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- The proof of the statement `ExtSSame` of Johnson/Desc/Sound/BordersSharedFill.lean.
import Johnson.Desc.Sound.BordersSharedFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Shared

/-- A member of the block's own sits at the tenant of a message that the block lays. -/
theorem mineS_sits (N : NumbersS) (ms : List Mem) (split : Bool) (k : ℕ) (x : Mem)
    (hx : x ∈ mineS N ms split k) : ∃ m, Comp.msg m ∈ laysAtS split k ∧ x.1.seat x.2 = N.tenant m := by
  obtain ⟨-, h⟩ := List.mem_filter.1 hx
  obtain ⟨c, hc, hd⟩ := List.any_eq_true.1 h
  cases c with
  | msg m => exact ⟨m, hc, of_decide_eq_true hd⟩
  | cells => cases hd
  | w => cases hd
  | index => cases hd

theorem extSSame : ExtSSame := by
  intro cs Xi S₂ Cells Tok G arr smp₂ ms decT₂ c₀ N split k c hc hap s y w
  have hboth : ∀ m', Comp.msg m' ∈ laysAtS split k →
      numOfComp N arr c ≠ some (arr (N.tenant m').1 (N.tenant m').2) ∧
        seatOfComp N c ≠ some (N.tenant m') := by
    intro m' hm'
    have h := List.all_eq_true.1 hap (.msg m') hm'
    have h' : (numOfComp N arr c != some (arr (N.tenant m').1 (N.tenant m').2) &&
        seatOfComp N c != some (N.tenant m')) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨fun e => by simp [e] at h', fun e => by simp [e] at h'⟩
  have key : ∀ n, (∀ m, Comp.msg m ∈ laysAtS split k → arr (N.tenant m).1 (N.tenant m).2 ≠ n) →
      (extS cs G arr smp₂ ms decT₂ c₀ N split k s y w).msg n = w.msg n := by
    intro n hn
    refine extAt_other cs G arr smp₂ decT₂ c₀ _ _ _ _ s y w n ?_
    intro hmem
    obtain ⟨x, hx, hxn⟩ := List.mem_map.1 hmem
    obtain ⟨m, hm, hs⟩ := mineS_sits N ms split k x hx
    refine hn m hm ?_
    rw [← hxn]
    show _ = arr (x.1.seat x.2).1 (x.1.seat x.2).2
    rw [hs]
  have keyP : ∀ q : ℕ × ℕ, (∀ m, Comp.msg m ∈ laysAtS split k → N.tenant m ≠ q) →
      (extS cs G arr smp₂ ms decT₂ c₀ N split k s y w).pad q.1 q.2 = w.pad q.1 q.2 := by
    intro q hq
    refine extAt_other_pad cs G arr smp₂ decT₂ c₀ _ _ _ _ s y w q.1 q.2 ?_
    intro hmem
    obtain ⟨x, hx, hxq⟩ := List.mem_map.1 hmem
    rw [List.append_nil] at hx
    obtain ⟨m, hm, hs⟩ := mineS_sits N ms split k x hx
    refine hq m hm ?_
    rw [← hs]
    exact hxq
  cases c with
  | cells =>
    show (if (laysAtS split k).contains Comp.cells then _ else w.cells) = w.cells
    rw [if_neg]
    intro h
    exact hc (List.contains_iff_mem.1 h)
  | msg m =>
    exact ⟨key _ fun m' hm' e => (hboth m' hm').1 (congrArg some e.symm),
      keyP _ fun m' hm' e => (hboth m' hm').2 (congrArg some e.symm)⟩
  | w =>
    exact ⟨key _ fun m' hm' e => (hboth m' hm').1 (congrArg some e.symm),
      keyP _ fun m' hm' e => (hboth m' hm').2 (congrArg some e.symm)⟩
  | index =>
    exact ⟨key _ fun m' hm' e => (hboth m' hm').1 (congrArg some e.symm),
      keyP _ fun m' hm' e => (hboth m' hm').2 (congrArg some e.symm)⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extSSame
