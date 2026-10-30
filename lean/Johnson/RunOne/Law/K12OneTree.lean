-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/K12OneTree.lean: THE TWO
ORACLE MESSAGES OF A SWITCH INSIDE A PROXIMITY TEST SHARE ONE TREE: where layTrees lays the switch's
two notices (the new tables; the mask that comes early with them), the laying has one tree
(oneTree_all); so has the laying of a fresh mask that comes alone (oneTreeMask_all). For all codes;
no premise.

-/
import Johnson.Desc.K12.Law.SwDid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12OneTree
open OnBytes OnBytes.Params

/-- A fold in Option whose every step keeps a number keeps it. -/
theorem foldlM_keeps {σ ι : Type} (sz : σ → ℕ) (step : σ → ι → Option σ)
    (hstep : ∀ s i s', step s i = some s' → sz s' = sz s) :
    ∀ (l : List ι) (s s' : σ), l.foldlM step s = some s' → sz s' = sz s
  | [], s, s', h => by
    obtain rfl : s = s' := Option.some.inj h
    rfl
  | i :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    cases hs : step s i with
    | none =>
      rw [hs] at h
      cases h
    | some t =>
      rw [hs] at h
      exact (foldlM_keeps sz step hstep l t s' h).trans (hstep s i t hs)

theorem of_ite_pure {α : Type} {c : Prop} [Decidable c] {x y : α}
    (h : (if c then (pure x : Option α) else none) = some y) : x = y := by
  split_ifs at h
  exact Option.some.inj h

theorem of_ite_none {α : Type} {c : Prop} [Decidable c] {x y : α}
    (h : (if c then none else (pure x : Option α)) = some y) : x = y := by
  split_ifs at h
  exact Option.some.inj h

/-- **The switch's two notices share one tree.** -/
theorem oneTree_all (codes : Codes) (nx : IoppStage) (last : Bool) (lay : TreeLay)
    (h : layTrees codes (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
      (H2K.Sw.othersOf last nx)) = some lay) : lay.shapes.size = 1 := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := of_ite_pure h
  show (filled.1.map _).size = 1
  rw [Array.size_map, foldlM_keeps (fun s => s.1.size) _ ?_ _ _ _ hf]
  · have hk : (2 ^ nx.k == 0) = false := by simp
    cases last
    · simp [Slice.sentOf, H2K.Sw.othersOf, switchTargetStage, foldMaskNotice, ioppFoldShape,
        List.range_succ, hk]
    · simp [Slice.sentOf, H2K.Sw.othersOf, switchTargetStage, baseMaskNotice,
        List.range_succ, hk]
  · intro s i s' hs
    obtain rfl := of_ite_none hs
    simp

/-- **A fresh mask that comes alone has one tree.** -/
theorem oneTreeMask_all (codes : Codes) (c : IoppStage) (L : GroupLayout) (lay : TreeLay)
    (h : layTrees codes #[foldMaskNotice (ioppFoldShape c L)] = some lay) :
    lay.shapes.size = 1 := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := of_ite_pure h
  show (filled.1.map _).size = 1
  rw [Array.size_map, foldlM_keeps (fun s => s.1.size) _ ?_ _ _ _ hf]
  · simp [foldMaskNotice, ioppFoldShape, List.range_succ]
  · intro s i s' hs
    obtain rfl := of_ite_none hs
    simp

end Johnson.RunOne.Law.K12OneTree

#print axioms Johnson.RunOne.Law.K12OneTree.foldlM_keeps
#print axioms Johnson.RunOne.Law.K12OneTree.of_ite_pure
#print axioms Johnson.RunOne.Law.K12OneTree.of_ite_none
#print axioms Johnson.RunOne.Law.K12OneTree.oneTree_all
#print axioms Johnson.RunOne.Law.K12OneTree.oneTreeMask_all
