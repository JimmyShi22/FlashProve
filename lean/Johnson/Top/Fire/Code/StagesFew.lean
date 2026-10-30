-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/StagesFew.lean: A FACT ON THE PLAN: a proximity test whose stages' sizes fit together (`ioppOk`) has AT MOST 34 STAGES. Over OnBytes/Iop/Ground | Prox | Wf alone: no block, no description.
Why. The key file's last test asks that two fresh numbers (the own group's; W's) are not the stand-in `noId` = 2 ^ 32 - 1. No block holds a fresh number against it: they part from it by counting alone: the counts are small multiples of the number of stages. By reading of the road: every stage's code is in order (1 ≤ ell; ell + r ≤ 2 ^ min logN 32), each stage but the last has at least one row variable, and from a stage to the next ell' · 2 ^ k' = ell: so ell at least halves, from at most 2 ^ 32 to at least 1.
Main names. `stage_facts`: what `ioppStageOk`'s yes says that is spent here. `pow_le_ell`: behind a stage p, a list of n ≥ 1 further stages in order has 2 ^ (n - 1) ≤ p's ell. `stages_le`: **`ioppOk codes stages answers = true → stages.length ≤ 34`**. `stages_le_of_admitted`: so from `Wf.admitted codes x m = true`: `x.stages.length ≤ 34`.
THE SILLY MEMBER. None: the premise is a test with code, true at the release's plan by its own runs (four stages).
Limits. It is not tied here to a description's tests on the plan, nor to the counts. Nothing on soundness.

-/
import OnBytes.Iop.Wf

set_option autoImplicit false

namespace LPFD
open OnBytes OnBytes.Params

theorem code_ok_facts (c : Code) (h : c.ok = true) : 1 ≤ c.ell ∧ c.ell ≤ 2 ^ 32 := by
  unfold Code.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩, _⟩, h7⟩ := h
  refine ⟨h3, ?_⟩
  have e : c.ell ≤ c.dim := Nat.le_add_right _ _
  exact Nat.le_trans e (Nat.le_trans h7 (Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)))

/-- What a stage's yes says that is spent here. -/
theorem stage_facts (codes : Codes) (answers : Nat) (before : Option IoppStage) (s : IoppStage) (last : Bool)
    (h : ioppStageOk codes answers before s last = true) :
    ∃ c : Code, codes.base[s.code]? = some c ∧ c.ok = true ∧ (last = false → 1 ≤ s.k) ∧
      ∀ p, before = some p → c.ell * 2 ^ s.k = (codes.base.getD p.code default).ell := by
  unfold ioppStageOk at h
  split at h
  · rename_i c zk hc hz
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨ha, _⟩, _⟩, _⟩, _⟩, _⟩, hI⟩, hM⟩ := h
    refine ⟨c, hc, ha, ?_, ?_⟩
    · intro hl
      subst hl
      simp at hI
      exact hI.1
    · intro p hp
      subst hp
      simp at hM
      rw [Array.getD_eq_getD_getElem?]
      exact hM.1.1
  · cases h

theorem getD_of_get (codes : Codes) (i : Nat) (c : Code) (h : codes.base[i]? = some c) : codes.base.getD i default = c := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- Behind a stage p, n ≥ 1 further stages in order: 2 ^ (n - 1) ≤ p's ell. -/
theorem pow_le_ell (codes : Codes) (answers : Nat) : ∀ (l : List IoppStage) (p : IoppStage), l ≠ [] →
    ioppStagesOk codes answers (some p) l = true → 2 ^ (l.length - 1) ≤ (codes.base.getD p.code default).ell
  | [], _, h, _ => absurd rfl h
  | [s], p, _, h => by
    unfold ioppStagesOk at h
    rw [Bool.and_eq_true] at h
    obtain ⟨c, _, hok, _, he⟩ := stage_facts _ _ _ _ _ h.1
    rw [← he p rfl]
    exact Nat.mul_pos (code_ok_facts c hok).1 (Nat.pow_pos (by omega))
  | s :: s' :: rest, p, _, h => by
    unfold ioppStagesOk at h
    rw [Bool.and_eq_true] at h
    obtain ⟨c, hc, _, hk, he⟩ := stage_facts _ _ _ _ _ h.1
    have ih := pow_le_ell codes answers (s' :: rest) s (List.cons_ne_nil _ _) h.2
    rw [getD_of_get codes s.code c hc] at ih
    rw [← he p rfl]
    have e1 : (s :: s' :: rest).length - 1 = ((s' :: rest).length - 1) + 1 := by simp
    rw [e1, Nat.pow_succ]
    exact Nat.mul_le_mul ih (Nat.le_trans (by omega) (Nat.pow_le_pow_right (by omega) (hk rfl)))

/-- **At most 34 stages.** -/
theorem stages_le (codes : Codes) (stages : List IoppStage) (answers : Nat) (h : ioppOk codes stages answers = true) :
    stages.length ≤ 34 := by
  unfold ioppOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hs⟩ := h
  match stages, hs with
  | [], _ => simp
  | [_], _ => simp
  | s :: s' :: rest, hs =>
    unfold ioppStagesOk at hs
    rw [Bool.and_eq_true] at hs
    obtain ⟨c, hc, hok, _, _⟩ := stage_facts _ _ _ _ _ hs.1
    have ih := pow_le_ell codes answers (s' :: rest) s (List.cons_ne_nil _ _) hs.2
    rw [getD_of_get codes s.code c hc] at ih
    have e : 2 ^ ((s' :: rest).length - 1) ≤ 2 ^ 32 := Nat.le_trans ih (code_ok_facts c hok).2
    have e' := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 e
    simp only [List.length_cons] at e' ⊢
    omega

/-- So from the ranges' parameters' own test. -/
theorem stages_le_of_admitted (codes : Codes) (x) (m) (h : Wf.admitted codes x m = true) : x.stages.length ≤ 34 := by
  unfold Wf.admitted at h
  simp only [Bool.and_eq_true] at h
  exact stages_le codes x.stages _ h.2

end LPFD

#print axioms LPFD.stage_facts
#print axioms LPFD.pow_le_ell
#print axioms LPFD.stages_le
#print axioms LPFD.stages_le_of_admitted
