-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/OneAnswer.lean: the code switch: AT EACH ENTRY OF THE FRAME's LIST
OF KEPT PLACES THE FRONT's STATEMENT HAS A MESSAGE WHOSE SHAPE COUNTS ONE ANSWER: the third clause
of what Johnson/P1K2R/DebtsAt.lean asks on the fenced states (hst), and the premise h of
Tw/K2C/OneStored.lean's hone_of_both: FROM THE TEST ON THE FRONT AND CLOSED FACTS.
  kept_old_at  each entry of the frame's list of kept places (the program's switchFrame) names one
               of the numbers that the carried rows keep (switchKept), by place
  one_answer_of_test  THE STATEMENT: from K2Hands/FrontB2.lean's frontB2 (its clauses «what the
               carried rows keep is olds» and «the kept old messages' shapes are the written
               front's»: FrontSide.lean's kept_of_test) · hty: the written front's kept old
               messages' shapes are the typed kept members' (keptTyped_at, KeptTypedFull.lean: by
               Lean's kernel at the 25 written entries) · keptShapeB r (a typed kept member counts
               one answer) · the frame at the front
SO THE DEBT hone (each kept old oracle message has just one stored OOD claim) RESTS ON: the test on
the front, the two invariants on stored sample rows, and closed facts.
LIMITS. A join. None of the premises is shown at a real value here. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.FrontSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.First VerifiableInference.Desc.First.K2Hands

/-- Each entry of the frame's list of kept places names one of the numbers that the carried rows
keep. -/
theorem kept_old_at {x : _root_.Tw.K2.Front} {W : SwitchFrame} (hW : K2.frameAt x = some W) :
    ∀ κ ∈ W.kept, ∃ i : ℕ, (switchKept x.f.rows).toList[i]? = some κ.old := by
  unfold K2.frameAt switchFrame at hW
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hW
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hW
  intro κ hκ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hκ
  have hi' := List.mem_range.1 hi
  refine ⟨i, ?_⟩
  simp [Array.getD_eq_getD_getElem?, hi']

/-- **AT EACH ENTRY OF THE FRAME's KEPT LIST THE FRONT's STATEMENT HAS A MESSAGE WHOSE SHAPE COUNTS
ONE ANSWER.** -/
theorem one_answer_of_test {r : SwRow} {f₀ fx : _root_.Tw.K2.Front} {W' W : SwitchFrame}
    {grp rows n0 : ℕ} {olds : List ℕ} (h1 : frontB2 f₀ W' grp rows n0 olds fx = true)
    (hty : keptShapes f₀ = r.kept.map fun i => (r.lo[i]?).map (·.1))
    (hs : keptShapeB r = true) (hW : K2.frameAt fx = some W) :
    ∀ κ ∈ W.kept, ∃ xo : OnBytes.Oracle, fx.st.oracles[κ.old]? = some xo ∧
      xo.shape.answers = 1 := by
  intro κ hκ
  obtain ⟨hl, hsh⟩ := kept_of_test h1 hty
  obtain ⟨i, hi⟩ := kept_old_at hW κ hκ
  have n4 : (switchKept fx.f.rows).toList = olds := by
    simp only [frontB2, Bool.and_eq_true] at h1
    exact (nums_of_test h1.1.2).2.2.2
  rw [n4] at hi
  have hil : i < r.kept.length := by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨k, hk⟩ : ∃ k, r.kept[i]? = some k := ⟨_, List.getElem?_eq_getElem hil⟩
  have e := List.all_eq_true.1 hs k (List.mem_of_getElem? hk)
  obtain ⟨y, hy, ha⟩ : ∃ y, r.lo[k]? = some y ∧ y.1.answers = 1 := by
    cases hy : r.lo[k]? with
    | none => rw [hy] at e; cases e
    | some y =>
      rw [hy] at e
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at e
      exact ⟨y, rfl, e.1⟩
  obtain ⟨xo, hx, ex⟩ := hsh i κ.old y hi (by rw [hk]; exact hy)
  exact ⟨xo, hx, by rw [ex]; exact ha⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.kept_old_at
#print axioms VerifiableInference.Desc.First.K2Caller.one_answer_of_test
