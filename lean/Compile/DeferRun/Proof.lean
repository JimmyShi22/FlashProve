-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DeferRun/Proof.lean: mode I of a token program that reveals nothing is a plain run with a
log: the proofs of the four statements of Compile/DeferRun/Spec.lean. General in the family of
oracles.

General lemmas. This file states no goal of the release.

  modeI_defer_at, modeI_defer   by induction on the program, constructor by constructor; the first
                 is the statement at one program and one state.
  modeI_seq      from modeI_defer, twice, and the law of a run of two programs one after the other.
  modeI_frame    by induction on the program.
  release_lay    by induction on the list of evaluations.
Follows the pattern of Compile/Step1_life2_Erase.lean.

-/
import Compile.DeferRun.Spec
import Compile.Step1_life2_Erase
import Rom.Handle.Laws
import Rom.Forget

set_option autoImplicit false

noncomputable section

namespace Compile
namespace DeferRun
open Rom Prob

variable {S : OSpec} {sp : Split S} {α β : Type}

theorem modeI_defer_at (mk : Mark S) (c : Step S sp α) : ∀ D : DSt S, Marks mk c D.vals →
    (c.run true D).map keep = (erase c D.vals).runDefer mk D.table (D.evs.map qa) := by
  induction c with
  | pure a =>
    intro D _
    simp only [Step.run, erase, OComp.runDefer, OComp.interp, PMF.pure_map, keep]
  | sample n k ih =>
    intro D h
    simp only [Marks] at h
    simp only [Step.run, erase, OComp.runDefer, OComp.interp_sample, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r D (h r))
  | plain o q k ih =>
    intro D h
    simp only [Marks] at h
    simp only [Step.run, erase, OComp.runDefer, OComp.interp_query,
      Handler.defer_of_not _ h.1, Handler.lazy, PMF.map_bind, PMF.bind_map, Function.comp_def]
    exact congrArg _ (funext fun p => ih p.1 _ (h.2 p.1))
  | fresh ℓ k ih =>
    intro D h
    simp only [Marks] at h
    simp only [Step.run, erase, OComp.runDefer, OComp.interp_sample, PMF.map_bind]
    refine Eq.trans ?_ (Life2.unif_bits_bind ℓ fun u =>
      (erase (k D.vals.length) (D.vals ++ [List.ofFn u])).interp
        (Handler.defer mk Handler.lazy) (D.table, D.evs.map qa)).symm
    exact congrArg _ (funext fun u => ih _ _ (h u))
  | marked o t us pt inj k ih =>
    intro D h
    simp only [Marks] at h
    simp only [Step.run, erase, OComp.runDefer, OComp.interp_query,
      Handler.defer_of_mark _ h.1, PMF.map_bind, PMF.bind_map, Function.comp_def, if_true]
    refine congrArg _ (funext fun r => ?_)
    refine Eq.trans (ih _ _ _ (h.2 r)) ?_
    simp only [List.map_append, List.map_cons, List.map_nil]
    rfl
  | reveal ts k ih =>
    intro D h
    simp only [Marks] at h

theorem modeI_defer : Spec.modeI_defer := fun _ _ _ mk c D h => modeI_defer_at mk c D h

theorem modeI_seq : Spec.modeI_seq := by
  intro S sp α β mk₁ mk₂ c₁ c₂ D h₁ h₂
  rw [Life2.run_bind, PMF.map_bind, ← modeI_defer_at mk₁ c₁ D h₁, PMF.bind_map]
  exact Rom.bind_congr_support _ fun x hx => modeI_defer_at mk₂ (c₂ x.1) x.2 (h₂ x hx)

theorem modeI_frame : Spec.modeI_frame := by
  intro S sp α mk c
  induction c with
  | pure a =>
    intro D _ x hx
    simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨rfl, [], (List.append_nil _).symm, fun _ he => absurd he List.not_mem_nil⟩
  | sample n k ih =>
    intro D h x hx
    simp only [Marks] at h
    simp only [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, _, hx⟩ := hx
    exact ih r D (h r) x hx
  | plain o q k ih =>
    intro D h x hx
    simp only [Marks] at h
    simp only [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨p, _, hx⟩ := hx
    have e := fun hm => ih p.1 _ hm x hx
    exact e (h.2 p.1)
  | fresh ℓ k ih =>
    intro D h x hx
    simp only [Marks] at h
    simp only [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    have e := fun hm => ih _ _ hm x hx
    exact e (h u)
  | marked o t us pt inj k ih =>
    intro D h x hx
    simp only [Marks] at h
    simp only [Step.run, if_true, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, _, hx⟩ := hx
    obtain ⟨h1, new, h2, h3⟩ := ih _ _ _ (h.2 r) x hx
    refine ⟨h1, _ :: new, h2.trans (List.append_assoc _ _ _), fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact h3 e he
  | reveal ts k ih =>
    intro D h
    simp only [Marks] at h

theorem release_lay : Spec.release_lay := by
  intro S shown evs
  induction evs with
  | nil =>
    intro T
    rfl
  | cons e es ih =>
    intro T
    by_cases h : (!e.released && shown.contains e.charged) = true
    · rw [Life2.releaseAll_cons_pos h, List.filter_cons_of_pos
        (p := fun e : Ev S => !e.released && shown.contains e.charged) h, List.map_cons,
        Table.lay_cons]
      exact ih _
    · rw [Life2.releaseAll_cons_neg h, List.filter_cons_of_neg
        (p := fun e : Ev S => !e.released && shown.contains e.charged) h]
      exact ih _

end DeferRun
end Compile

#print axioms Compile.DeferRun.modeI_defer
#print axioms Compile.DeferRun.modeI_seq
#print axioms Compile.DeferRun.modeI_frame
#print axioms Compile.DeferRun.release_lay
