-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/BindingMany.lean: two facts on `mapSlots g b` (Compile/Spec.lean), which runs one algorithm
`g a` for each entry `a` of a list `b`, in sequence. If every `g a` is coin-free and makes at most t
queries (`DetBound`, Compile/GlueBinding.lean), then the whole is coin-free and makes at most
length · t queries (`detBound_mapSlots`), and each `g a` runs to its result within the common trace
(`runsIn_mapSlots`; `RunsIn`: Compile/Spec.lean).
-/
import Compile.GlueBinding
import Compile.HashEvents
import Iop.State

noncomputable section

namespace Compile.BindingMany

open Iop Rom Prob
open scoped ENNReal

section Tools
variable {S : OSpec} {β Pf : Type}

/-- Coin-free algorithms with at most t queries each, one for each entry of a list, in sequence: at
most length · t queries. -/
theorem detBound_mapSlots {g : β → OComp S Pf} {t : ℕ} (hg : ∀ a, DetBound (g a) t) :
    ∀ b : List β, DetBound (mapSlots g b) (b.length * t)
  | [] => trivial
  | a :: l => by
      have h : DetBound (mapSlots g (a :: l)) (t + (l.length * t + 0)) := by
        simp only [mapSlots]
        refine (hg a).bind fun π => (detBound_mapSlots hg l).bind fun r => ?_
        trivial
      refine h.mono ?_
      simp only [List.length_cons]
      nlinarith

/-- Each of them runs to its result within the common trace. -/
theorem runsIn_mapSlots {g : β → OComp S Pf} {t : ℕ} (hg : ∀ a, DetBound (g a) t) (f : Fam S) :
    ∀ (b : List β), ∀ o ∈ ((mapSlots g b).withTrace.runEager f).support, ∀ e ∈ b.zip o.1.val,
      ∃ tr : Trace S, tr ⊆ o.2 ∧ RunsIn tr (g e.1) e.2
  | [], o, _, e, he => by simp at he
  | a :: l, o, ho, e, he => by
      simp only [mapSlots, withTrace_bind, OComp.runEager_bind, PMF.mem_support_bind_iff] at ho
      obtain ⟨z1, hz1, y, ⟨z2, hz2, y2, hy2, hy⟩, ho⟩ := ho
      have hy2' : y2 ∈
          (PMF.pure ((⟨z1.1 :: z2.1.val, by simp [z2.1.property]⟩ : ZKCP.Gen.Slots Pf (a :: l)),
              ([] : Trace S))).support := hy2
      have hy' : y ∈ (PMF.pure (y2.1, z2.2 ++ y2.2)).support := hy
      have ho' : o ∈ (PMF.pure (y.1, z1.2 ++ y.2)).support := ho
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hy2' hy' ho'
      subst hy2'
      subst hy'
      subst ho'
      have he' : e ∈ (a, z1.1) :: l.zip z2.1.val := he
      rcases List.mem_cons.1 he' with rfl | he''
      · exact ⟨z1.2, fun x hx => List.mem_append_left _ hx, runsIn_of_mem_support (hg a) f z1 hz1⟩
      · obtain ⟨tr, hsub, hr⟩ := runsIn_mapSlots hg f l z2 hz2 e he''
        exact ⟨tr, fun x hx => List.mem_append_right _ (List.mem_append_left _ (hsub hx)), hr⟩

end Tools

end Compile.BindingMany

