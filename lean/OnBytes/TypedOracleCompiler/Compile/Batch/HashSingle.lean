-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/HashSingle.lean: the price of the hash event `EM`
(OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean) over ONE hash function, read through a coding.

Why. `hashEvents` (OnBytes/TypedOracleCompiler/Compile/Batch/Hash.lean) prices `EM` for an algorithm over the typed
oracles. Statements on a word under a root, read off a log of strings (`singleTr`,
Rom/ExitDown.lean), ask "outside `EM` of what the coding reads off the log". Here that event has a
price for an algorithm over the one function.

States.
  `Merkle.Events.HashEvent.of_filter`: the hash event of the entries of a trace that pass a test, in
    their order, is a hash event of the whole trace.
  `Pr_EM_singleTr_le`: for every coding m and every algorithm c over one hash function with at most
    t queries: the chance that what m reads off c's own log holds `EM` is at most 2 t² / 2^lam.

How. `down`, `queryBound_down`, `Pr_down`, `withTrace_down`, `withTrace_retr`, `single_upTr`
(Rom/ExitDown.lean); `hashEvents`.

Limits. THE CODING IS FIXED BEFORE THE FUNCTION IS DRAWN: a coding that is made of an answer of the
function (a public digest) is not covered. The log is c's own, whole. The event `EF` is not priced
here. Nothing on soundness. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Hash
import Rom.ExitDown
import Rom.EagerLazy

set_option autoImplicit false

open scoped ENNReal

namespace Merkle.Events

variable {E D : Type} {Ev : Events E D}

/-- **The hash event of a part of a trace is a hash event of the whole trace**: of the entries that
pass a test p, in their order. -/
theorem HashEvent.of_filter (p : E → Bool) {tr : List E} (h : Ev.HashEvent (tr.filter p)) :
    Ev.HashEvent tr := by
  obtain ⟨pre, e, post, c, he, hne, ha, ho⟩ := h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.filter_eq_append_iff.1 he
  obtain ⟨m₁, m₂, rfl, hm, hpe, -⟩ := List.filter_eq_cons_iff.1 h₂
  refine ⟨l₁ ++ m₁, e, m₂, c, by simp, ?_, ha, ?_⟩
  · intro hmem
    rcases List.mem_append.1 hmem with h | h
    · exact hne (h₁ ▸ List.mem_filter.2 ⟨h, hpe⟩)
    · exact hm e h hpe
  · refine ho.mono fun x hx => ?_
    rw [← h₁] at hx
    exact List.mem_append_left _ (List.mem_filter.1 hx).1

end Merkle.Events

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Merkle MeasureTheory
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The price of `EM` over one hash function, through a coding.** For every algorithm c over one
hash function with at most t queries (coins allowed) and every coding m, FIXED BEFORE THE FUNCTION
IS DRAWN: the chance that what m reads off c's own log (`singleTr`, Rom/ExitDown.lean) holds the
hash event `EM` is at most 2 t² / 2^lam. -/
theorem Pr_EM_singleTr_le {α : Type} (m : OracleCoding (typedOracleFamily lam K L) lam) (c : OComp (rom lam) α) (t : ℕ)
    (hq : c.QueryBound t) :
    Rom.Pr c.withTrace (fun _ => {o | EM (singleTr m o.2)}) ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans ?_ (hashEvents (down m c) t (queryBound_down m c t hq))
  rw [← Pr_eq_law, Pr_down m c.withTrace]
  refine lintegral_mono fun F => ?_
  show pr ((down m c.withTrace).runEager F) {o | EM (singleTr m o.2)} ≤
    pr ((down m c).withTrace.runEager F) {o | EM o.2 ∨ EF o.2}
  rw [runEager_down, withTrace_down, pr_map, withTrace_retr (glue m F) c, pr_map, pr_map]
  refine pr_mono _ fun o ho => Or.inl ?_
  have h1 : EM (singleTr m (retr (glue m F) o.2)) := ho
  rw [← single_upTr] at h1
  have h2 : EM (upTr m F o.2) := Merkle.Events.HashEvent.of_filter _ h1
  show EM (upTr m F (retr (glue m F) o.2))
  rw [upTr_retr]
  exact h2

end TypedOracleCompiler.Compile.Batch

#print axioms TypedOracleCompiler.Compile.Batch.Pr_EM_singleTr_le
