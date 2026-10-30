-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManySem.lean: the rounds after the batching, taken off in one chain, for any number of
stages.

OnBytes/Slice/ChainSem.lean joins the blocks' statements for three stages by hand (`chain_sem`).
Each of these statements leaves what follows its block open. So they can be joined by induction on a
chain of OnBytes/Slice/ManyDefs.lean.

Main theorems.
 `Chain.exists_bl`   a transcript of a chain's joined shapes is made of blocks' transcripts.
 `chain_many`        if each block of the chain is taken off and the claim at the first stage has
                     no witness, the prover has lost towards any predicate that holds wherever a
                     test of work fails and wherever the yes in the field fails.
Not claimed. That the blocks are taken off (`Chain.Holds`). That any verifier's yes gives the yes in
the field. Nothing on the batching, which comes before the chain. Nothing on the sizes of the error
counts.

-/
import OnBytes.Slice.ManyDefs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-- A transcript of a chain's joined shapes is made of blocks' transcripts. -/
theorem Chain.exists_bl {s : Sg} (c : Chain s) (τ : Tr c.sh) : ∃ b, τ = c.tr b := by
  induction c with
  | last s e dL dB fu fs εb => exact ⟨τ, rfl⟩
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨τF, τ1, rfl⟩ := exists_app (s := PQ.uL (ckP .two) (foldRds s dE dT))
      (t := PQ.uL (ckP .two) [dS, dC] ++ next.sh) τ
    obtain ⟨τC, τ2, rfl⟩ := exists_app (s := PQ.uL (ckP .two) [dS, dC]) (t := next.sh) τ1
    obtain ⟨b, rfl⟩ := ih τ2
    exact ⟨(τF, τC, b), rfl⟩

/-- The chain, for any number of stages. If each block is taken off and the claim q on the word y
has no witness at the first stage's radius, the prover has lost in the chain's rounds, towards any
predicate that holds wherever a test of work fails and wherever the yes in the field fails. -/
theorem chain_many {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (hno : ∀ w, ¬ s.RIn c.rad (q, y) w)
    (bad : Tr c.sh → Prop) (hp : ∀ b, c.pass b = false → bad (c.tr b))
    (H : ∀ b, ¬ c.Acc q y z g b → bad (c.tr b)) : Doomed c.sh c.err bad := by
  induction c with
  | last s e dL dB fu fs εb => exact h q y g fu fs hno bad hp H
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hF, hC, hN⟩ := h
    refine hF _ _ q y z hno bad ?_ ?_
    · intro τF b hc
      obtain ⟨τC, b, rfl⟩ := exists_app (s := PQ.uL (ckP .two) [dS, dC]) (t := next.sh) b
      obtain ⟨b, rfl⟩ := next.exists_bl b
      refine hp (τF, τC, b) ?_
      show (PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τF) && _) = false
      rw [hc]
      rfl
    intro τF h1
    refine hC _ _ _ _ fW h1 (fun b => bad (Tr.app τF b)) ?_ ?_
    · intro τC b hc
      obtain ⟨b, rfl⟩ := next.exists_bl b
      refine hp (τF, τC, b) ?_
      show (_ && (PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τC) && _)) = false
      rw [hc, Bool.false_and, Bool.and_false]
    intro τC h2
    refine ih hN _ (fW τC.1) (fZ τC.1) (fG τC.1) h2 (fun b => bad (Tr.app τF (Tr.app τC b))) ?_ ?_
    · intro b hc
      refine hp (τF, τC, b) ?_
      show (_ && (_ && next.pass b)) = false
      rw [hc, Bool.and_false, Bool.and_false]
    · intro b ha
      exact H (τF, τC, b) ha

end OnBytes.Slice
