-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SkipU.lean: the prover that makes no query for an empty slot is the prover of the
compiled scheme without the work of the empty slots. The proof of `Spec.skipPp`
(Compile/Batch/SpecSkipU.lean). (Words of this library: lean/GLOSSARY.md.)

`skipPp`: the programs `Pp` (Compile/Batch/Star.lean) and `PpU` (Compile/Batch/StarU.lean) are in
the relation `Rom.Skip`, with equal results, for every correspondence w at the start that meets the
two conditions which `Spec.skipPp` states: the number 0 denotes the same string on both sides
(`w.ρ 0 0`); and so does each token in the tree of a copy in the key (`w.ρ s s` and `w.ρ s' s'`, for
each pair (s, s') in `lf.node.tree.salts`, lf in `k.leaves`). Both sample the same copy and the same
placement, and then, if the key has that copy, each runs its compiled prover once (`sk_proveB` of
Compile/Batch/SkipUFinish.lean).

How the proof goes. A full slot, the shared part, the inner nodes of the request tree and the proof
strings are the same terms in both programs, on tokens that correspond. For an empty slot the first
program alone samples coins and a salt, builds trees and queries the oracles; every one of these
queries is charged to a dead token (without a counterpart: `Wd.dd`, Rom/Skip.lean), so the token of
its answer is dead too. The one place where the work of an empty slot meets the rest is its leaf of
the request tree: the first program hashes the dead slot value (`SlotAcc.c`,
Compile/Batch/Prover.lean), the second samples the leaf (`sk_rleaves` of
Compile/Batch/SkipUTree.lean).

Notation:
  `Tok` (a token): a natural number; the program's handle of a string (the head of Rom/Defer.lean).
  `w`: a `Rom.Wd`, "how the tokens of two programs correspond" (Rom/Skip.lean).
  `w.ρ t₁ t₂`: a proposition; "token t₁ of the first program and token t₂ of the second denote the
    same string" (the head of Rom/Skip.lean).
  `Rom.Skip Q w c₁ c₂`: a proposition on two programs (`Step`, Rom/Defer.lean), "by rules on the
    text of the two programs" (the head of Rom/Skip.lean); Q: "what holds of the two results, with
    the correspondence at the end".
  `k`: an `IskH lam L` (Compile/Batch/Star.lean), the key: the index `i`, the first encoding `root`,
    the copies `leaves`.
  `j`, `σ`: a natural number and a permutation of `Fin L.maxBatchSize`; "the copy j and the placement σ"
    (`PpJ`, Compile/Batch/Star.lean); "request number a is in slot σ a" (`slotsOfReq`).
  `xs`, `fr`: a `List X`, the requests of the batch; a map `ℕ → Bool`, "for which requests a proof
    string is made at all" (the head of Compile/Batch/Star.lean).
  an empty slot: one with `SlotAcc.x` = none ("what it holds; none: the slot is empty",
    Compile/Batch/Prover.lean).

Limits: it is a statement about the two programs as terms. It contains no probability; what the
relation means for runs in mode I (Rom/Defer.lean) is proved in Rom/SkipRun.lean.
-/
import Compile.Batch.SkipUFinish

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the batch, once the copy and the placement are sampled -/
theorem SkipU.sk_PpJ (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (k : IskH lam L) (fr : ℕ → Bool)
    (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) {w : Wd} (h0 : w.ρ 0 0)
    (hk : ∀ lf ∈ k.leaves, ∀ s s', some (s, s') ∈ lf.node.tree.salts → w.ρ s s ∧ w.ρ s' s') :
    Skip (fun _ a₁ a₂ => a₁ = a₂) w (PpJ W WP p k fr xs j σ) (PpJU W WP p k fr xs j σ) := by
  unfold PpJ PpJU
  cases hj : k.leaves[j]? with
  | none => exact .pure rfl
  | some lf =>
    refine Skip.bind'
      (SkipU.sk_proveB p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [lf.node.tree]
        (k.i, lf.node.r) _ _ h0 fun tr htr => ?_)
      fun _ π₁ π₂ _ e => ?_
    · obtain rfl : tr = lf.node.tree := List.mem_singleton.mp htr
      exact hk lf (List.mem_of_getElem? hj)
    · subst e
      exact .pure rfl

/-- The proof of `Spec.skipPp`: `PpU` is `Pp` without the work of the empty slots, under the two
conditions on w of that statement. -/
theorem skipPp : Spec.skipPp := fun _ _ _ _ W WP p k fr xs w h0 hk =>
  Skip.sample p.M fun j => Skip.bind' (SkipU.sk_drawT WP.perm w) fun v σ σ' hv e => by
    subst e
    exact SkipU.sk_PpJ W WP p k fr xs j.val σ (hv.ρ _ _ h0) fun lf hlf s s' hs =>
      ⟨hv.ρ _ _ (hk lf hlf s s' hs).1, hv.ρ _ _ (hk lf hlf s s' hs).2⟩

end Compile.Batch
