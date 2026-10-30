-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/MaskU.lean: proof strings that are not shown need not be made, for the prover with no
query for an empty slot.

The proof string of a slot is made, after all hashing, by reading secret strings: no coin, no oracle
query. So the program `PpU` (Compile/Batch/StarU.lean) that makes proof strings for the adversary's
own requests only gives the same reply to a batch as the program that makes all:
`maskPpU : MaskProg (PpU W WP p)` (Compile/Batch/PubProg.lean). The last part of `proveBU` is the
last part of `proveB`, so the lemmas of Compile/Batch/RealB.lean on it are used as they are.
`maskPp`: the same for `Pp`, from Compile/Batch/RealB.lean.

Notation: `erase c vs` (Compile/Star.lean): forget the rules: tokens are strings, kept in a list
(vs); `mask fl j l` (Compile/Batch/RealB.lean): strike out the entries whose number, counted from j,
has no flag; in Compile/Batch/Chall.lean: `ownFlag b`: is request number a of the batch the
adversary's own; `replyOf b πs`: the reply to a batch: of the proofs that the prover's program
returns, truncated or padded to one for each request, those of the adversary's own requests; slot:
lean/GLOSSARY.md; an empty slot: `none` in the list xs of `proveB` (Compile/Batch/Prover.lean).
-/
import Compile.Batch.PubProg
import Compile.Batch.RealB

noncomputable section

namespace Compile.Batch
open Iop Rom
open Compile.GlueB (GCall ownPf realW)
open RealB

section Prove

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- Under `hsub`: the proof strings for fl are those for fl', some replaced by `none` (`mask`). -/
theorem erase_proveBU_mask (fl fl' : ℕ → Bool) (hsub : ∀ j, fl j = true → fl' j = true)
    (xs : List (Option Y)) (vs : List Bits) :
    erase (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs =
      (erase (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl' xs) vs).bind
        fun o => OComp.pure (mask fl 0 o.1, o.2) := by
  unfold proveBU
  simp only [erase_bind, OComp.bind_assoc,
    erase_finishAll_mask (L := L) Q H wq wp trees w fl fl' hsub]

end Prove

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

theorem erase_PpJU_reply {γ : Type} (k : IskH lam L) (b : ZKCP.Gen.Batch X Unit) (j : ℕ)
    (σ : Equiv.Perm (Fin L.maxBatchSize)) (vs : List Bits) (st : γ) :
    ((erase (PpJU W WP p k (ownFlag b) (reqs b) j σ) vs).bind fun o =>
        OComp.pure (replyOf b o.1, st)) =
      (erase (PpJU W WP p k (fun _ => true) (reqs b) j σ) vs).bind fun o =>
        OComp.pure (replyOf b o.1, st) := by
  unfold PpJU
  cases k.leaves[j]? with
  | none => rfl
  | some lf =>
    dsimp only
    simp only [erase_bind, OComp.bind_assoc]
    rw [erase_proveBU_mask p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ _ _ _
        (slotFlags σ (ownFlag b)) (slotFlags σ fun _ => true) (slotFlags_le σ (ownFlag b))]
    simp only [OComp.bind_assoc, OComp.bind, step_pure_eq, erase_pure]
    exact congrArg _ (funext fun o => congrArg (fun z => OComp.pure (z, st))
      (replyOf_mask b j lf.node.tree.root lf.piL σ o.1))

/-- What is not shown need not be made (`MaskProg`), for `PpU`. -/
theorem maskPpU : MaskProg (PpU W WP p) := by
  intro γ k b vs st
  unfold PpU drawT
  simp only [erase_sample, erase_bind, erase_pure, OComp.bind, erase_PpJU_reply W WP p k b _ _ _ st]

/-- the same for the prover that hashes empty slots -/
theorem maskPp : MaskProg (Pp W WP p) := fun _ k b vs st => erase_Pp_reply W WP p k b vs st

end Compile.Batch
