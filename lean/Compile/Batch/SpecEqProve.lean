-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecEqProve.lean: under the hypotheses of its statement, one execution of the honest
prover (`proveBL`) in the language `LStep` (Rom/DeferLate.lean) has the distribution of a session of
the interactive protocol followed by the reduction's subroutine (`proveBW`; both
Compile/Batch/Mirror.lean; the reduction: `theWrapBP`, Compile/Batch/PubWr.lean). Statement only.
The proof: Compile/Batch/EqProve.lean. (Words of this library: lean/GLOSSARY.md.)

  `osOf`   what the reduction knows of the N slots, from what the session returns for J
           (`ownSlots`): for a slot of J its request, the verifier messages of its transcript and
           its output; nothing of the others
  `Spec.eqProveB`   with token numbers shifted (`virtL N₀ δ`, any N₀, δ) and from any state, as an
                    equality of distributions of (result, state):
                    on the left the honest prover samples its coins, does the hash work of all N
                    slots with uniform Fiat-Shamir answers, reads the verifier messages off the
                    answers, and makes the proof strings of the slots of J;
                    on the right the verifier messages and the coins are sampled first (the
                    session), and the subroutine does the same hash work with answers sampled from
                    those that yield the given messages (for the slots of J and, if J is not empty,
                    for the shared chain; in a round with proof-of-work bits: as the doc comment of
                    `tryL` tells, Compile/Batch/Mirror.lean), and makes the proof strings from the
                    outputs

Among the hypotheses is the format of the rounds (Iop/BatchFmt.lean): in a shared round without
format the honest prover reads the verifier message off fixed hash blocks, which is not uniform.
-/
import Compile.Batch.Mirror
import Compile.Batch.SpecFit
import Compile.Step1_defc_L
import Iop.BatchFmt

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.BatchLife (bsess BSess)
open Compile.DefC (virtL)

/-- the slots that hold a request and whose flag is true -/
def ownSlots {Y : Type} {N : ℕ} (x : Fin N → Option Y) (fl : ℕ → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun j => fl j.val = true ∧ (x j).isSome = true

open Classical in
/-- what the reduction knows of the slots, from what the session returns for J -/
def osOf {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {N : ℕ} (x : Fin N → Option Y)
    (J : Finset (Fin N)) (so : BSess Q J) : List (Option (Own Q)) :=
  (List.finRange N).map fun j =>
    if h : j ∈ J then (x j).map fun xj => (xj, so.1 ⟨j, h⟩, so.2 ⟨j, h⟩) else none

/-- One execution (hypotheses below). -/
def Spec.eqProveB : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (sMT sFS : ℕ) (t : Tag) (Y : Type) (E : ExtSpec)
      (Q : BatchInteractiveOracleProof Y E) (Wt : Type) (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (N₀ δ N : ℕ) (w : Wt)
      (fl : ℕ → Bool) (x : Fin N → Option Y) (st : LSt (spec lam K L)),
    RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh → GrFitP H wq → wp.OK → Q.ann.Fmt →
    (virtL N₀ δ (proveBL sMT sFS t Q H wq wp embS embP xin embE depthReq trees w
          fl ((List.finRange N).map x))).run st =
      (bsess H w x (ownSlots x fl)).bind fun so =>
          (virtL N₀ δ
            (proveBW sMT sFS t Q wq embS embP xin embE depthReq
              trees (osOf x (ownSlots x fl) so))).run st

end Compile.Batch
