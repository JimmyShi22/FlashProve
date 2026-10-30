-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Split.lean: the round in which one row on two groups of oracle messages becomes a row on each
group, as one kind of block: the reduction, its joints, and the statement that it is knowledge
sound.

A chain of a key file or of a proof is made of blocks of a few kinds. For each kind there is one
statement, general in the block's sizes, that the block is round-by-round knowledge sound between
its own joints. This file has the kind "split": the prover says one scalar, the value of the first
group's part of the row with a mask entry added; the verifier says nothing. The reduction is the
library's `ldSplitR` (Cb/Ld/LdSplit.lean), in the record `LdSplD` (Cb/Req1/LdSegKit.lean). Nothing
of it is stated anew. Definitions and proofs.
Main names:
  `Size`: the type of cores and the library's record of a split.
  `R`, `eps`, `inJ`, `outJ`: the reduction, one round; its error, 0; the two joints: those of the
    record's two stages.
  `HAt s`: the statement at the size s: the reduction is knowledge sound (`Reduction.Know`) on the
    statements of `inJ`, between the two relaxed relations, the identity extracting, at `eps s`.
  `hAt`: it holds at every size, without a premise (`LdSplD.goodK`,
    Cb/Thin/Kinds/BatSplitStep.lean).
  `point`, `isLocal`, `onOut`: beside it, without a premise. `never_rejects`, `rounds`, `errs`,
    `vals`: one round, the error 0, one value of the verifier's message.
Limits: nothing says that a split of a chain of the programs is a value of `Size`, or which entry is
the mask entry there. Nothing on an honest prover.
-/
import Cb.Thin.Kinds.BatSplitStep
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Split
open Iop Prob IOR Cb

/-- What a split is made of: the library's record, with its type of cores. -/
structure Size (E : Type) [Field E] [Fintype E] : Type 1 where
  Kc : Type
  D : LdSplD E Kc

variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The reduction. -/
def R : IOR s.D.src.X s.D.src.Ex s.D.tgt.X s.D.tgt.Ex := s.D.link.R

/-- The error. -/
def eps : Err (R s).shape := s.D.link.P.err

/-- The joint before the round: one row on the two groups' messages. -/
def inJ : Rels s.Kc s.D.src.X s.D.src.Ex s.D.src.W := s.D.src.J.rels

/-- The joint after the round: a row on each group's message. -/
def outJ : Rels s.Kc s.D.tgt.X s.D.tgt.Ex s.D.tgt.W := s.D.tgt.J.rels

/-- The statement that the round at the size s is knowledge sound. -/
def HAt : Prop :=
  (R s).red.Know (inJ s).on (inJ s).relR (outJ s).relR (fun _ _ w => w) (eps s)

/-- It holds at every size. -/
theorem hAt : HAt s := s.D.goodK.know

/-! ### beside the statement, for all sizes -/

theorem point : Nonempty (R s).shape.IsPoint := s.D.goodK.point

theorem isLocal : (R s).IsLocal := s.D.goodK.isLocal

theorem onOut : ∀ a τ b, (inJ s).on a → (R s).red.out a τ = some b → (outJ s).on b :=
  s.D.goodK.onOut

/-- The verifier never rejects. -/
theorem never_rejects (x : s.D.src.X) (y : s.D.src.Ex.Str) (τ : Tr (R s).shape) :
    ((R s).out x y τ).isSome := rfl

theorem rounds : (R s).shape.length = 1 := rfl

theorem errs : (eps s).toList = [0] := rfl

theorem vals : (R s).shape.chalList = [1] := rfl

end Cb.Pv.Split

#print axioms Cb.Pv.Split.hAt
#print axioms Cb.Pv.Split.onOut
