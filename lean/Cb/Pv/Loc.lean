-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Loc.lean: the round in which the verifier draws long positions of an open word of a group and
reads them, as one kind of block: the reduction, its joints, and the statement that it is knowledge
sound.

A chain of a proof is made of blocks of a few kinds. For each kind there is one statement, general
in the block's sizes, that the block is round-by-round knowledge sound between its own joints. This
file has the kind "locations of a group": the prover sends nothing; the verifier draws t long
positions of the open word; the symbols read there join the explicit part, and the open word leaves
the oracles. The reduction is the library's `ldLocOf` (Cb/Ld/LdSwitchLoc.lean) between two
re-bracketings, in the record `LdLocD` (Cb/Req1/LdSegKit.lean). Nothing of it is stated anew.
Definitions and proofs.
Main names:
  `Size`: the type of cores and the library's record of the locations.
  `R`, `eps`, `inJ`, `outJ`: the reduction, one round; its error, (|P| - e - 1) ^ t, a count of
    tuples of positions; the two joints: those of the record's two stages.
  `HAt s`: the statement at the size s: the reduction is knowledge sound (`Reduction.Know`) on the
    statements of `inJ`, between the two relaxed relations, the identity extracting, at `eps s`.
  `OK s`: the condition: `LdLocD.HypK` (Cb/Thin/Kinds/Loc.lean): the relaxed relation and the
    condition of the joint before are those of an open test whose witness is read off the messages;
    the laws of the messages held in the open word.
  `hAt`: the statement holds under `OK s` (`LdLocD.goodK`).
  `point`, `isLocal`, `onOut`: beside it, under `OK s`. `never_rejects`, `rounds`, `errs`, `vals`.
Limits: this is not the round of the same name in the test on a stored table, in which columns of
the table are read: that round is `LdLinP.loc` (Cb/Ld/LdLin.lean; Cb/Pv/Lin.lean). Nothing says that
a round of a chain of the programs is a value of `Size`, that `OK` holds there, or that the error is
small. Nothing on an honest prover.
-/
import Cb.Thin.Kinds.Loc
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Loc
open Iop Prob IOR Cb

/-- What the locations are made of: the library's record, with its type of cores. -/
structure Size (E : Type) [Field E] [Fintype E] : Type 1 where
  Kc : Type
  D : LdLocD E Kc

variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The reduction. -/
noncomputable def R : IOR s.D.src.X s.D.src.Ex s.D.tgt.X s.D.tgt.Ex := s.D.link.R

/-- The error. -/
noncomputable def eps : Err (R s).shape := s.D.link.P.err

/-- The joint before the round: the open word is among the oracles. -/
def inJ : Rels s.Kc s.D.src.X s.D.src.Ex s.D.src.W := s.D.src.J.rels

/-- The joint after the round: the symbols read are claimed of the messages. -/
def outJ : Rels s.Kc s.D.tgt.X s.D.tgt.Ex s.D.tgt.W := s.D.tgt.J.rels

/-- The statement that the round at the size s is knowledge sound. -/
def HAt : Prop :=
  (R s).red.Know (inJ s).on (inJ s).relR (outJ s).relR (fun _ _ w => w) (eps s)

/-- The condition. -/
def OK : Prop := s.D.HypK

/-- The statement holds under the condition. -/
theorem hAt (h : OK s) : HAt s := (s.D.goodK h).know

/-! ### beside the statement -/

theorem point (h : OK s) : Nonempty (R s).shape.IsPoint := (s.D.goodK h).point

theorem isLocal (h : OK s) : (R s).IsLocal := (s.D.goodK h).isLocal

theorem onOut (h : OK s) :
    ∀ a τ b, (inJ s).on a → (R s).red.out a τ = some b → (outJ s).on b :=
  (s.D.goodK h).onOut

/-- The verifier never rejects. -/
theorem never_rejects (x : s.D.src.X) (y : s.D.src.Ex.Str) (τ : Tr (R s).shape) :
    ((R s).out x y τ).isSome := rfl

theorem rounds : (R s).shape.length = 1 := rfl

theorem errs : (eps s).toList = [(Fintype.card s.D.P - s.D.e - 1) ^ s.D.t] := rfl

theorem vals : (R s).shape.chalList = [Fintype.card (Fin s.D.t → s.D.P)] := rfl

end Cb.Pv.Loc

#print axioms Cb.Pv.Loc.hAt
#print axioms Cb.Pv.Loc.onOut
