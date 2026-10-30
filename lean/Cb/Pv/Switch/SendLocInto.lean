-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Switch/SendLocInto.lean: the code switch between two groups of a request's chain, without and
with a rider (Cb/Pv/Switch/SendLoc.lean, Cb/Pv/Switch/SendLocRide.lean), stated between the joints
with their own conditions: no oracle message that is open has a collision.

In the two files the joints are the library's stages' joints: the joint over the open oracle
messages with its condition moved into the relaxed relation (`IOR.Rels.cf`, Ior/KnowCollGood.lean):
it asks nothing of a statement. A block that follows may want the joint as the library has it, with
its condition (`Sig.over`, Cb/Ld/LdSig.lean). From a joint with the condition moved back to the
joint with its condition no step without rounds leads. This file names the joints with their
conditions and states the same facts between them, in the form "into" (`Reduction.KnowInto`,
Ior/KnowColl.lean): to reach a statement outside the condition behind counts as a win of the prover
and is paid in the errors. By the library's `knowInto_iff` it is the same statement. Definitions and
proofs.

Main names (in the namespaces `Cb.Pv.SendLoc` and `Cb.Pv.SendLocRide` alike):
  `inJP s`, `outJP s`: the two joints with their conditions. `inJ_cf`, `outJ_cf`: `inJ` and `outJ`
    are these with the condition moved, by definition.
  `HAtInto s`: the block is knowledge sound on the statements of `inJP` into the statements of
    `outJP`, at the same errors, with the same extractor. `hAtInto`: it holds under `OK s`.
    `hAtInto_iff`: it is equivalent to `HAt s`.
  `know_plain`: so the block is knowledge sound (`Reduction.Know`) to the relaxed relation of
    `outJP` as it stands.
Limits: those of the two files. That every output statement meets the condition of `outJP` is not
stated, and it is not so: whether the words that were sent have a collision at the seeds is the
prover's doing.
-/
import Cb.Pv.Switch.SendLocRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.SendLoc
open Iop Prob IOR Cb

variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The joint before the block, with its condition. -/
def inJP : Rels s.Kc (stage s).X (stage s).Ex (stage s).W := (stage s).S.over (stage s).A

/-- The joint behind the block, with its condition. -/
def outJP : Rels s.Kc (loc s).tgt.X (loc s).tgt.Ex (loc s).tgt.W := (loc s).tgt.S.over (loc s).tgt.A

theorem inJ_cf : inJ s = (inJP s).cf := rfl

theorem outJ_cf : outJ s = (outJP s).cf := rfl

/-- The statement between the joints with their conditions. -/
def HAtInto : Prop :=
  (R s).red.KnowInto (inJP s).on (outJP s).on (inJP s).relR (outJP s).relR (ext s) (eps s)

/-- The two statements are equivalent. -/
theorem hAtInto_iff : HAtInto s ↔ HAt s := knowInto_iff _ _ _ _ _ _ _ _ _ _ _

theorem hAtInto (h : OK s) : HAtInto s := (hAtInto_iff s).2 (hAt s h)

/-- Knowledge soundness to the relaxed relation behind as it stands. -/
theorem know_plain (h : HAtInto s) :
    (R s).red.Know (inJP s).on (inJP s).relR (outJP s).relR (ext s) (eps s) := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b w hb hw => hτ b w hb (Or.inl hw)) (h a ha)

end Cb.Pv.SendLoc

namespace Cb.Pv.SendLocRide
open Iop Prob IOR Cb

variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The joint before the block, with its condition. -/
def inJP : Rels s.sw.Kc (SendLoc.stage s.sw).X (SendLoc.stage s.sw).Ex (SendLoc.stage s.sw).W :=
  SendLoc.inJP s.sw

/-- The joint behind the block, with its condition; nothing is asked of the rider. -/
def outJP : Rels s.sw.Kc (SendLoc.loc s.sw).tgt.X ((SendLoc.loc s.sw).tgt.Ex.prod s.Cw.nat)
    (SendLoc.loc s.sw).tgt.W :=
  (SendLoc.outJP s.sw).keepE s.Cw.nat

theorem inJ_cf : inJ s = (inJP s).cf := rfl

theorem outJ_cf : outJ s = (outJP s).cf := rfl

/-- The statement between the joints with their conditions. -/
def HAtInto : Prop :=
  (R s).red.KnowInto (inJP s).on (outJP s).on (inJP s).relR (outJP s).relR (ext s) (eps s)

/-- The two statements are equivalent. -/
theorem hAtInto_iff : HAtInto s ↔ HAt s := knowInto_iff _ _ _ _ _ _ _ _ _ _ _

theorem hAtInto (h : OK s) : HAtInto s := (hAtInto_iff s).2 (hAt s h)

/-- Knowledge soundness to the relaxed relation behind as it stands. -/
theorem know_plain (h : HAtInto s) :
    (R s).red.Know (inJP s).on (inJP s).relR (outJP s).relR (ext s) (eps s) := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b w hb hw => hτ b w hb (Or.inl hw)) (h a ha)

end Cb.Pv.SendLocRide

#print axioms Cb.Pv.SendLoc.hAtInto
#print axioms Cb.Pv.SendLocRide.hAtInto
#print axioms Cb.Pv.SendLocRide.know_plain
