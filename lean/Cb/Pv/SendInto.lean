-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/SendInto.lean: the sending of a family of oracle messages (Cb/Pv/Send.lean), stated into the
joint behind it with that joint's own condition: no member has a collision.

In Cb/Pv/Send.lean the joint behind a sending is `outJ`: the library's joint over the family with
its condition moved into the relaxed relation (`IOR.Rels.cf`, Ior/KnowCollGood.lean): it asks
nothing of a statement. A block that follows may want the joint as the library has it, whose
condition says that no member has a collision (`Sig.over`, `Sig.CF`, Cb/Ld/LdSig.lean). This file
names that joint and states the same fact into it: a call of the library's theorem. One short proof
is new: `know_plain`.
Main names (s : `Size E` of Cb/Pv/Send.lean):
  `outJInto s A back`: the joint behind the sending, with its condition. `outJ_cf`: `outJ` is that
    joint with the condition moved, by definition.
  `HAtInto s`: the statement that the sending is knowledge sound on the statements of A into the
    statements without a collision (`Reduction.KnowInto`, Ior/KnowColl.lean): to reach a statement
    with a collision counts as a win of the prover and is paid in the errors.
  `hAtInto`: it holds under `Size.OK`: the library's `ldSendFam_into`. `hAtInto_iff`: it is the
    statement `HAt s`, by definition.
  `know_plain`: so the sending is knowledge sound (`Reduction.Know`) to that joint's relaxed
    relation as it stands.
Limits: those of Cb/Pv/Send.lean. The verifier never rejects (`never_rejects`, Cb/Pv/Send.lean):
that every output statement meets the condition of `outJInto` is not stated, and nothing here gives
it.

-/
import Cb.Pv.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Send
open Iop IOR Cb

variable {E : Type} [Field E] (s : Size E)

/-- The joint after the sending, with its condition. -/
def outJInto {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W) (back : s.N.Msg → W' → W) :
    Rels Kc (X × s.N.Smp) (E₀.prod s.N.ext) (s.N.Wit × W') :=
  s.N.over (s.N.pull A back)

theorem outJ_cf {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W)
    (back : s.N.Msg → W' → W) : outJ s A back = (outJInto s A back).cf := rfl

/-- The statement that the sending at the size s is knowledge sound into the statements without a
collision. -/
def HAtInto : Prop :=
  ∀ (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W) (back : s.N.Msg → W' → W),
    (R s X E₀).red.KnowInto A.on (outJInto s A back).on A.relR (outJInto s A back).relR
      (fun _ _ w => back (s.N.msgs w.1) w.2) (eps s)

theorem hAtInto (h : s.OK) : HAtInto s := fun Kc X W W' E₀ A back =>
  ldSendFam_into E s.N s.Sd Kc X W W' E₀ A back s.L h.fair h.list h.evades

/-- The two statements are one. -/
theorem hAtInto_iff : HAtInto s ↔ HAt s := Iff.rfl

/-- Knowledge soundness to the joint's relaxed relation as it stands. -/
theorem know_plain (h : HAtInto s) {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W)
    (back : s.N.Msg → W' → W) :
    (R s X E₀).red.Know A.on A.relR (outJInto s A back).relR
      (fun _ _ w => back (s.N.msgs w.1) w.2) (eps s) := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b w hb hw => hτ b w hb (Or.inl hw)) (h Kc X W W' E₀ A back a ha)

#print axioms hAtInto
#print axioms know_plain

end Cb.Pv.Send
