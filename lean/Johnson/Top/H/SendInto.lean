-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/SendInto.lean: the kind of block SEND as a value of `Kind` (Johnson/Top/Kind.lean)
whose joint behind the block keeps its own condition: no member has a collision.

Nothing new is proved: every line is a call of Cb/Pv/SendInto.lean or Cb/Pv/Send.lean. The callers,
the joint before the block, the reduction, the extractor and the errors are those of `kSend`
(Johnson/Top/H/Send.lean); the joint behind the block is `Cb.Pv.Send.outJInto` in the place of
`Cb.Pv.Send.outJ`.
Main names:
  `kSendInto L`: the kind, at a written list of callers.
  `kSendInto_know`, `_point`, `_local`: as for `kSend`; `_know` and `_local` under `SendOK L`.
  `kSendInto_good`: under `SendOK L` every block has the property that a typed list of blocks asks
    (`KObj.BK.Good`, Johnson/E/KObj/Blocks.lean), whose third clause is knowledge soundness into the
    next joint's condition: that is the library's theorem on a sending as it stands.
  `HSendInto`: closed, over the field `Cb.Gl.E`. `hSendInto`: it holds.
Limits: `Kind.OnOut` is not shown of this kind, and `kSendInto_good` does not go through
`Kind.good`: the verifier never rejects, and nothing says that an output statement has no collision;
to reach one with a collision is paid in the first round's error. No list of callers is written
here. Nothing says that a block of the kind is the step that the programs run, or that its errors
are small. Nothing on an honest prover.

-/
import Johnson.Top.H.Send
import Cb.Pv.SendInto

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

section
variable {E : Type} [Field E]

/-- SEND into the statements without a collision, at a written list of callers. -/
@[reducible] noncomputable def kSendInto (L : List (SendCaller E)) : Kind.{1} where
  Size := SendCaller E
  sizes := L
  src := fun c => jOf c.A
  dst := fun c => jOf (Cb.Pv.Send.outJInto c.s c.A c.back)
  block := fun c =>
    ⟨Cb.Pv.Send.R c.s c.X c.E₀, fun _ _ w => c.back (c.s.N.msgs w.1) w.2, Cb.Pv.Send.eps c.s⟩

variable (L : List (SendCaller E))

theorem kSendInto_know (h : SendOK L) : (kSendInto L).Know := fun c hc =>
  Cb.Pv.Send.know_plain c.s (Cb.Pv.Send.hAtInto c.s (h c hc)) c.A c.back

theorem kSendInto_point : (kSendInto L).Point := fun c _ => Cb.Pv.Send.point c.s c.X c.E₀

theorem kSendInto_local (h : SendOK L) : (kSendInto L).Local := fun c hc =>
  Cb.Pv.Send.isLocal c.s c.X c.E₀ (h c hc).laws

theorem kSendInto_good (h : SendOK L) : ∀ c ∈ L, ((kSendInto L).block c).Good := fun c hc =>
  ⟨Cb.Pv.Send.point c.s c.X c.E₀, Cb.Pv.Send.isLocal c.s c.X c.E₀ (h c hc).laws,
    Cb.Pv.Send.hAtInto c.s (h c hc) c.Kc c.X c.W c.W' c.E₀ c.A c.back⟩

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the condition. -/
def HSendInto : Prop := ∀ L : List (SendCaller Cb.Gl.E), SendOK L → (kSendInto L).Know

theorem hSendInto : HSendInto := kSendInto_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hSendInto
#print axioms VerifiableInference.OnPublicFiles.kSendInto_good
