-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectProofs.lean: the proofs of the statements of Cb/Obj/LdObject.lean.

In standard terms: the object (`LdObj`) has a configuration, data of the two phases and the link,
and five terms, one of each sub-protocol's kind; `Obj.subs` packs them as the four sub-protocols
(the test for linear constraints at its two settings) from which Hiop/RecBuild.lean forms a
holographic IOP with an untrusted committer and records.

No axiom beyond Lean's three. No hypothesis beside the premises that are written out and whatever
the arguments hold as proofs.
Each item of the four lists is the theorem of its own file (Cb/Obj/LdObjectOff.lean,
Cb/Obj/LdObjectLinkPair.lean, Cb/Obj/LdObjectReq.lean, Cb/Obj/LdObjectOnB.lean); `fitOff` and
`fitOn` are fields of `Obj.OK L` itself; the properties of the object are `Hiop.rec_main`
at `Cb.ldCf_props`.

Main names (statements and hypotheses: Cb/Obj/LdObject.lean):
  `ldObj_hyp`, `ldObj_props`.

Limits: the theorems assume `Obj.OK L` (all but `ldObj_padBij_none`), which is not shown to be
satisfiable here. What the head of Cb/Obj/LdObject.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states the conclusion of `ldObj_hyp` of a concrete object.




-/
import Cb.Obj.LdObject

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
theorem ldObj_hyp : Spec.ldObj_hyp F E := by
  intro Obj L h
  have hd := h.conf.core.dist
  have he := h.conf.rad
  have hW := ldOW_object F E Obj.off.ol Obj.Kw Obj.wf Obj.cw h.wf
  have hT := ldOT_object F E Obj.off.ol Obj.lin Obj.dOff hd he h.lin
  have hK := ldOlA_object F E Obj.Cf Obj.K Obj.on0K Obj.on1K Obj.link L h.conf h.fitsK h.link
  have hR := ldOR_object F E Obj.on.ol Obj.Kr Obj.req Obj.cr Obj.z0 Obj.r0 h.req
  have hB := ldOBT_object F E Obj.on.ol Obj.N Obj.linB Obj.dOn hd he h.linB
  exact ⟨⟨hW.1, hT.1, hK.1, hR.1, hB.1, h.fitOff, h.fitOn⟩, ⟨hW.2, hT.2, hK.2, hR.2, hB.2⟩⟩

-- Limit: no theorem of this library states that the hypotheses of this theorem can be met together.
theorem ldObj_props : Spec.ldObj_props F E := fun Obj L b εs h hB hb hP hR =>
  rec_main Obj.Cf.conf Obj.subs Obj.nums b (L.choose 2 * Obj.Cf.Z.err) εs
    (ldCf_props F E Obj.Cf L b h.conf hB hb) (ldObj_hyp F E Obj L h) hP hR

omit [Fintype F] [Fintype E] in
theorem ldObj_padBij_none : Spec.ldObj_padBij_none F E := by
  intro Cf hS hP ρ a
  constructor
  · intro c c' _
    exact funext fun p => (hP.false p).elim
  · intro y
    exact ⟨fun p => (hP.false p).elim, funext fun s => (hS.false s).elim⟩

end
end Cb
