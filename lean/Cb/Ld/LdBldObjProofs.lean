-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldObjProofs.lean: the proofs of the statements of Cb/Ld/LdBldObj.lean (the object's data,
without the closings of the two linear tests, and its seven standard senders, for variable data).
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
What is said and what is not: the head of that file.

Main names (statements and hypotheses: Cb/Ld/LdBldObj.lean):
  `bldObj_snd`, `bldObj_wf`: the senders in the object; its pair of weights-formedness.
  `bldObj_places`, `bldObj_fair`: the two `Places`, the link's `Reads`; fair seeds of the seven
    families.
  `bldObj_own`: `X.D.Own3₀` from `X.OwnNum`.
-/
import Cb.Ld.LdBldObj
import Cb.Ld.LdBldLinProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

theorem bldObj_snd : Spec.bldObj_snd F E := fun _ => rfl

theorem bldObj_wf : Spec.bldObj_wf F E := fun _ => rfl

theorem bldObj_places : Spec.bldObj_places F E := fun X hO hB hK =>
  ⟨bldLn_places E _ _ _ _ X.A.W.O.toC.P X.Lo X.dT X.w1 X.w3 hO,
    bldLn_places E _ _ _ _ X.RqB.on.ol.toC.P X.Lb X.dB X.w1B X.w3B hB,
    bldLk_reads F E X.Cf X.Lk hK⟩

theorem bldObj_fair : Spec.bldObj_fair F E := fun X =>
  ⟨(bld_fair E X.Lo.FW).1, (bld_fair E X.Lo.FU).1, (bld_fair E X.Lo.FO).1, (bld_fair E X.Lk.F).1,
    (bld_fair E X.Lb.FW).1, (bld_fair E X.Lb.FU).1, (bld_fair E X.Lb.FO).1⟩

theorem bldObj_own : Spec.bldObj_own F E := fun _ h =>
  { lay := ⟨h.layO, h.layB⟩
    q₀e := rfl
    e'le := h.e'le, εfIs := rfl, pyInj := h.pyO
    par := Or.inr ⟨rfl, h.e₀far, rfl⟩, on1Is := rfl, e₁le := h.e₁le,
      ε₁Is := rfl, plInj := bld_binC _ _ h.lay2
    bearK := h.bearK
    onBIs := rfl, εfBIs := rfl, e'far := h.e'far, pyInjB := h.pyB
    monoB := fun _ _ hVU hU =>
      ⟨Finset.eq_empty_iff_forall_notMem.2 fun y => y.elim,
        fun a => le_trans (cnt_mono fun _ hy => hVU hy) (hU.2 a)⟩ }

end
end Cb
