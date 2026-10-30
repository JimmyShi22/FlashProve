-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmIdxProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsmIdx.lean (the assembled
lookup on keys that read an encoded index).

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names, each under the hypotheses of its statement (Cb/Ld/LdLkpAsmIdx.lean):
  `ldLkpAsmI_good`: `IOR.GoodB` of `A.subI C S msg`; between which joints, and which statements
    knowledge soundness covers: its row in the head of Cb/Ld/LdLkpAsmIdx.lean.
  `ldLkpAsmI_plain`: the format at the base (Cb/Ld/LdLkpFormat.lean: `Plain`).
  `ldLkpAsmI_idx`: see its statement in Cb/Ld/LdLkpAsmIdx.lean.
  `ldLkpAsmI_passes`, `ldLkpAsmI_same`: over S: state and samples are handed on by the verifier
    (`ldLkpAsmI_passes`); the witness by the honest prover (`ldLkpAsmI_same`).
How `ldLkpAsmI_good` is got (read off the proof): the index-lifting rule over a signature,
`idxLift_goodB` (Cb/Ld/LdWfIdxProofs.lean), at `ldLkpAsm_base` (Cb/Ld/LdLkpAsmProofs.lean), with
`ldLkpFmt_pass` and `ldLkpFmt_plain` (Cb/Ld/LdLkpFormatAsm.lean).

Limits: see the head of Cb/Ld/LdLkpAsmIdx.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsmIdx
import Cb.Ld.LdLkpAsmProofs
import Cb.Ld.LdWfIdxProofs
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpAsmI_good : Spec.ldLkpAsmI_good E := by
  intro p _ A Mu C S rc R0 msg hA hMu
  exact idxLift_goodB E C S Unit _ _ Unit Unit _ _ _ _ rc (fun x => rc x.1) (fun _ _ _ wp => wp) _
    (fun x y τ x' h =>
      congrArg rc (ldLkpFmt_pass E A C.E0 (C.Msg × S.Msg) Unit Unit msg x y τ x' h))
    (ldLkpFmt_plain E A C.E0 (C.Msg × S.Msg) Unit Unit msg).copies.copy
    (ldLkpAsm_base E p A Mu C.E0 Unit (C.Msg × S.Msg) Unit R0 msg hA hMu)

theorem ldLkpAsmI_plain : Spec.ldLkpAsmI_plain E := by
  intro A C M msg
  have h := ldLkpFmt_plain E A C.E0 (C.Msg × M) Unit Unit msg
  refine ⟨h.copies, fun w x c ρ => ?_, h.budAll, fun w x => h.free (idxIn C w) x⟩
  show ((((A.baseA C.E0 (C.Msg × M) Unit Unit msg).H.mapW (idxIn C) fun w o =>
        (w.1, (w.2.1, o.2))).strat
      w x c).run ρ).2.2 = w
  rw [Honest.mapW_run]

theorem ldLkpAsmI_idx : Spec.ldLkpAsmI_idx E := fun A C S msg =>
  lift_idxStep S (ldLkpAsmI_plain E A C S.Msg msg)

theorem ldLkpAsmI_passes : Spec.ldLkpAsmI_passes E := fun A C S msg =>
  lift_passes (b := A.baseI C S.Msg msg) S (ldLkpFmt_pass E A C.E0 (C.Msg × S.Msg) Unit Unit msg)

theorem ldLkpAsmI_same : Spec.ldLkpAsmI_same E := fun A C S msg =>
  lift_keepsW S (ldLkpAsmI_plain E A C S.Msg msg)

end
end Cb
