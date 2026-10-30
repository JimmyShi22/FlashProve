-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectTermsProofs.lean: the proof of `Spec.ldObjT_ok` (Cb/Obj/LdObjectTerms.lean), and what
follows for the object with the terms that the library builds for its sub-protocols.

The object is one record with a configuration and, over it, the sub-protocols of the proof system,
as five terms.
No axiom beyond Lean's three. No hypothesis beside the premises that are written out and whatever
the arguments hold as proofs: the theorems assume `T.Hyp L`, which, as far as this file shows,
is not shown to be satisfiable (limits: the head of Cb/Obj/LdObjectTerms.lean).

Each clause of `T.obj.OK`, but for `conf` and
`fitsK`, which are clauses of `T.Hyp`, is the theorem of the part that built the term.

Main names:
  `ldObjT_ok`: the object's `OK` from the blocks' own hypotheses (statement and hypotheses:
    Cb/Obj/LdObjectTerms.lean).
  `Spec.ldObjT_hyp`: `T.Hyp L` ⇒ the four parameter lists, whole (`SubsR.Hyp`, Hiop/RecBuild.lean),
    for `T.obj.subs`.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldObjT_ok` or `ldObjT_hyp` can
   be met together. -/
import Cb.Obj.LdObjectTerms

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

def Spec.ldObjT_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (T : LdObjT F E) (L : ℕ), T.Hyp L → T.obj.subs.Hyp T.obj.nums

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldObjT_ok : Spec.ldObjT_ok F E := by
  classical
  intro T L h
  obtain ⟨f1, f2, f3⟩ := LdWfP.link_all h.base.rest.wfLaws h.base.rest.wfHyp
  have hTail := ldOLF_tailFA F E T.W.O T.εf T.Sn T.q₀ T.Bw.t T.Qt T.fq T.dT T.dT₀ h.base.rest.q₀e
    h.base.rest.fold h.base.rest.pyInj h.base.snds.snd h.rows h.plan h.demand
  have hCl := ldLkC_chain _ _ _ _ _ T.K.P T.Kc T.dK₂ T.Sl _
    (T.K.P.coreC T.on0K T.on1K T.Sl T.ε₀ T.ε₁) h.close h.base.rest.bearK
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ hTail
  have hFmt := ldFmt_req E T.Kr _ _ _ _ _ T.r _ _ h.base.rest.rFmt
  have hLB : T.linB.OK :=
    ldOnT_ok F E T.on.ol T.onB T.SnB T.qaB T.εfB T.N T.VT T.cZ T.kT T.dB T.dB₀ T.yB
      h.base.rest.fitsB h.base.rest.foldB h.base.rest.pyInjB h.base.snds.sndB h.base.snds.apartB
      h.base.rest.monoB h.cOk h.cSides h.cKB h.cOkV h.cCoh h.cEnd
  refine { conf := h.base.rest.conf, wf := ?_, lin := ⟨hTail, fun U hU => ?_⟩,
           fitsK := h.base.rest.fitsK, link := ?_, req := ?_, linB := hLB,
           fitOff := ?_, fitOn := ?_ }
  · exact
      { good := LdWfP.link_goodT h.base.rest.wfLaws h.base.rest.wfHyp
        prefx := f1
        passes := f2
        hands := f3
        relB := fun x y w hw => ⟨hw.1, (ldOWf_holds T.W h.base.rest.tie _ _ _ _).1 hw.2⟩
        relRB := fun a m U hU hh => ⟨U, hU, (ldOWf_holds T.W h.base.rest.tie _ _ _ _).2 hh⟩
        onB := fun _ ha => ha }
  · rw [ldOl_card_isLeft]
    exact hU.1
  · exact ldLc_tail T.K.P T.on0K T.on1K T.ε₀ T.ε₁ T.Sl (T.Kc.cZ T.dK₂) T.dK h.base.rest.foldK
      h.base.rest.plInj h.base.snds.sndK hCl.1 hCl.2
  · exact ldOS_okAtS F E T.on.ol T.Kr T.cr T.Wz T.Bz T.piz T.r T.w₀ T.qφ T.linB.qi h.base.rest.rEnd
      h.base.rest.rHyp h.base.rest.rZk hFmt
  · refine ldOWf_fit T.W T.Bw T.linT.Q (fun V => V.card ≤ T.W.O.t) h.base.rest.wfHyp
      h.base.rest.wfBud h.base.rest.wfNeed (fun U V hVU hU => ⟨?_, fun a => ?_⟩) h9
    · exact (Finset.card_le_card (Finset.toLeft_subset_toLeft hVU)).trans hU.1
    · exact (cnt_mono fun x hx => hVU hx).trans (hU.2 a)
  · exact ldOS_fitAt F E T.on.ol T.Kr T.cr T.Wz T.Bz T.piz T.r T.w₀ T.qφ T.linB.qi T.linB.R
      h.base.rest.rHyp hFmt hLB.mono hLB.reads

theorem ldObjT_hyp : Spec.ldObjT_hyp F E := fun T L h => ldObj_hyp F E T.obj L (ldObjT_ok F E T L h)

end
end Cb
