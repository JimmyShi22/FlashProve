-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinJProofs.lean: the proofs of the statements of Cb/Gl/GlFinJ.lean
(`Cb.Gl.glFinJ_req`, `Cb.Gl.glFinJ_hyp`).

The proofs are an assembly of Cb/GlVal/GlReqJohnProofs.lean (sendings and closings of the reference
request), Cb/GlVal/GlThird.lean (the configuration), Cb/Gl/GlObjMix.lean (the seven tests). What the
statements say and do not say: the head of Cb/Gl/GlFinJ.lean. BCHKS46F F is a hypothesis by name of
both, no axiom.

Main names:
  `glFinJ_req`: the reference request's generic record (statement and hypotheses:
    Cb/Gl/GlFinJ.lean): BCHKS46F F → ReqRefGl .. → LdReqRefDJ ..
  `glFinJ_hyp`: the object's generic record (statement and hypotheses: Cb/Gl/GlFinJ.lean):
    BCHKS46F F → FinJ X V p₀ plR a k msg r e mca → X.Z.HypRefJ p X.R X.core X.first X.c X.Ls X.T
    X.qφ X.q X.κ V p₀ plR.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlFinJ
import Cb.GlVal.GlReqJohnProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

theorem glFinJ_req : Spec.glFinJ_req := fun H Kc pp _ _ _ _ L T _ _ _ h =>
  { duty := h.duty,
    std := ⟨glReqJohn_send Kc _ _ h.std.1,
        glReqJohn_list H Kc _ _ _ L pp h.std.2.1,
        glReqJohn_body Kc _ T.A pp h.std.2.2⟩,
    deg := h.deg, ev := h.ev, tie := h.tie, own := h.own, lay := h.lay, layT := h.layT,
    layB := h.layB, fmt := h.fmt
    bFirst := h.bFirst, bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

theorem glFinJ_hyp : Spec.glFinJ_hyp := fun H X _ Fp _ _ _ V p₀ plR a k msg r e mca h =>
  { wfIs := h.wfIs
    sndIs := h.sndIs
    reqIs := h.reqIs
    onIs := h.onIs
    wfJ :=
      { isStd := h.wfStd, ok := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).1, body := h.wfBody,
        bdDat := h.wfBd, plL := h.wfAtL, plB := h.wfAtB, noPad := h.wfNoPad, rest2 := h.wfRest2
        conf3 := gl3_conf X.Z.Zw.W.Cf a k msg r e mca h.code h.ha h.hk h.hp h.h3 h.smp h.model
        near := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).2 }
    sOff :=
      { places := h.plS, okW := (glReqJohn_msgs _ _ _ _ _ _ h.sW).1,
        okU := (glReqJohn_msgs _ _ _ _ _ _ h.sU).1, okO := (glReqJohn_msgs _ _ _ _ _ _ h.sO).1,
        fairW := h.fW, fairU := h.fU, fairO := h.fO
        nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sW).2,
          nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sU).2,
          nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sO).2 }
    sLink := { ok := (glReqJohn_msgs _ _ _ _ _ _ h.sK).1, reads := h.rdK, fair := h.fK,
               near := (glReqJohn_msgs _ _ _ _ _ _ h.sK).2 }
    sOn :=
      { places := h.plB, okW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).1,
        okU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).1, okO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).1,
        fairW := h.fWB, fairU := h.fUB, fairO := h.fOB
        nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).2,
          nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).2,
          nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).2 }
    own₀ := h.own₀
    req := glFinJ_req H X.Kc p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ h.req
    places := h.places
    pl₁ := h.pl₁
    pK := gl3_runAt _ _ _ h.tK
    p₁ := gl3_runAt _ _ _ h.t₁
    p₂ := gl3_runAt _ _ _ h.t₂
    p₃ := gl3_runAt _ _ _ h.t₃
    p₁B := glJ_runAt H _ _ _ h.t₁B
    p₂B := glJ_runAt H _ _ _ h.t₂B
    p₃B := glJ_runAt H _ _ _ h.t₃B }

end Cb.Gl
