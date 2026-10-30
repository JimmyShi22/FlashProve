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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinalPp.lean: conditions over p = 2^64 - 2^32 + 1 (on codes, radii,
sendings, places, the request's record and more: Main names), as one structure, for the protocol
object whose test for linear constraints follows a plan with one splitting (`LdLinPp`,
Cb/Ld/LdLinClosePlanP.lean); the generic hypotheses on that object follow under the hypothesis
`Cb.BCHKS46At F E` on mutual correlated agreement.

Exactly: over p: the conditions with the object at the plan of a write-up
of ours (lean/CREDITS.md) for the linear test (one splitting in the shared part; whole
tests on four kinds of
group) (by a reading).

A record, one statement (`Cb.Gl.Spec.glAt_finalPpHyp`) and its proof. The analogue of `Gl.Final`
(Cb/Gl/GlFinal.lean: the plan without a splitting).

Main names:
  `Gl.FinalPp X V p₀ plR a k msg r e mca`: X : LdFinPp F E (Cb/Obj/LdObjectPpFin.lean).
    The clauses that know no plan are `Gl.Final`'s, with the fields of `LdFinPp` for those of
    `LdFinJ` (X.Z.R.Y for X.Z.Y; X.Z.δ.dS .. for X.Z.dS ..); among them the request (`ReqRefGlU`:
    the hypotheses of `LdReqRefLayD LayGl ..` (Cb/Ld/LdLayD.lean) on the request's masks).
    The plan: onIs, places, pl₁ (Cb/Obj/LdObjectPpRefPlan.lean); tK, t₁ .. t₄: `RunGlAt` (within a
    third); t₁B .. t₄B: `RunGlJAt` (below the Johnson radius; the three codes of each fold and the
    last code `GlJ`: Cb/Gl/GlLdJ.lean, Cb/Gl/GlCopy.lean): nine tests for seven.
  `Spec.glAt_finalPpHyp`: BCHKS46At F E → Gl.FinalPp X .. → X.Z.HypRefPJU LayGl p ..
    (Cb/Obj/LdObjectPpData.lean).

The statement on codes (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean) enters at five clauses: the
session's four tests and the request's closings.

Limits: this file does not say that `Gl.FinalPp` can be met: not here. Declared differences (not a
complete list): those of the heads of Cb/Obj/LdObjectPpData.lean, Cb/Gl/GlFinal.lean, but for "the
linear test's plan without a splitting".

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlFinalAt
import Cb.Obj.LdObjectPpFin

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

/-- The object at the write-up's plan, at the reference request, at this field: the
conditions.
-/
structure FinalPp (X : LdFinPp F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] {Fp : Type}
    [Field Fp] [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPp X.R.O.d.ol.toC)
    (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ) : Prop where
  /-- which terms stand in the object -/
  wfIs    : (⟨X.Z.R.W, X.Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨X.Z.Zw.W, X.Z.Zw.G.B⟩
  sndIs   : X.Z.R.toLdObjD = X.Z.R.toLdObjD.std X.Z.R.Y
  reqIs   : X.Z.R.toLdObjD.pack =
    ldRefPack X.R X.core X.first X.first.tgt (.nil X.first.tgt)
      (LdProg.all_nilK _ _) X.c X.Ls X.T X.qφ X.q
  /-- the code of the encoded index: within a third -/
  code    : X.Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha      : a ≤ 32
  hk      : k < 2 ^ a
  hp      : msg + r ≤ k + 1
  h3      : 3 * X.Z.Zw.W.Cf.eM < 2 ^ a - k
  smp     : X.Z.Zw.W.Cf.Z.OKOn (Ood.PadInF F)
  model   : X.Z.Zw.W.Cf.ModelOK
  /-- weights-formedness, its sender the standard one -/
  wfStd   : (⟨X.Z.Zw.D, X.Z.Zw.X⟩ : Σ D, X.Z.Zw.K.MaskPl D X.Z.Zw.Rl) =
    ⟨X.Z.Zw.W.P.stdD V.Y V.dat V.w0,
      X.Z.Zw.K.stdX X.Z.Zw.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
  wfBody  : ∀ m, X.Z.Zw.W.P.body m = V.bd (V.Y.dataOf m)
  wfBd    : ∀ b, V.bd (V.dat b) = b
  wfAtL   : ∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)
  wfAtB   : ∀ i, V.nAt (X.Z.Zw.W.P.wAt i) = V.Y.entF (V.pl none i)
  wfNoPad : ∀ n, V.RdW n → V.Y.NoPad n
  wfRest2 : X.Z.Zw.Rest2 p
  wfM     : MsgsGl X.Z.Zw.W.P.S V.Y X.Z.Zw.L X.Z.Zw.t X.Z.δ.dS
  /-- the offline test's three sendings -/
  plS     : X.Z.R.Y.TS.Places
  fW      : X.Z.R.W.O.toC.P.SdW.Fair
  fU      : X.Z.R.W.O.toC.P.SdU.Fair
  fO      : X.Z.R.W.O.toC.P.SdO.Fair
  sW      : MsgsGl X.Z.R.W.O.toC.P.NW X.Z.R.Y.TS.YW X.Z.R.Y.LW X.Z.R.Y.tW X.Z.δ.dW
  sU      : MsgsGl X.Z.R.W.O.toC.P.NU X.Z.R.Y.TS.YU X.Z.R.Y.LU X.Z.R.Y.tU X.Z.δ.dU
  sO      : MsgsGl X.Z.R.W.O.toC.P.NO X.Z.R.Y.TS.YO X.Z.R.Y.LO X.Z.R.Y.tO X.Z.δ.dO
  /-- the link's sending -/
  rdK     : X.Z.R.Y.YK.Reads X.Z.R.Y.ixK fun m => Sum.elim (X.Z.R.K.P.uv₀ m) (X.Z.R.K.P.uv₁ m)
  fK      : X.Z.R.Y.SdK.Fair
  sK      : MsgsGl X.Z.R.K.P.N X.Z.R.Y.YK X.Z.R.Y.LK X.Z.R.Y.tK X.Z.δ.dN
  /-- the batch test's three sendings -/
  plB     : X.Z.R.Y.TB.Places
  fWB     : X.Z.R.on.ol.toC.P.SdW.Fair
  fUB     : X.Z.R.on.ol.toC.P.SdU.Fair
  fOB     : X.Z.R.on.ol.toC.P.SdO.Fair
  sWB     : MsgsGl X.Z.R.on.ol.toC.P.NW X.Z.R.Y.TB.YW X.Z.R.Y.LWB X.Z.R.Y.tWB X.Z.δ.dWB
  sUB     : MsgsGl X.Z.R.on.ol.toC.P.NU X.Z.R.Y.TB.YU X.Z.R.Y.LUB X.Z.R.Y.tUB X.Z.δ.dUB
  sOB     : MsgsGl X.Z.R.on.ol.toC.P.NO X.Z.R.Y.TB.YO X.Z.R.Y.LOB X.Z.R.Y.tOB X.Z.δ.dOB
  /-- the index's folds -/
  own₀    : X.Z.R.toLdObjD.Own3₀
  /-- the request -/
  req     : ReqRefGlU p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ
  /-- the plan -/
  onIs    : X.Z.R.onPack = ldRefOnP X.R p₀
  places  : X.R.PlacesOKP p₀ plR
  pl₁     : X.Z.R.HypPl₁
  /-- the link's test and the offline test's four: within a third -/
  tK      : RunGlAt X.Z.R.Kc.run X.Z.twK X.Z.dK
  t₁      : RunGlAt X.Z.R.TP₀.D₁ X.Z.tw₁ X.Z.d₁
  t₂      : RunGlAt X.Z.R.TP₀.D₂ X.Z.tw₂ X.Z.d₂
  t₃      : RunGlAt X.Z.R.TP₀.D₃ X.Z.tw₃ X.Z.d₃
  t₄      : RunGlAt X.Z.R.X.run X.Z.tw₄ X.Z.d₄
  /-- the session's four tests: below the Johnson radius -/
  t₁B     : RunGlJAt X.Z.R.TB₀.D₁ X.Z.tw₁B X.Z.d₁B
  t₂B     : RunGlJAt X.Z.R.TB₀.D₂ X.Z.tw₂B X.Z.d₂B
  t₃B     : RunGlJAt X.Z.R.TB₀.D₃ X.Z.tw₃B X.Z.d₃B
  t₄B     : RunGlJAt X.Z.R.XB.run X.Z.tw₄B X.Z.d₄B

/-- The generic record, at this field, under the statement on codes (`Cb.BCHKS46At`) at one field.
(not all hypotheses are named here: see the statement below) -/
def Spec.glAt_finalPpHyp : Prop :=
  Cb.BCHKS46At F E →
  ∀ (X : LdFinPp F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPp X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinalPp X V p₀ plR a k msg r e mca →
    X.Z.HypRefPJU LayGl p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR

theorem glAt_finalPpHyp : Spec.glAt_finalPpHyp := fun H X _ Fp _ _ _ _ _ _ a k msg r e mca h =>
  { core :=
      { wfIs := h.wfIs
        sndIs := h.sndIs
        reqIs := h.reqIs
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
            okU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).1,
            okO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).1, fairW := h.fWB,
            fairU := h.fUB, fairO := h.fOB
            nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).2,
              nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).2,
              nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).2 }
        own₀ := h.own₀
        req := glAt_finalReq H X.Kc p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ h.req }
    onIs := h.onIs
    places := h.places
    pl₁ := h.pl₁
    pK := gl3_runAt _ _ _ h.tK
    p₁ := gl3_runAt _ _ _ h.t₁
    p₂ := gl3_runAt _ _ _ h.t₂
    p₃ := gl3_runAt _ _ _ h.t₃
    p₄ := gl3_runAt _ _ _ h.t₄
    p₁B := glAt_runAt H _ _ _ _ h.t₁B
    p₂B := glAt_runAt H _ _ _ _ h.t₂B
    p₃B := glAt_runAt H _ _ _ _ h.t₃B
    p₄B := glAt_runAt H _ _ _ _ h.t₄B }

end Cb.Gl
