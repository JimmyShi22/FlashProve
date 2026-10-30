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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinalPpP.lean: conditions on the codes, senders, plan and nine
tests of the protocol object over p = 2^64 - 2^32 + 1, as one structure, the request's pack a
parameter (`FinalPp`,
Cb/Gl/GlFinalPp.lean, without its clause "req"); the generic hypotheses on the protocol object
follow under the premise `Gl.AgreeJ` on mutual correlated agreement and the properties `P.Good` of
the request's pack.

Exactly: over p: the conditions on the object at the plan of this protocol's technical report
(lean/CREDITS.md) for the linear test, generic in the request; agreement from the one premise
`Gl.AgreeJ`.

A record, statements (`Cb.Gl.Spec.glAg_finalPP`, `Cb.Gl.Spec.glFinalPP_ofPp`) and proofs.

Main names:
  `Gl.FinalPP Z P Rq V p₀ plR a k msg r e mca`: the clauses are `Gl.FinalPp`'s (Z for X.Z, Rq for
    X.R), but for: reqIs : Z.R.toLdObjD.pack = P; no clause "req".
  `Spec.glAg_finalPP`: `Gl.AgreeJ` (Cb/Gl/GlFinalAg.lean: the one statement on agreement that the
    chain uses, proved nowhere in this library; it follows from BCHKS46At F E: `glAg_ofAt`; whether
    that assumed statement holds is not said) → Gl.FinalPP Z P Rq .. → `P.Good` →
    Z.HypRefPP p P Rq V p₀ plR (Cb/Obj/LdObjectPpDataP.lean).
  `Spec.glFinalPP_ofPp`: Gl.FinalPp X .. ⇒ Gl.FinalPP X.Z (the pack `ldRefPack` ..) X.R ..: the
    request of `ldRefPack` is an instance.

Here `Gl.AgreeJ` enters at four clauses: the session's four tests.

Limits: what an edition of the request (a pack P, such as `ldRefPack`) needs of
`Gl.AgreeJ` for `P.Good` is that edition's. `P.Good` is a bundle of properties of a term: an edition
of the request has to give it from its own record on data.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlFinalPp
import Cb.Gl.GlFinalAg
import Cb.Obj.LdObjectPpDataP

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

/-- The object at the report's plan, at this field, the request a parameter: the conditions. -/
structure FinalPP (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
    (P : LdReqPack F E) {Kc : Type} (Rq : LdORE F E Kc) {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC)
    (plR : Rq.Bn → Rq.S.Ent → Prop) (a k msg r e mca : ℕ) : Prop where
  /-- which terms stand in the object -/
  wfIs    : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs   : Z.R.toLdObjD = Z.R.toLdObjD.std Z.R.Y
  reqIs   : Z.R.toLdObjD.pack = P
  /-- the code of the encoded index: within a third -/
  code    : Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha      : a ≤ 32
  hk      : k < 2 ^ a
  hp      : msg + r ≤ k + 1
  h3      : 3 * Z.Zw.W.Cf.eM < 2 ^ a - k
  smp     : Z.Zw.W.Cf.Z.OKOn (Ood.PadInF F)
  model   : Z.Zw.W.Cf.ModelOK
  /-- weights-formedness, its sender the standard one -/
  wfStd   : (⟨Z.Zw.D, Z.Zw.X⟩ : Σ D, Z.Zw.K.MaskPl D Z.Zw.Rl) = ⟨Z.Zw.W.P.stdD V.Y V.dat V.w0, Z.Zw.K.stdX Z.Zw.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
  wfBody  : ∀ m, Z.Zw.W.P.body m = V.bd (V.Y.dataOf m)
  wfBd    : ∀ b, V.bd (V.dat b) = b
  wfAtL   : ∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)
  wfAtB   : ∀ i, V.nAt (Z.Zw.W.P.wAt i) = V.Y.entF (V.pl none i)
  wfNoPad : ∀ n, V.RdW n → V.Y.NoPad n
  wfRest2 : Z.Zw.Rest2 p
  wfM     : MsgsGl Z.Zw.W.P.S V.Y Z.Zw.L Z.Zw.t Z.δ.dS
  /-- the offline test's three sendings -/
  plS     : Z.R.Y.TS.Places
  fW      : Z.R.W.O.toC.P.SdW.Fair
  fU      : Z.R.W.O.toC.P.SdU.Fair
  fO      : Z.R.W.O.toC.P.SdO.Fair
  sW      : MsgsGl Z.R.W.O.toC.P.NW Z.R.Y.TS.YW Z.R.Y.LW Z.R.Y.tW Z.δ.dW
  sU      : MsgsGl Z.R.W.O.toC.P.NU Z.R.Y.TS.YU Z.R.Y.LU Z.R.Y.tU Z.δ.dU
  sO      : MsgsGl Z.R.W.O.toC.P.NO Z.R.Y.TS.YO Z.R.Y.LO Z.R.Y.tO Z.δ.dO
  /-- the link's sending -/
  rdK     : Z.R.Y.YK.Reads Z.R.Y.ixK fun m => Sum.elim (Z.R.K.P.uv₀ m) (Z.R.K.P.uv₁ m)
  fK      : Z.R.Y.SdK.Fair
  sK      : MsgsGl Z.R.K.P.N Z.R.Y.YK Z.R.Y.LK Z.R.Y.tK Z.δ.dN
  /-- the batch test's three sendings -/
  plB     : Z.R.Y.TB.Places
  fWB     : Z.R.on.ol.toC.P.SdW.Fair
  fUB     : Z.R.on.ol.toC.P.SdU.Fair
  fOB     : Z.R.on.ol.toC.P.SdO.Fair
  sWB     : MsgsGl Z.R.on.ol.toC.P.NW Z.R.Y.TB.YW Z.R.Y.LWB Z.R.Y.tWB Z.δ.dWB
  sUB     : MsgsGl Z.R.on.ol.toC.P.NU Z.R.Y.TB.YU Z.R.Y.LUB Z.R.Y.tUB Z.δ.dUB
  sOB     : MsgsGl Z.R.on.ol.toC.P.NO Z.R.Y.TB.YO Z.R.Y.LOB Z.R.Y.tOB Z.δ.dOB
  /-- the index's folds -/
  own₀    : Z.R.toLdObjD.Own3₀
  /-- the plan -/
  onIs    : Z.R.onPack = ldRefOnP Rq p₀
  places  : Rq.PlacesOKP p₀ plR
  pl₁     : Z.R.HypPl₁
  /-- the link's test and the offline test's four: within a third -/
  tK      : RunGlAt Z.R.Kc.run Z.twK Z.dK
  t₁      : RunGlAt Z.R.TP₀.D₁ Z.tw₁ Z.d₁
  t₂      : RunGlAt Z.R.TP₀.D₂ Z.tw₂ Z.d₂
  t₃      : RunGlAt Z.R.TP₀.D₃ Z.tw₃ Z.d₃
  t₄      : RunGlAt Z.R.X.run Z.tw₄ Z.d₄
  /-- the session's four tests: below the Johnson radius -/
  t₁B     : RunGlJAt Z.R.TB₀.D₁ Z.tw₁B Z.d₁B
  t₂B     : RunGlJAt Z.R.TB₀.D₂ Z.tw₂B Z.d₂B
  t₃B     : RunGlJAt Z.R.TB₀.D₃ Z.tw₃B Z.d₃B
  t₄B     : RunGlJAt Z.R.XB.run Z.tw₄B Z.d₄B

namespace Spec

def glAg_finalPP : Prop :=
  AgreeJ →
  ∀ (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (P : LdReqPack F E) (Kc : Type)
      (Rq : LdORE F E Kc) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinalPP Z P Rq V p₀ plR a k msg r e mca → P.Good → Z.HypRefPP p P Rq V p₀ plR

def glFinalPP_ofPp : Prop :=
  ∀ (X : LdFinPp F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPp X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinalPp X V p₀ plR a k msg r e mca →
    FinalPP X.Z
      (ldRefPack X.R X.core X.first X.first.tgt (.nil X.first.tgt)
        (LdProg.all_nilK _ _) X.c X.Ls X.T X.qφ X.q)
      X.R V p₀ plR a k msg r e mca

end Spec

theorem glAg_finalPP : Spec.glAg_finalPP := fun H Z _ _ _ _ Fp _ _ _ _ _ _ a k msg r e mca h hg =>
  { core :=
      { wfIs := h.wfIs
        sndIs := h.sndIs
        reqIs := h.reqIs
        wfJ :=
          { isStd := h.wfStd, ok := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).1, body := h.wfBody,
            bdDat := h.wfBd, plL := h.wfAtL, plB := h.wfAtB, noPad := h.wfNoPad, rest2 := h.wfRest2
            conf3 := gl3_conf Z.Zw.W.Cf a k msg r e mca h.code h.ha h.hk h.hp h.h3 h.smp h.model
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
        req := hg }
    onIs := h.onIs
    places := h.places
    pl₁ := h.pl₁
    pK := gl3_runAt _ _ _ h.tK
    p₁ := gl3_runAt _ _ _ h.t₁
    p₂ := gl3_runAt _ _ _ h.t₂
    p₃ := gl3_runAt _ _ _ h.t₃
    p₄ := gl3_runAt _ _ _ h.t₄
    p₁B := glAg_runAt H _ _ _ _ h.t₁B
    p₂B := glAg_runAt H _ _ _ _ h.t₂B
    p₃B := glAg_runAt H _ _ _ _ h.t₃B
    p₄B := glAg_runAt H _ _ _ _ h.t₄B }

theorem glFinalPP_ofPp : Spec.glFinalPP_ofPp := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, code := h.code, ha := h.ha, hk := h.hk,
    hp := h.hp, h3 := h.h3, smp := h.smp, model := h.model, wfStd := h.wfStd, wfBody := h.wfBody,
    wfBd := h.wfBd, wfAtL := h.wfAtL, wfAtB := h.wfAtB, wfNoPad := h.wfNoPad, wfRest2 := h.wfRest2,
    wfM := h.wfM, plS := h.plS, fW := h.fW, fU := h.fU, fO := h.fO, sW := h.sW, sU := h.sU,
    sO := h.sO, rdK := h.rdK, fK := h.fK, sK := h.sK, plB := h.plB, fWB := h.fWB, fUB := h.fUB,
    fOB := h.fOB, sWB := h.sWB, sUB := h.sUB, sOB := h.sOB, own₀ := h.own₀, onIs := h.onIs,
    places := h.places, pl₁ := h.pl₁, tK := h.tK, t₁ := h.t₁, t₂ := h.t₂, t₃ := h.t₃, t₄ := h.t₄,
    t₁B := h.t₁B, t₂B := h.t₂B, t₃B := h.t₃B, t₄B := h.t₄B }

end Cb.Gl
