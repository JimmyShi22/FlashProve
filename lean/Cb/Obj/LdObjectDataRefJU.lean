-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefJU.lean: book-keeping for the hypotheses of a holographic IOP: the records of
the reference request and of the object around it with both reductions at once: no clause on a
list, on a fold's bad points or on "two members of one list agree at few seeds"
(Cb/Req1/LdReqJohn.lean, Cb/Obj/LdObjectDataRefJ.lean), and the three clauses on masks (`lay`,
`layT`, `layB`) replaced by the record on places, layouts and data maps (Cb/Ld/LdLayD.lean).

Two records, two statements (`Cb.Spec.ldReqRefJU`, `Cb.Spec.ldObjRefJU_hyp`) and their proofs:
applications. Packaging: all content is in `Cb.ldReqRefLay_data` and in the lemmas under
`Z.HypRefJ`. No assumed theorem beyond the hypotheses of this file's statements.

Its statements are implications between records of hypotheses.
The object's data: the head of Cb/Obj/LdObjectData.lean. The reference request and a request's end
R: the head of Cb/Obj/LdObjectDataRef.lean.
A bound on lists says that every word has at most L codewords within the radius e (`ListAt`,
Cb/Ld/LdRel.lean; for the messages of an oracle message: `OMsg.ListLE`, Cb/Ld/LdSig.lean).

Main names:
  `Q : LdLayQ E`: a parameter (Cb/Ld/LdLayDKit.lean): what the record on masks asks of each layout
    that it names; `Q.Sound`: it gives the layout's laws (`Y.OK t`).
  `LdReqRefDJU Q ..`: Cb/Req1/LdReqJohn.lean's record `LdReqRefDJ`, field for field, but: it has no
    `lay`, `layT`, `layB`; in their place `layD : LdReqRefLayD Q pp R first b L T`.
  `Z.HypRefJU Q ..`: Cb/Obj/LdObjectDataRefJ.lean's record `Z.HypRefJ` (`Z : LdObjZM F E`,
    Cb/Obj/LdObjectDataMix.lean), field for field, with `req` at `LdReqRefDJU`.
  `Spec.ldReqRefJU`: (the characteristic of E is pp) `Q.Sound` → `LdReqRefDJU Q ..` →
    `LdReqRefDJ ..`.
  `Spec.ldObjRefJU_hyp`: (the characteristic of E is p) `Q.Sound` → `Z.HypRefJU Q ..` →
    `Z.HypRefJ ..`.

Limits: all that the heads of Cb/Req1/LdReqJohn.lean, Cb/Obj/LdObjectDataRefJ.lean,
Cb/Ld/LdLayD.lean, Cb/Ld/LdLayDTop.lean list; among it: the model's duty stands, and beside it the
model owes the conditions `LdPend.StepD` inside `LdReqRefLayD` (its steps' honest maps neither read
a pending mask nor drop it); zero-evaders on public coefficients are asked; "fmt" and the numbers
speak of each closing's link's format and list of errors; no splitting; a body's own sendings lay
no masks.
Agreement is still a premise, as in `Z.HypRefJ`: `MCArows` / `MCAat` of codes, in the batch test's
three towers and in each closing of the request.
This file does not say that the records can be met: no instance in this file.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefJ
import Cb.Ld.LdLayDProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record of the reference request: no lists; the hypotheses of `LdReqRefLayD Q ..`
(Cb/Ld/LdLayD.lean) on the request's masks. -/
structure LdReqRefDJU (Q : LdLayQ E) (pp : ℕ) (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : first.IsStdJ ∧ L.ProtoJ pp ∧ T.A.ProtoJ pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  layD   : LdReqRefLayD Q pp R first b L T
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      L.FmtP (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φb ∧
      T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- `Z.toZ`'s hypotheses at the reference request: no lists; the hypotheses of `LdReqRefLayD Q ..`
(Cb/Ld/LdLayD.lean) on the request's masks. -/
structure LdObjZM.HypRefJU (Z : LdObjZM F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
    (Q : LdLayQ E) (p : ℕ) {Kc : Type} (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  /-- which terms are in `Z.R` -/
  wfIs   : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs  : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  reqIs  : Z.R.toLdObjD.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  onIs   : Z.R.onPack = ldRefOn R p₀
  /-- weights-formedness, the seven sendings, the index's folds -/
  wfJ    : V.HypJ p Z.dS
  sOff   : Z.Y.TS.NearS Z.Y.LW Z.Y.LU Z.Y.LO Z.Y.tW Z.Y.tU Z.Y.tO Z.dW Z.dU Z.dO
  sLink  : Z.R.K.P.StdNear Z.Y.SdK Z.Y.LK Z.Y.tK Z.Y.YK Z.Y.ixK Z.dN
  sOn    : Z.Y.TB.NearS Z.Y.LWB Z.Y.LUB Z.Y.LOB Z.Y.tWB Z.Y.tUB Z.Y.tOB Z.dWB Z.dUB Z.dOB
  own₀   : Z.R.toLdObjD.Own3₀
  /-- the request -/
  req    : LdReqRefDJU Q p R core first b Ls T qφ q κ
  places : R.PlacesOK p₀ plR
  pl₁    : Z.R.HypPl₁
  /-- the link's test and the offline test's three: within a third -/
  pK     : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁     : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂     : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃     : Z.R.X.run.Pre3 Z.tw₃ Z.d₃
  /-- the batch test's three: below the Johnson radius -/
  p₁B    : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B    : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B    : Z.R.XB.run.PreJ Z.tw₃B Z.d₃B

end

namespace Spec

def ldReqRefJU : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    ∀ Q : LdLayQ E,
      Q.Sound → LdReqRefDJU Q pp R core first b L T qφ q κ → LdReqRefDJ pp R core first b L T qφ q κ

def ldObjRefJU_hyp : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZM F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    ∀ Q : LdLayQ E, Q.Sound → Z.HypRefJU Q p R core first b Ls T qφ q κ V p₀ plR →
      Z.HypRefJ p R core first b Ls T qφ q κ V p₀ plR

end Spec

theorem ldReqRefJU : Spec.ldReqRefJU := fun F E Kc _ _ _ _ _ pp _ R _ first b L T _ _ _ Q hQ h =>
  have hl := ldReqRefLay_data F E Kc pp R _ first b L T Q hQ h.duty.model
    (ldReqJohn_list E Kc _ _ _ L pp h.std.2.1) (ldReqJohn_body E Kc _ T.A pp h.std.2.2) h.layD
  { duty := h.duty, std := h.std, deg := h.deg, ev := h.ev, tie := h.tie, own := h.own, lay := hl.1,
    layT := hl.2.1, layB := hl.2.2, fmt := h.fmt
    bFirst := h.bFirst, bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

theorem ldObjRefJU_hyp :
    Spec.ldObjRefJU_hyp := fun F E _ _ _ _ _ _ _ _ _ Kc p _ _ _ R core first b Ls T qφ q κ _ _ _ Q hQ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, onIs := h.onIs, wfJ := h.wfJ,
    sOff := h.sOff, sLink := h.sLink, sOn := h.sOn, own₀ := h.own₀
    req := ldReqRefJU F E Kc p R core first b Ls T qφ q κ Q hQ h.req
    places := h.places, pl₁ := h.pl₁, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B,
      p₂B := h.p₂B, p₃B := h.p₃B }

end Cb
