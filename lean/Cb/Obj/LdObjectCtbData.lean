-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbData.lean: countability, needed to code typed oracles into one random oracle:
`Z.R.toP.CtbP` from `Z.Hyp p L` and `Z.FinZ`, for `Z : LdObjZ`.

Definitions, theorems. Bookkeeping for the passage to one random oracle.
Cb/Obj/LdObjectCtbParts.lean requires of the object at the plan seventeen facts (`P.CtbP`; with
`P.Hyp L` they are the premises of `ldObjP_ctb` there), among them the shapes of the preamble of
weights-formedness, of five whole tests on groups and of the two rests. At the record `Z : LdObjZ`
of Cb/Obj/LdObjectData.lean these terms are values: the assembled lookups and the batching; seven
towers. (`CtbSh s`, CompileK/ImplCountable.lean: the positions, symbols and plain parts of every
round of the shape s are countable.)

Main names:
  `Z.FinZ`: what is left, on data and on the request's program: instances are countable; the symbols
    as sent of the eight families (the preamble's; three offline; the link's; three online) are
    countable (`Sig.CtbSy`); in the codes of the seven towers a native symbol has finitely many
    coordinates (`LdTowG.FinT`, Cb/Obj/LdObjectCtbTower.lean); the request's program has `r.Ctb`,
    move by move (Cb/Obj/LdObjectCtbReq.lean): at a sub-protocol or a fold it still asks `CtbSh` of
    shapes (`Chain.Ctb`, `Link.Ctb`, Cb/Obj/LdObjectCtb.lean).
  `ldObjZ_ctbP`: `Z.Hyp p L` and `Z.FinZ` ⇒ `Z.R.toP.CtbP`. Of `Z.Hyp` only its equations are used:
    which blocks of weights-formedness stand in R; each test's whole test is its tower.

Lemmas on `Sig.CtbSy` and `LdCode.FinNS`: `ctbSy_one`, `finNS_grp` (Cb/Obj/LdObjectCtb.lean);
`finNS_reading`, `finNS_il`, `finNS_pair`, `finNS_fam` (Cb/Obj/LdObjectCtbFin.lean).

Limits: on a protocol this file has one kind of conclusion, countability (as in `LdRunD.Pre.ctb`,
`ldObjZ_ctbWf`, `ldObjZ_ctbP`); beyond it no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectData
import Cb.Obj.LdObjectCtbParts
import Cb.Obj.LdObjectCtbTower
import Cb.Obj.LdObjectCtbPre
import Cb.Obj.LdObjectCtbBat
import Cb.Obj.LdObjectCtbReq

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the codes of the tower T on the complex of D's group: a native symbol has finitely many
coordinates -/
def LdRunD.TowFin {S : Sig E} (D : LdRunD S) (T : D.Tow) : Prop := T.FinT

/-- What is left: conditions on codes, families, instances; the request's program. -/
structure LdObjZ.FinZ (Z : LdObjZ F E) : Prop where
  inst : Countable Z.R.W.Cf.Xm
  sP   : Z.Zw.W.P.S.CtbSy
  nW   : Z.R.W.NW.CtbSy
  nU   : Z.R.W.NU.CtbSy
  nO   : Z.R.W.NO.CtbSy
  nK   : Z.R.K.N.CtbSy
  nWB  : Z.R.on.NW.CtbSy
  nUB  : Z.R.on.NU.CtbSy
  nOB  : Z.R.on.NO.CtbSy
  req  : Z.R.r.Ctb
  tK   : Z.R.Kc.run.TowFin Z.twK
  t₁   : Z.R.TP₀.D₁.TowFin Z.tw₁
  t₂   : Z.R.TP₀.D₂.TowFin Z.tw₂
  t₃   : Z.R.X.run.TowFin Z.tw₃
  t₁B  : Z.R.TB₀.D₁.TowFin Z.tw₁B
  t₂B  : Z.R.TB₀.D₂.TowFin Z.tw₂B
  t₃B  : Z.R.XB.run.TowFin Z.tw₃B

/-- a test whose whole test is a tower -/
theorem LdRunD.Pre.ctb {S : Sig E} {D : LdRunD S} {T : D.Tow} (h : D.Pre T) (hT : D.TowFin T) :
    CtbSh D.T.R.shape := by
  rw [h.isT]
  exact ctb_towG T hT

/-- the preamble of weights-formedness, at every pair that is Zw's -/
theorem ldObjZ_ctbWf (Zw : LdWfE F E) (hS : Zw.W.P.S.CtbSy) : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Zw.W, Zw.G.B⟩ → CtbSh x.2.link.R.shape := by
  rintro _ rfl
  exact ldWfCtb_lks Zw.G.B Zw.K rfl hS

/-- Countability: the seventeen facts. -/
theorem ldObjZ_ctbP (Z : LdObjZ F E) (p L : ℕ) (h : Z.Hyp p L) (c : Z.FinZ) : Z.R.toP.CtbP where
  inst := c.inst
  wf := ldObjZ_ctbWf Z.Zw c.sP ⟨Z.R.W, Z.R.Bw⟩ h.wfIs
  nW := c.nW
  nU := c.nU
  nO := c.nO
  t₁ := h.p₁.ctb c.t₁
  t₂ := h.p₂.ctb c.t₂
  rest := ctb_cons Z.R.X.run _ Z.R.X.d Z.R.X.d' (h.p₃.ctb c.t₃) (ctb_nil _ _ _ _)
  nK := c.nK
  tK := h.pK.ctb c.tK
  req := ctb_req Z.R.r c.req
  nWB := c.nWB
  nUB := c.nUB
  nOB := c.nOB
  t₁B := h.p₁B.ctb c.t₁B
  t₂B := h.p₂B.ctb c.t₂B
  restB := ctbA_consLo Z.R.XB.run _ Z.R.XB.d Z.R.XB.d' (h.p₃B.ctb c.t₃B) (ctbA_tcNil _ _ _ _)

end
end Cb
