-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpData.lean: assembly of the holographic IOP from its sub-protocols: the object on
data at the plan of a write-up of ours (lean/CREDITS.md) for the linear test (one splitting
in the shared part;
whole tests on four kinds of group), at the reference request: no hypothesis on a list; offline and
the link within a third, the session's four tests below the Johnson radius.

Definitions, statements and proofs: an assembly of Cb/Obj/LdObjectPpCore.lean,
Cb/Obj/LdObjectPpRows.lean, Cb/Obj/LdObjectPpRefPlan.lean, the towers
(Cb/Obj/LdObjectDataThird.lean, Cb/Obj/LdObjectTowerJohn.lean), Cb/Obj/LdObjectCtbPaper.lean.
Generic. No assumed theorem beyond the hypotheses of its statements.
A tower is a whole test on a group, given by recursion: a fold, a code switch, then a tower on the
new code; at the end a base case (the data: `LdTowJ`, on a group `LdTowGJ`,
Cb/Obj/LdObjectTowerJohn.lean). `Pre3` (Cb/Obj/LdObjectTowers.lean) asks, among other clauses,
`Third` of the tower (Cb/Obj/LdObjectTowerThird.lean), which has 3 e < d at each fold and at the
base case, 2 e' < d' at each code switch. `PreJ` asks, among other clauses, `John`, which has every
radius below the Johnson radius (`InJohnson`, Cb/Gen/JohnsonList.lean).
The analogue of `LdObjZM` with `Z.HypRefJ`, `Z.HypRefJU` (Cb/Obj/LdObjectDataMix.lean,
Cb/Obj/LdObjectDataRefJ.lean, ..RefJU.lean: the plan without a splitting).

Main names:
  `LdObjZp F E`: data only, but for the proofs inside its fields' types (among them `LdLinPp.hU`,
    `hO`, in `R`'s plans): `R : LdObjRp` (Cb/Obj/LdObjectPpRows.lean); Zw (weights-formedness); δ:
    the distances of the messages sent; nine towers with their distances: the link's and the offline
    test's four within a third (`Tow3`), the session's four below the Johnson radius (`TowJ`).
  `Z.HypRefPJ` ..:
    core: the nine clauses that know no plan (Cb/Obj/LdObjectPpCore.lean: `D.CoreJ`): which terms
      stand in the object; weights-formedness; the seven standard sendings; the index's folds; the
      request's record `LdReqRefDJ` (agreement is a premise there too: `MCArows` of codes, in each
      closing of the request: `LdFoldD.IsGrpJ`, Cb/Req1/LdReqJohn.lean);
    onIs, places, pl₁: the plan at the end of the request, by places
      (Cb/Obj/LdObjectPpRefPlan.lean); choices of the two plans and numbers; the splitting's mask
      entry is a free entry of Ω's family's layout, what the splitting reads in Ω's family is no pad
      entry;
    pK, p₁ .. p₄: `Pre3`; p₁B .. p₄B: `PreJ` (`MCAat` / `MCArows` in their towers: premises
      on agreement).
  `Z.HypRefPJU` Q ..: the same with the hypotheses of `LdReqRefLayD Q ..` (Cb/Ld/LdLayD.lean) on the
    request's masks (`D.CoreJU` Q).
  `Spec.ldObjZp_hyp`: E of characteristic p (`CharP E p`), `Z.HypRefPJ` .. ⇒ `Z.R.Hyp 1` ∧ "the two
    languages agree" (`∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'`). So
    (`ldObjRp_hyp`, `ldObjPp_hyp`) `Z.R.toPp.toT.Hyp 1`.
  `Spec.ldObjZp_hypU`: E of characteristic p, `Q.Sound`, `Z.HypRefPJU` Q .. ⇒ `Z.HypRefPJ` ..
  `Z.FinZp`, `Spec.ldObjZp_ctb`: E of characteristic p, `Z.HypRefPJ` .., countability on data
    (`Z.FinZp`) ⇒ `Z.R.toPp.CtbPp`.
  `Spec.ldObjZp_runs`: the fourth test in every slot runs in the format's phases.

The session's four tests: D₁ on the group of the fold of the index with the splitting's message; D₂
on Ω's group with that message; D₃ on the instance's group; XB on what the request leaves beside.
The first two are shared by all instances.

Notation: the `1` in `Z.R.Hyp 1`: the argument `L` of `LdObjRp.Hyp`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding); `Rq`: the end of
a request and the test that follows: the data (`LdORE`, Cb/Obj/LdObjectReqEnd.lean); `first`: the
first sending: the data (`LdSendD`, Cb/Req1/LdSegKit.lean); `Ls`: a list of reference segments, up
to the stage `b` (`LdRefL`, Cb/Req1/LdReqRef.lean); `T`: the last segment: the data (`LdRefT`, the
same file); `V`: the standard sender of weights-formedness: the data beside `Z.Zw` (`LdWfE.StdW`,
Cb/Obj/LdObjectDataSnd.lean); `Fp`: a finite field, with `Algebra Fp E`; `p₀`: the plan: the data
(`LdLinPp`, Cb/Ld/LdLinClosePlanP.lean); `plR`: for each row that stays open (`Rq.Bn`: `LdORE`,
Cb/Obj/LdObjectReqEnd.lean), a set of entries; `Spec.ldObjZp_hyp`, `_hypU`, `_ctb` also bind the
instance `[∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]`.

Limits: declared differences (by a reading): those of the heads of Cb/Obj/LdObjectDataRefJ.lean,
Cb/Req1/LdReqJohn.lean (each to the text that its head names) but for the plan: all oracle messages
are words over E. The plan was held against the write-up by reading: its splitting's one
native mask row "in two groups of two lengths" fits `LdLinPp`: a group has its own long positions
and, for each member, its own map from these to the member's positions, so one short word is read by
repetition at two lengths. That two lengths are not forced is wider. Lean's instance's group may
hold more than {Ω, the instance's message, its index-mask message}: wider.
This file does not say that `Z.HypRefPJ` can be met: no instance in this file. It says nothing on
small errors. No theorem of this library states that the hypotheses of `ldObjZp_hyp` can be met
together.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectPpCore
import Cb.Obj.LdObjectPpRefPlan
import Cb.Obj.LdObjectCtbPaper
import Cb.Obj.LdObjectFmtPaper
import Cb.Obj.LdObjectCtbData

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- The object on data at the write-up's plan. -/
structure LdObjZp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  R    : LdObjRp F E
  Zw   : LdWfE F E
  δ    : R.toLdObjD.Dst Zw
  twK  : R.Kc.run.Tow3
  tw₁  : R.TP₀.D₁.Tow3
  tw₂  : R.TP₀.D₂.Tow3
  tw₃  : R.TP₀.D₃.Tow3
  tw₄  : R.X.run.Tow3
  tw₁B : R.TB₀.D₁.TowJ
  tw₂B : R.TB₀.D₂.TowJ
  tw₃B : R.TB₀.D₃.TowJ
  tw₄B : R.XB.run.TowJ
  dK   : ℕ
  d₁   : ℕ
  d₂   : ℕ
  d₃   : ℕ
  d₄   : ℕ
  d₁B  : ℕ
  d₂B  : ℕ
  d₃B  : ℕ
  d₄B  : ℕ

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record at the reference request. -/
structure LdObjZp.HypRefPJ (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p : ℕ)
    {Kc : Type} (Rq : LdORE F E Kc) (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
    (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
    (q : Finset Rq.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop) : Prop where
  core   : Z.R.toLdObjD.CoreJ Z.Zw Z.R.Y Z.δ p Rq core first b Ls T qφ q κ V
  onIs   : Z.R.onPack = ldRefOnP Rq p₀
  places : Rq.PlacesOKP p₀ plR
  pl₁    : Z.R.HypPl₁
  /-- the link's test and the offline test's four: within a third -/
  pK     : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁     : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂     : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃     : Z.R.TP₀.D₃.Pre3 Z.tw₃ Z.d₃
  p₄     : Z.R.X.run.Pre3 Z.tw₄ Z.d₄
  /-- the batch test's four: below the Johnson radius -/
  p₁B    : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B    : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B    : Z.R.TB₀.D₃.PreJ Z.tw₃B Z.d₃B
  p₄B    : Z.R.XB.run.PreJ Z.tw₄B Z.d₄B

/-- The same, with the hypotheses of `LdReqRefLayD Q ..` (Cb/Ld/LdLayD.lean) on the request's
masks. -/
structure LdObjZp.HypRefPJU (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
    (Q : LdLayQ E) (p : ℕ) {Kc : Type} (Rq : LdORE F E Kc)
    (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
    (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
    (q : Finset Rq.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop) : Prop where
  core   : Z.R.toLdObjD.CoreJU Z.Zw Z.R.Y Z.δ Q p Rq core first b Ls T qφ q κ V
  onIs   : Z.R.onPack = ldRefOnP Rq p₀
  places : Rq.PlacesOKP p₀ plR
  pl₁    : Z.R.HypPl₁
  /-- the link's test and the offline test's four: within a third -/
  pK     : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁     : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂     : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃     : Z.R.TP₀.D₃.Pre3 Z.tw₃ Z.d₃
  p₄     : Z.R.X.run.Pre3 Z.tw₄ Z.d₄
  /-- the batch test's four: below the Johnson radius -/
  p₁B    : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B    : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B    : Z.R.TB₀.D₃.PreJ Z.tw₃B Z.d₃B
  p₄B    : Z.R.XB.run.PreJ Z.tw₄B Z.d₄B

/-- Countability: conditions on codes, families, instances; the request's program. -/
structure LdObjZp.FinZp (Z : LdObjZp F E) : Prop where
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
  tK   : Z.R.Kc.run.TowFin (Z.R.Kc.run.up3 Z.twK)
  t₁   : Z.R.TP₀.D₁.TowFin (Z.R.TP₀.D₁.up3 Z.tw₁)
  t₂   : Z.R.TP₀.D₂.TowFin (Z.R.TP₀.D₂.up3 Z.tw₂)
  t₃   : Z.R.TP₀.D₃.TowFin (Z.R.TP₀.D₃.up3 Z.tw₃)
  t₄   : Z.R.X.run.TowFin (Z.R.X.run.up3 Z.tw₄)
  t₁B  : Z.R.TB₀.D₁.TowFin (Z.R.TB₀.D₁.upJ Z.tw₁B)
  t₂B  : Z.R.TB₀.D₂.TowFin (Z.R.TB₀.D₂.upJ Z.tw₂B)
  t₃B  : Z.R.TB₀.D₃.TowFin (Z.R.TB₀.D₃.upJ Z.tw₃B)
  t₄B  : Z.R.XB.run.TowFin (Z.R.XB.run.upJ Z.tw₄B)

end

namespace Spec
section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

def ldObjZp_hyp : Prop :=
  ∀ (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
      (Rq : LdORE F E Kc) (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    Z.HypRefPJ p Rq core first b Ls T qφ q κ V p₀ plR →
    Z.R.Hyp 1 ∧ ∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'

def ldObjZp_hypU : Prop :=
  ∀ (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
      (Rq : LdORE F E Kc) (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    ∀ Q : LdLayQ E, Q.Sound → Z.HypRefPJU Q p Rq core first b Ls T qφ q κ V p₀ plR →
      Z.HypRefPJ p Rq core first b Ls T qφ q κ V p₀ plR

def ldObjZp_ctb : Prop :=
  ∀ (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
      (Rq : LdORE F E Kc) (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    Z.HypRefPJ p Rq core first b Ls T qφ q κ V p₀ plR → Z.FinZp → Z.R.toPp.CtbPp

end

def ldObjZp_runs : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdObjRp F E),
    R.toPp.cA'.Runs .aft .aft

end Spec

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

theorem ldObjZp_hyp : Spec.ldObjZp_hyp F E Fp := by
  intro Kc p _ Z _ Rq core first b Ls T qφ q κ V p₀ plR h
  obtain ⟨c1, c2, c3⟩ :=
    ldObjPpCore F E Fp Kc p Z.R.toLdObjD Z.Zw Z.R.Y Z.δ Rq core first b Ls T qφ q κ V h.core
  exact
    ⟨{ rest0 := h.core.sndIs ▸ c1
       sndOK := c2
       pl := ldRefPlanP_hyp F E Kc Z.R Rq p₀ plR h.onIs h.places h.pl₁
       close := h.pK.ok
       test₁ := h.p₁.ok, test₂ := h.p₂.ok, test₃ := h.p₃.ok, test₄ := h.p₄.ok
       test₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).2,
         test₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).2
       test₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).2, test₄B := (ldTowGJ_run E _ _ Z.tw₄B Z.d₄B h.p₄B).2 }, c3⟩

theorem ldObjZp_hypU :
    Spec.ldObjZp_hypU F E Fp := fun Kc p _ Z _ Rq core first b Ls T qφ q κ V _ _ Q hQ h =>
  { core := ldObjPpCoreU F E Fp Kc p Z.R.toLdObjD Z.Zw Z.R.Y Z.δ Rq core first b
      Ls T qφ q κ V Q hQ h.core
    onIs := h.onIs, places := h.places, pl₁ := h.pl₁, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂,
      p₃ := h.p₃, p₄ := h.p₄, p₁B := h.p₁B, p₂B := h.p₂B, p₃B := h.p₃B, p₄B := h.p₄B }

theorem ldObjZp_ctb : Spec.ldObjZp_ctb F E Fp := fun _ _ _ Z _ _ _ _ _ _ _ _ _ _ _ _ _ h c =>
  { inst := c.inst
    wf := ldObjZ_ctbWf Z.Zw c.sP ⟨Z.R.W, Z.R.Bw⟩ h.core.wfIs
    nW := c.nW, nU := c.nU, nO := c.nO
    t₁ := h.p₁.pre.ctb c.t₁, t₂ := h.p₂.pre.ctb c.t₂, t₃ := h.p₃.pre.ctb c.t₃
    rest := ctb_cons Z.R.X.run _ Z.R.X.d Z.R.X.d' (h.p₄.pre.ctb c.t₄) (ctb_nil _ _ _ _)
    nK := c.nK
    tK := h.pK.pre.ctb c.tK
    req := ctb_req Z.R.r c.req
    nWB := c.nWB, nUB := c.nUB, nOB := c.nOB
    t₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).1.ctb c.t₁B,
      t₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).1.ctb c.t₂B,
      t₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).1.ctb c.t₃B
    restB := ctbA_consLo Z.R.XB.run _ Z.R.XB.d Z.R.XB.d'
      ((ldTowGJ_run E _ _ Z.tw₄B Z.d₄B h.p₄B).1.ctb c.t₄B) (ctbA_tcNil _ _ _ _) }

end

theorem ldObjZp_runs : Spec.ldObjZp_runs := fun _ _ _ _ _ _ _ R =>
  consLo_runs R.XB.run _ R.XB.d R.XB.d' .aft (tcNil_runs _ _ _ _ .aft)

end Cb
