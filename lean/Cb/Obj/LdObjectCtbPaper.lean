-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbPaper.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the object whose closings follow a plan with a splitting (`LdObjPp`,
Cb/Obj/LdObjectPlanPaper.lean).

A definition, theorems. Bookkeeping for the passage to one random oracle. The analogue of
`LdObjP.CtbP`, `ldObjP_ctb` (Cb/Obj/LdObjectCtbParts.lean: the plan without a splitting). Generic.

Main names:
  `front_ctbA`, `front_ctb`: the links of any front (steps without rounds; "many rows into one": one
    drawn seed; "a row on two groups into a row on each": one value said) have countable shapes: as
    annotated links played by the shared part, and as plain links.
  `ldPlanP_ctbA`, `ldPlanP_ctb`: the closing at the plan with a splitting, for a batch and for one
    instance, from: the shapes of its three whole tests, and the rest's.
  `P.CtbPp`: instances; weights-formedness's link (`P.Bw.link`,
    its chain as one `IOR.Link`); the symbols of seven families; the six whole tests' shapes and the
    link's (`P.Kc`); the two rests; the request.
  `ldObjPp_ctbT`: `P.Hyp L`, `P.CtbPp` ⇒ `P.toT.CtbT` (Cb/Obj/LdObjectCtbTerms.lean); so
    `ldObjT_ctb` there applies.

Why `P.Hyp L` stands among the premises of facts on format and countability: the online closing
`P.cZ` is the term with its honest side. That, its honest side forgotten, it is the plan's annotated
chain (`ldObjPp_forget`, Cb/Obj/LdObjectFmtPaper.lean) is an equation between terms; it does not
hold by definition, but is proved from the plan's conditions (`Cb.ldLinPV_std`). So format and
countability of `P.toT` are shown here (format: Cb/Obj/LdObjectFmtPaper.lean) for objects that meet
`P.Hyp L` only. Cb/Ld/LdHonSide.lean proves the equation (`ldHon_forget`), and `P.CtbPp` ⇒
`P.toT.CtbT` (`ldHon_ctbT`), without that premise.

Limits: this file does not say that `P.CtbPp` holds of a value. On a protocol it has one kind of
conclusion, countability (as in `front_ctbA`, `front_ctb`, and, under `P.Hyp L` and `P.CtbPp`,
`ldObjPp_ctbT`); beyond it no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectFmtPaper
import Cb.Obj.LdObjectCtbTerms
import Cb.Obj.LdObjectCtbBat
import Cb.Obj.LdObjectCtbPre

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

omit [Fintype E] in
theorem ctb_frontBat (B : Type) (iB : Fintype B) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent)
    (Z : Evader E B) (St₀ : Type) (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) :
    (Front.batD B iB Sb sl Z St₀ A₀).link.Ctb :=
  ctb_drawR Z.D _ _

theorem ctb_frontSpl (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type) (sl₁ : Slf E St₁ G₁.C.J)
    (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type) (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp))
    (Rs : S.Ent → Prop) (dRs : DecidablePred Rs) :
    (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link.Ctb :=
  ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable E)⟩, trivial⟩

theorem front_ctbA : ∀ {x y : FSt S E₀ Wp Unit} (p : Front x y), (Front.cA true p).CtbA
  | _, _, .nil x => by
      rw [Front.cA_nil]
      exact (ChainA.ctbA_one _).2 (ctbA_lo _ trivial)
  | _, _, .step p z f g m back => by
      rw [Front.cA_step]
      exact (ChainA.ctbA_snoc _ _).2 ⟨front_ctbA p, ctbA_lo _ trivial⟩
  | _, _, .bat B iB Sb sl Z St₀ A₀ p => by
      rw [Front.cA_bat]
      exact (ChainA.ctbA_snoc _ _).2 ⟨front_ctbA p, ctbS_shared (ctb_frontBat B iB Sb sl Z St₀ A₀)⟩
  | _, _, .split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p => by
      rw [Front.cA_split]
      exact (ChainA.ctbA_snoc _ _).2
        ⟨front_ctbA p, ctbS_shared (ctb_frontSpl G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs)⟩

theorem front_ctbF : ∀ {x y : FSt S E₀ Wp Unit} (p : Front x y), (Front.cA true p).forget.Ctb
  | _, _, .nil x => by
      rw [Front.cA_nil, ChainA.forget_one]
      exact (Chain.ctb_one _).2 trivial
  | _, _, .step p z f g m back => by
      rw [Front.cA_step, ChainA.forget_snoc]
      exact (Chain.ctb_snoc _ _).2 ⟨front_ctbF p, trivial⟩
  | _, _, .bat B iB Sb sl Z St₀ A₀ p => by
      rw [Front.cA_bat, ChainA.forget_snoc, Front.md_l]
      exact (Chain.ctb_snoc _ _).2 ⟨front_ctbF p, ctb_frontBat B iB Sb sl Z St₀ A₀⟩
  | _, _, .split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p => by
      rw [Front.cA_split, ChainA.forget_snoc, Front.md_l]
      exact (Chain.ctb_snoc _ _).2
        ⟨front_ctbF p, ctb_frontSpl G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs⟩

theorem front_ctb {x y : FSt S E₀ Wp Unit} (p : Front x y) : (LdTc.frontC p).Ctb := by
  rw [← frontB_forget E S E₀ Wp x y p true]
  exact front_ctbF p

end

section
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)

omit [Nonempty ι] in
theorem ldPlanP_ctbA (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
    (same' : cA'.forget = T.Q'.c) (h1 : CtbSh T.D₁.T.R.shape) (h2 : CtbSh T.D₂.T.R.shape)
    (h3 : CtbSh T.D₃.T.R.shape) (h : cA'.CtbA) :
    (C.cZA (T.QA cA' same') (C.fqP T.fa)).CtbA :=
  chainA_ctb_append _ _ ((ChainA.ctbA_one _).2 trivial)
    (chainA_ctb_append _ _ (front_ctbA T.front)
      (ctbA_consSh T.D₁ _ T.d₁ T.d₁' h1
        (ctbA_consSh T.D₂ _ T.d₂ T.d₂' h2 (ctbA_consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃' h3 h))))

omit [Fintype ι] [Nonempty ι] in
theorem ldPlanP_ctb (h1 : CtbSh T.D₁.T.R.shape) (h2 : CtbSh T.D₂.T.R.shape)
    (h3 : CtbSh T.D₃.T.R.shape) (h : T.Q'.c.Ctb) : T.QF.c.Ctb :=
  chainCtb_append _ _ (front_ctb T.front)
    (ctb_cons T.D₁ _ T.d₁ T.d₁' h1
      (ctb_cons T.D₂ _ T.d₂ T.d₂' h2 (ctb_cons T.D₃ T.Q' T.d₃ T.d₃' h3 h)))

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- What is left to show at an object. -/
structure LdObjPp.CtbPp (P : LdObjPp F E) : Prop where
  inst : Countable P.W.Cf.Xm
  wf   : CtbSh P.Bw.link.R.shape
  nW   : P.W.NW.CtbSy
  nU   : P.W.NU.CtbSy
  nO   : P.W.NO.CtbSy
  t₁   : CtbSh P.TP.D₁.T.R.shape
  t₂   : CtbSh P.TP.D₂.T.R.shape
  t₃   : CtbSh P.TP.D₃.T.R.shape
  rest : P.TP.Q'.c.Ctb
  nK   : P.K.N.CtbSy
  tK   : CtbSh P.Kc.T.R.shape
  req  : P.r.chain.Ctb
  nWB  : P.on.NW.CtbSy
  nUB  : P.on.NU.CtbSy
  nOB  : P.on.NO.CtbSy
  t₁B  : CtbSh P.TB.D₁.T.R.shape
  t₂B  : CtbSh P.TB.D₂.T.R.shape
  t₃B  : CtbSh P.TB.D₃.T.R.shape
  restB : P.cA'.CtbA

theorem ldObjPp_ctbT (P : LdObjPp F E) (L : ℕ) (h : P.Hyp L) (c : P.CtbPp) : P.toT.CtbT :=
  { inst := c.inst, wf := c.wf, nW := c.nW, nU := c.nU, nO := c.nO
    plan := ldPlanP_ctb P.W.O.toC P.p P.TP c.t₁ c.t₂ c.t₃ c.rest
    nK := c.nK, tK := c.tK, req := c.req, nWB := c.nWB, nUB := c.nUB, nOB := c.nOB
    cz := by
      show P.cZ.forget.CtbA
      rw [ldObjPp_forget P L h]
      exact ldPlanP_ctbA P.on.ol.toC P.pB P.TB P.cA' P.same' c.t₁B c.t₂B c.t₃B c.restB }

end
end Cb
