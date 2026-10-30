-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbParts.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the object whose two closings follow a plan without a splitting (`LdObjP`,
Cb/Obj/LdObjectPlan.lean), from facts on its parts and `P.Hyp L`.

Definitions, theorems. Bookkeeping for the passage to one random oracle (`TopC.Ctb`,
Cond/ObjCtb.lean: instances, symbols, positions and plain parts are countable), as
Cb/Obj/LdObjectCtb.lean, which says what `CtbSh` and `CtbS` are.

Main names:
  `ctbS_app`, `ctbS_shared`: annotated shapes: pieces in a row; rounds in which only the shared part
    speaks.
  `a.CtbA`, `c.CtbA`: chains of annotated links.
  `P.CtbP`: instances countable; the shape of the preamble of
    weights-formedness; the symbols as sent of the seven families (three offline, the link's
    (`P.K`), three online); the shapes of the five whole tests on groups; the two rests; all links
    of the request.
  `ldObjP_ctb`: `P.Hyp L` and `P.CtbP` ⇒ `TopC.Ctb P.toT.obj.subs r`.

Limits: on a protocol this file has one kind of conclusion, countability (as in `ldObjP_ctb`, under
`P.Hyp L` and `P.CtbP`); beyond it no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtb
import Cb.Obj.LdObjectPlan
import Cond.ObjCtb

set_option autoImplicit false

namespace Iop

theorem ctbS_app :
    ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t}, CtbS s A → CtbS t B → CtbS (s ++ t) (RoundSplits.app A B)
  | [], _, _, _, _, h => h
  | _ :: _, _, (_, _), _, h, h' => ⟨h.1, ctbS_app h.2 h'⟩

theorem ctbS_shared : ∀ {s : Shape}, CtbSh s → CtbS s (RoundSplits.const (RAnn.ofShared .sh) s)
  | [], _ => trivial
  | _ :: _, h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2, inferInstanceAs (Countable Unit)⟩, ctbS_shared h.2⟩

namespace IOR
variable {K : Type}

def LinkA.CtbA {A B : Joint K} (a : LinkA K A B) : Prop := CtbS a.l.R.shape a.ann

def ChainA.CtbA : {A B : Joint K} → ChainA K A B → Prop
  | _, _, .one a => a.CtbA
  | _, _, .snoc c a => c.CtbA ∧ a.CtbA

theorem ChainA.ctbA_one {A B : Joint K} (a : LinkA K A B) : (ChainA.one a).CtbA ↔ a.CtbA := by
  rw [ChainA.CtbA]
theorem ChainA.ctbA_snoc {A B C : Joint K} (c : ChainA K A B) (a : LinkA K B C) :
    (c.snoc a).CtbA ↔ c.CtbA ∧ a.CtbA := by rw [ChainA.CtbA]

end IOR

open IOR IOR.ChainA

theorem chainA_ctb {K : Type} {A B : Joint K} (c : ChainA K A B) (d : A.W) (h : c.CtbA) :
    (c.linkA d).CtbA := by
  induction c with
  | one a =>
    rw [linkA_one]
    exact (ChainA.ctbA_one a).1 h
  | snoc c a ih =>
    rw [linkA_snoc]
    exact ctbS_app (ih ((ChainA.ctbA_snoc c a).1 h).1) ((ChainA.ctbA_snoc c a).1 h).2

theorem chainA_ctb_append {K : Type} {A B C : Joint K} (c : ChainA K A B) (c' : ChainA K B C)
    (h : c.CtbA) (h' : c'.CtbA) : (c.append c').CtbA := by
  induction c' with
  | one a =>
    rw [append_one]
    exact (ChainA.ctbA_snoc c a).2 ⟨h, (ChainA.ctbA_one a).1 h'⟩
  | snoc c' a ih =>
    rw [append_snoc]
    exact (ChainA.ctbA_snoc _ a).2
      ⟨ih ((ChainA.ctbA_snoc c' a).1 h').1, ((ChainA.ctbA_snoc c' a).1 h').2⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- the core of the test for a batch -/
theorem ldLinCB_ctb (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N : ℕ) (hW : P.NW.CtbSy) (hU : P.NU.CtbSy) (hO : P.NO.CtbSy) :
    (P.chainA on0 S εf N).CtbA := by
  unfold LdLinP.chainA
  rw [ChainA.ctbA_snoc, ChainA.ctbA_snoc, ChainA.ctbA_snoc, ChainA.ctbA_snoc, ChainA.ctbA_snoc,
    ChainA.ctbA_snoc, ChainA.ctbA_one]
  exact ⟨⟨⟨⟨⟨⟨trivial, ctbS_allLocal (ctb_sendFam _ _ _ _ hW)⟩, ctbS_shared (ctb_peek _)⟩,
          ctbS_shared (ctb_sendFam _ _ _ _ hU)⟩,
        ctbS_shared (ctb_peek _)⟩,
      ctbS_shared (ctb_sendFam _ _ _ _ hO)⟩,
    ctbS_shared (ctb_peek _)⟩

omit [Nonempty ι] in
/-- the closing at the plan -/
theorem ldPlan_ctb (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p)
    (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)
    (h1 : CtbSh T.D₁.T.R.shape) (h2 : CtbSh T.D₂.T.R.shape) (h : cA'.CtbA) :
    (C.cZA (T.QA cA' same') T.fq).CtbA :=
  chainA_ctb_append _ _ ((ChainA.ctbA_one _).2 trivial)
    (chainA_ctb_append _ _ ((ChainA.ctbA_one _).2 (ctbS_shared (ctb_run T.D₁ _ T.d₁ T.d₁' h1)))
      (chainA_ctb_append _ _
        ((ChainA.ctbA_one _).2 (ctbS_allLocal (ctb_run T.D₂ _ T.d₂ T.d₂' h2))) h))

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the batch test's term -/
theorem ldOnT_ctb (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
    (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
    (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) {VT : JV N LdLinP.JT}
    (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (d : O.toC.P.W0) (d₀ : O.P.W0) (hW : O.NW.CtbSy)
    (hU : O.NU.CtbSy) (hO : O.NO.CtbSy) (hc : cZ.forget.CtbA) :
    CtbS (O.termT on0 Sn qa εf N cZ d d₀).R.shape (O.termT on0 Sn qa εf N cZ d d₀).A := by
  show (O.toC.P.linCV Sn qa N on0 εf cZ d).a.CtbA
  unfold LdLinP.linCV
  rw [chainV_link, chainV_forget_append, ldLinV_forget]
  exact chainA_ctb _ _ (chainA_ctb_append _ _ (ldLinCB_ctb O.toC.P on0 Sn εf N hW hU hO) hc)

/-- What each part has to show. -/
structure LdObjP.CtbP (P : LdObjP F E) : Prop where
  inst : Countable P.W.Cf.Xm
  wf   : CtbSh P.Bw.link.R.shape
  nW   : P.W.NW.CtbSy
  nU   : P.W.NU.CtbSy
  nO   : P.W.NO.CtbSy
  t₁   : CtbSh P.TP.D₁.T.R.shape
  t₂   : CtbSh P.TP.D₂.T.R.shape
  rest : P.TP.Q'.c.Ctb
  nK   : P.K.N.CtbSy
  tK   : CtbSh P.Kc.T.R.shape
  req  : P.r.chain.Ctb
  nWB  : P.on.NW.CtbSy
  nUB  : P.on.NU.CtbSy
  nOB  : P.on.NO.CtbSy
  t₁B  : CtbSh P.TB.D₁.T.R.shape
  t₂B  : CtbSh P.TB.D₂.T.R.shape
  restB : P.cA'.CtbA

theorem ldObjP_ctb (P : LdObjP F E) (L : ℕ) (r : P.toT.obj.Cf.conf.Rec) (h : P.Hyp L) (c : P.CtbP) :
    TopC.Ctb P.toT.obj.subs r := by
  obtain ⟨-, -, -, hV4, -⟩ :=
    ldLinVL_all E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.x₀ P.y₀ P.QV'
      P.SnB P.qaB P.baB h.r.shared h.r.restB h.r.saysAB h.test₁B h.test₂B h.r.leftV h.r.tieC
      h.r.qaOK h.r.needNA h.r.needNW h.r.needNU h.r.needNO
  have hcZ : P.cZ.forget.CtbA := by
    rw [show P.cZ.forget = _ from hV4]
    exact ldPlan_ctb P.on.ol.toC P.pB P.TB P.cA' P.same' c.t₁B c.t₂B c.restB
  refine ⟨c.inst, inferInstanceAs (Countable (P.W.Cf.Row → F)), ?_, ?_, ?_⟩
  · exact ctbSh_append (s := P.Bw.link.R.shape) c.wf
      (ldOCtb_lin P.W.O P.εf P.Sn P.TP.Q P.TP.fq P.dT c.nW c.nU c.nO
        (ctb_cons P.TP.D₁ _ P.TP.d₁ P.TP.d₁' c.t₁
          (ctb_cons P.TP.D₂ P.TP.Q' P.TP.d₂ P.TP.d₂' c.t₂ c.rest)))
  · exact ldOCtb_link P.K P.on0K P.on1K P.Sl P.ε₀ P.ε₁ P.Kc P.dK₂ P.dK c.nK c.tK
  · exact ctbS_app (s := (P.r.chain.link (ldStartW E P.w₀)).R.shape)
      (ctbS_allLocal (chainCtb_link P.r.chain _ c.req))
      (ldOnT_ctb P.on.ol P.onB P.SnB P.qaB P.εfB P.N P.cZ P.dB P.dB₀ c.nWB c.nUB c.nOB hcZ)

end
end Cb
