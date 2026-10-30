-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaConvObj.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean): the converses for the object's other four lists: from the whole lists back to the
records. The quoted words say e ≤ κ · v, with e the round's error, a count of values of its verifier
message (`Err`, Iop/Rbr.lean), and v the number of all values of that message.

Theorems: the rules of Cb/Ld/LdKappaKit.lean, Cb/Ld/LdKappaRun.lean, Cb/Ld/LdKappaTow.lean,
Cb/Ld/LdKappaBat.lean, Cb/Ld/LdKappaObj.lean read backwards. Nothing is evaluated. The fifth list, a
request's preamble: Cb/Ld/LdKappaConv.lean. The five lists are the errors of the protocol's
sub-protocols: weights-formedness, the test for linear constraints at one instance, the link, a
request's preamble, the test at N instances. These errors are numbers that are listed: by a link, a
block, a whole test or the object, among others (the data fields `Link.P.err`, `LinkA.err`, `N.err`;
`obj.nums`, Cb/Obj/LdObject.lean): that any of these is sound at the numbers that it lists is no
statement of this file; for the object that tie is `Spec.ldObj_hyp` (Cb/Obj/LdObject.lean), under
`Obj.OK L`, in the sense of `SubsR.HypK` (Hiop/RecBuild.lean), for the test at N instances with a
closing `Spec.ldLinCB_know` (Cb/Ld/LdLinChainB.lean: `KnowB` for the vectors that share the encoded
index and its record (`SameKey P.k0`), on the statements with the condition `(P.j0 on0).on`), for
weights-formedness `Spec.ldWf` (Cb/Ld/LdWf.lean), each under its hypotheses (that condition itself
asks soundness of some of the parts one level down: for these the tie carries soundness, it does not
found it).

Main names:
  `ldKappaConv_lin`, `ldKappaConv_link`, `ldKappaConv_linA`: the three cores: to `KapC`, `KapC`,
    `KapCB`.
  `ldKappaConv_run`, `ldKappaConv_cons`, `ldKappaConv_linC`, `ldKappaConv_linkC`,
    `ldKappaConv_linCA`, `ldKappaConv_consLo`, `ldKappaConv_consSh`: one whole test (to `D.Kap κ`);
    plans; the tests with their closings.
  `ldKappaConv_sum`, `ldKappaConv_towC`, `ldKappaConv_towG`, `ldKappaConv_pre`: the fold; towers (to
    `T.Kap κ`); a test whose whole test is a tower.
  `ldKappaConv_wf`: weights-formedness (to `B.Kap κ`).
  `ldKappaConv_objT`, `ldKappaConv_objP`, `ldKappaConv_objR`: the object, level by level:
    `obj.nums.Below κ` → all premises of `ldKappa_objT`, `ldKappa_objP`, `ldKappa_objR`
    (Cb/Ld/LdKappaObj.lean).

Notation: `KapC` (Cb/Ld/LdKappaKit.lean): the core of the test for linear constraints, of the link:
its numbers; `KapCB` (Cb/Ld/LdKappaBat.lean): the core at N instances: its numbers; `D.Kap`
(Cb/Ld/LdKappaRun.lean): one whole test on a group: its numbers, and its test's list (`test`);
`T.Kap` (Cb/Ld/LdKappaTow.lean): a tower's numbers; `B.Kap` (Cb/Ld/LdKappaBat.lean):
weights-formedness: its numbers, and its blocks' lists.

Limits: this file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaObj
import Cb.Ld.LdKappaConv

set_option autoImplicit false

namespace Iop
open scoped ENNReal
open IOR IOR.ChainA

theorem chainA_errBelow_iff {K : Type} {A B : Joint K} (c : ChainA K A B) (d : A.W) (κ : ℝ≥0∞) :
    Err.Below (c.linkA d).err κ ↔ c.ErrBelowA κ := by
  induction c with
  | one a => rw [linkA_one, errBelowA_one]
  | snoc c a ih =>
      rw [linkA_snoc, errBelowA_snoc, ← ih]
      exact Err.below_app_iff (c.linkA d).err a.err κ

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

section
variable {E ι κ' J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Y]

theorem ldKappaConv_lin (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf : ℕ) (κ : ℝ≥0∞) (h : (P.chain on0 S εf).ErrBelow κ) : P.KapC S εf κ := by
  unfold LdLinP.chain at h
  simp only [errBelow_snoc, errBelow_one] at h
  exact ⟨h.1.1.1.1.1.2.1, h.1.1.1.1.2.1, h.1.1.1.2.1, h.1.1.2.1, h.1.2.1, h.2.1⟩

theorem ldKappaConv_linA (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N : ℕ) (κ : ℝ≥0∞) (h : (P.chainA on0 S εf N).ErrBelowA κ) :
    P.KapCB S εf N κ := by
  unfold LdLinP.chainA at h
  simp only [errBelowA_snoc, errBelowA_one] at h
  exact ⟨h.1.1.1.1.1.2.1, h.1.1.1.1.2.1, h.1.1.1.2.1, h.1.1.2.1, h.1.2.1, h.2.1⟩

theorem ldKappaConv_linC (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf : ℕ) (cZ : Chain Unit P.J6 LdLinP.JT) (d : P.W0) (κ : ℝ≥0∞)
    (h : Err.Below (P.linC on0 S εf cZ d).P.err κ) :
    P.KapC S εf κ ∧ cZ.ErrBelow κ := by
  unfold LdLinP.linC at h
  rw [chain_errBelow_iff, errBelow_append] at h
  exact ⟨ldKappaConv_lin P on0 S εf κ h.1, h.2⟩

theorem ldKappaConv_linCA (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N : ℕ) (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0) (κ : ℝ≥0∞)
    (h : Err.Below (P.linCA on0 S εf N cZ d).err κ) :
    P.KapCB S εf N κ ∧ cZ.ErrBelowA κ := by
  unfold LdLinP.linCA at h
  rw [chainA_errBelow_iff, errBelowA_append] at h
  exact ⟨ldKappaConv_linA P on0 S εf N κ h.1, h.2⟩

omit [Fintype E] [Nonempty ι] in
theorem ldKappaConv_linZ (C : LdLinC E ι κ' J Y) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St)
    (κ : ℝ≥0∞) (h : (C.cZ Q fq).ErrBelow κ) : Q.c.ErrBelow κ :=
  ((errBelow_append Unit _ _ _ _ _ κ).1 h).2

omit [Fintype E] [Nonempty ι] in
theorem ldKappaConv_linZA (C : LdLinC E ι κ' J Y) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
    (κ : ℝ≥0∞) (h : (C.cZA QA fq).ErrBelowA κ) : QA.cA.ErrBelowA κ :=
  ((errBelowA_append _ _ κ).1 h).2

end

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E}

theorem ldKappaConv_run (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
    (κ : ℝ≥0∞) (h : Err.Below (D.link A₀ d d').P.err κ) : D.Kap κ := by
  have h1 := (Err.below_app_iff (ldBridgeN D.G D.kp D.Sb D.Z St₀ E₀ Unit (D.L * D.Z.err)).err
    ((D.T.N.beside Unit (LdCarX D.kp St₀) (LdCarE D.kp E₀)).seq (IOR.Nums.pure Unit _ _)).err κ).1 h
  exact ⟨h1.1.1,
    ((Err.below_app_iff (D.T.N.beside Unit (LdCarX D.kp St₀) (LdCarE D.kp E₀)).err _ κ).1 h1.2).1⟩

theorem ldKappaConv_cons {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S) (Q : LdTc (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞) (h : (LdTc.cons D Q d d').c.ErrBelow κ) :
    D.Kap κ ∧ Q.c.ErrBelow κ :=
  ⟨ldKappaConv_run D Q.base d d' κ
      ((errBelow_one _ κ).1 ((errBelow_append Unit _ _ _ _ _ κ).1 h).1),
    ((errBelow_append Unit _ _ _ _ _ κ).1 h).2⟩

theorem ldKappaConv_consLo {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞)
    (h : (LdTcA.consLo D QA d d').cA.ErrBelowA κ) : D.Kap κ ∧ QA.cA.ErrBelowA κ :=
  ⟨ldKappaConv_run D QA.Q.base d d' κ ((errBelowA_one _ κ).1 ((errBelowA_append _ _ κ).1 h).1),
    ((errBelowA_append _ _ κ).1 h).2⟩

theorem ldKappaConv_consSh {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞)
    (h : (LdTcA.consSh D QA d d').cA.ErrBelowA κ) : D.Kap κ ∧ QA.cA.ErrBelowA κ :=
  ⟨ldKappaConv_run D QA.Q.base d d' κ ((errBelowA_one _ κ).1 ((errBelowA_append _ _ κ).1 h).1),
    ((errBelowA_append _ _ κ).1 h).2⟩

end

section
variable {E ι κ' J Λ : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Λ]

theorem ldKappaConv_link (P : LdLkP E ι κ' J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (ε₀ ε₁ : ℕ) (κ : ℝ≥0∞) (h : (P.coreC on0 on1 S ε₀ ε₁).ErrBelow κ) :
    P.KapC S ε₀ ε₁ κ := by
  unfold LdLkP.coreC at h
  simp only [errBelow_snoc, errBelow_one] at h
  exact ⟨h.1.1.1.1, h.1.1.2.1, h.1.2.1, h.2.1⟩

theorem ldKappaConv_linkC (P : LdLkP E ι κ' J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (ε₀ ε₁ : ℕ) (K : P.Cl) (d₂ : P.W2) (d : P.W0) (κ : ℝ≥0∞)
    (h : Err.Below (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d₂) d).P.err κ) :
    P.KapC S ε₀ ε₁ κ ∧ K.run.Kap κ := by
  unfold LdLkP.linkC at h
  rw [chain_errBelow_iff, errBelow_append] at h
  exact ⟨ldKappaConv_link P on0 on1 S ε₀ ε₁ κ h.1,
    (ldKappaConv_cons K.run _ _ _ κ ((errBelow_append Unit _ _ _ _ _ κ).1 h.2).2).1⟩

end

section
variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
theorem sErr_below_conv {Ch : Type} [Fintype Ch] [Nonempty Ch] (n : ℕ) (κ : ℝ≥0∞) :
    ∀ (k : ℕ) (f : ℕ → ℕ), Err.Below (sErr (E := E) (Ch := Ch) n k f) κ →
      ∀ i, i < k → (f i : ℝ≥0∞) ≤ κ * (Fintype.card Ch : ℝ≥0∞)
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ + 1, _, h, 0, _ => h.1
  | k + 1, f, h, i + 1, hi =>
    sErr_below_conv n κ k (fun j => f (j + 1)) h.2 i (Nat.lt_of_succ_lt_succ hi)

omit [Fintype E] in
theorem ldKappaConv_sum {P : Type} [Fintype P] (Y : SumPar E P) (Lst mC mS mW : ℕ → ℕ) (κ : ℝ≥0∞)
    (h : Err.Below (Y.err Lst mC mS mW) κ) : Y.Kap Lst mC mS mW κ :=
  ⟨h.1, sErr_below_conv Y.n κ Y.k _ h.2⟩

theorem ldKappaConv_step {a : LdJoint E} {P' StM : Type} [Fintype P'] [Nonempty P']
    (D : LdSw E a.P P' StM) (F : LdBlock a (D.jIn a.e)) (e' L : ℕ) (rest : LdTower (D.jOut e'))
    (κ : ℝ≥0∞) (h : Err.Below (LdTower.step a D F e' L rest).toEnd.N.err κ) :
    Err.Below F.N.err κ ∧
    Err.Below (ldSwBlock D a.e e' L rest.q).N.err κ ∧
    Err.Below rest.toEnd.N.err κ := by
  have h1 :=
    (Err.below_app_iff (Err.app F.N.err (ldSwBlock D a.e e' L rest.q).N.err) rest.toEnd.N.err κ).1 h
  have h2 := (Err.below_app_iff F.N.err (ldSwBlock D a.e e' L rest.q).N.err κ).1 h1.1
  exact ⟨h2.1, h2.2, h1.2⟩

theorem ldKappaConv_towC (κ : ℝ≥0∞) :
    ∀ {a : LdJoint E} (T : LdTowC a), Err.Below T.toEnd.N.err κ → T.Kap κ := by
  intro a T
  induction T with
  | base a t cov d bad L2 => exact fun h => ⟨h.1, h.2.1⟩
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := ldKappaConv_step
      (a := ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e) (S.D e)
      (ldSumAfter Y e S.ts Lst mC mS mW sl ((Y.reform sl).ext d)) e' L rest.toTower κ h
    exact ⟨ldKappaConv_sum (Y.reform sl) Lst mC mS mW κ h1, ⟨h2.1, h2.2.1⟩, ih h3⟩

theorem ldKappaConv_towG {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
    {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} (κ : ℝ≥0∞)
    (T : LdTowG G Sb sl Z) (h : Err.Below T.toEnd.N.err κ) : T.Kap κ := by
  cases T with
  | plain T => exact ldKappaConv_towC κ T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h1, h2, h3⟩ := ldKappaConv_step (a := G.joint Sb sl Z) (Sw.D G.e)
      (Sh.block Sb sl Z d Sw.ts Lst mC mS mW) e' L rest.toTower κ h
    exact ⟨ldKappaConv_sum (Sh.fold Sb sl Z) Lst mC mS mW κ h1,
      ⟨h2.1, h2.2.1⟩,
      ldKappaConv_towC κ rest h3⟩

theorem ldKappaConv_pre {S : Sig E} (D : LdRunD S) (T : LdTowG D.G D.Sb D.sl D.Z) (κ : ℝ≥0∞)
    (e : D.T = T.toEnd) (h : D.Kap κ) :
    ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞) ∧ T.Kap κ :=
  ⟨h.bridge, ldKappaConv_towG κ T (by have := h.test; rw [e] at this; exact this)⟩

end

theorem ldKappaConv_fam {K : Type} (J : ℕ → Joint K)
    (b : ∀ l, Link K (J l) (J (l + 1))) (κ : ℝ≥0∞) :
    ∀ n, (Chain.fam J b n).ErrBelow κ → ∀ l, l ≤ n → Err.Below (b l).P.err κ
  | 0, h, l, hl => by
      obtain rfl := Nat.le_zero.1 hl
      exact (errBelow_one _ κ).1 h
  | n + 1, h, l, hl => by
      rcases Nat.lt_or_ge l (n + 1) with h' | h'
      · exact ldKappaConv_fam J b κ n ((errBelow_snoc _ _ κ).1 h).1 l (Nat.le_of_lt_succ h')
      · obtain rfl := Nat.le_antisymm hl h'
        exact ((errBelow_snoc _ _ κ).1 h).2

theorem ldKappaConv_wf {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (B : P.Blk)
    (κ : ℝ≥0∞) (h : Err.Below B.link.P.err κ) : B.Kap κ := by
  unfold LdWfP.Blk.link at h
  rw [chain_errBelow_iff] at h
  unfold LdWfP.Blk.chain LdWfP.Blk.cLkp at h
  rw [errBelow_snoc, errBelow_append, errBelow_one] at h
  exact ⟨h.1.1.1, ldKappaConv_fam P.J B.lLkp κ P.n h.1.2, h.2⟩

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem errBelowA_to_eq {K : Type} {A B : Joint K} {c c' : ChainA K A B} (e : c = c')
    (κ : ℝ≥0∞) (h : c.ErrBelowA κ) : c'.ErrBelowA κ := e ▸ h

theorem ldKappaConv_objT (T : LdObjT F E) (κ : ℝ≥0∞) (h : T.obj.nums.Below κ) :
    T.Bw.Kap κ ∧ T.W.O.toC.P.KapC T.Sn T.εf κ ∧ T.Qt.c.ErrBelow κ ∧
    T.K.P.KapC T.Sl T.ε₀ T.ε₁ κ ∧ T.Kc.run.Kap κ ∧ T.r.Below κ ∧
    T.on.ol.toC.P.KapCB T.SnB T.εfB T.N κ ∧ T.cZ.forget.ErrBelowA κ := by
  obtain ⟨l1, l2⟩ :=
    ldKappaConv_linC T.W.O.toC.P T.W.O.on0 T.Sn T.εf (T.W.O.toC.cZ T.Qt T.fq) T.dT κ h.linOff
  obtain ⟨k1, k2⟩ := ldKappaConv_linkC T.K.P T.on0K T.on1K T.Sl T.ε₀ T.ε₁ T.Kc T.dK₂ T.dK κ h.link
  have hb : Err.Below (T.on.ol.termV T.onB T.SnB T.qaB T.εfB T.N T.cZ T.dB T.dB₀).a.err κ := h.linOn
  rw [(ldOnT_same F E T.on.ol T.onB T.SnB T.qaB T.εfB T.N T.VT T.cZ T.dB T.dB₀).1] at hb
  obtain ⟨b1, b2⟩ := ldKappaConv_linCA T.on.ol.toC.P T.onB T.SnB T.εfB T.N T.cZ.forget T.dB κ hb
  exact ⟨ldKappaConv_wf T.Bw κ h.wf, l1, ldKappaConv_linZ T.W.O.toC T.Qt T.fq κ l2, k1, k2,
    (ldReq_below_iff _ _ T.r T.w₀ κ).1 h.req, b1, b2⟩

theorem ldKappaConv_objP (P : LdObjP F E) (κ : ℝ≥0∞) (h : P.toT.obj.nums.Below κ) :
    P.Bw.Kap κ ∧ P.W.O.toC.P.KapC P.Sn P.εf κ ∧ P.TP.D₁.Kap κ ∧ P.TP.D₂.Kap κ ∧
    P.TP.Q'.c.ErrBelow κ ∧ P.K.P.KapC P.Sl P.ε₀ P.ε₁ κ ∧ P.Kc.run.Kap κ ∧ P.r.Below κ ∧
    P.on.ol.toC.P.KapCB P.SnB P.εfB P.N κ ∧ P.TB.D₁.Kap κ ∧ P.TB.D₂.Kap κ ∧ P.cA'.ErrBelowA κ := by
  obtain ⟨hW, hL, hQ, hK, hKc, hR, hB, hZ⟩ := ldKappaConv_objT P.toT κ h
  obtain ⟨q1, q'⟩ := ldKappaConv_cons P.TP.D₁ _ _ _ κ hQ
  obtain ⟨q2, q3⟩ := ldKappaConv_cons P.TP.D₂ _ _ _ κ q'
  have e := (ldLinV_cZ_same E _ _ _ _ P.on.ol.toC P.N (P.TB.QA P.cA' P.same') P.TB.fq
    (P.on.ol.toC.P.V6 P.SnB P.qaB P.N) (P.TB.tie₀ P.tie') (P.TB.qB₀ P.N P.q₀B P.bB')
    (P.TB.QV P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.x₀ P.QV')).1
  have z1 :=
    ldKappaConv_linZA P.on.ol.toC (P.TB.QA P.cA' P.same') P.TB.fq κ (errBelowA_to_eq e κ hZ)
  obtain ⟨b1, b'⟩ := ldKappaConv_consSh P.TB.D₁ _ _ _ κ z1
  obtain ⟨b2, b3⟩ := ldKappaConv_consLo P.TB.D₂ ⟨P.TB.Q', P.cA', P.same'⟩ _ _ κ b'
  exact ⟨hW, hL, q1, q2, q3, hK, hKc, hR, hB, b1, b2, b3⟩

theorem ldKappaConv_objR (R : LdObjR F E) (κ : ℝ≥0∞) (h : R.toP.toT.obj.nums.Below κ) :
    R.Bw.Kap κ ∧ R.W.O.toC.P.KapC R.Sn R.εf κ ∧ R.TP₀.D₁.Kap κ ∧ R.TP₀.D₂.Kap κ ∧ R.X.run.Kap κ ∧
    R.K.P.KapC R.Sl R.ε₀ R.ε₁ κ ∧ R.Kc.run.Kap κ ∧ R.r.Below κ ∧
    R.on.ol.toC.P.KapCB R.SnB R.εfB R.N κ ∧ R.TB₀.D₁.Kap κ ∧ R.TB₀.D₂.Kap κ ∧ R.XB.run.Kap κ := by
  obtain ⟨hW, hL, h1, h2, h3, hK, hKc, hR, hB, b1, b2, b3⟩ := ldKappaConv_objP R.toP κ h
  exact ⟨hW, hL, h1, h2, (ldKappaConv_cons R.X.run _ _ _ κ h3).1, hK, hKc, hR, hB, b1, b2,
    (ldKappaConv_consLo R.XB.run _ _ _ κ b3).1⟩

end
end Cb
