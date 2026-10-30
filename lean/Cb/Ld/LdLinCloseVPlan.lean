-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseVPlan.lean: a plan of whole tests on groups for a batch, with its honest side; the
closing of the test for linear constraints for a batch, with its honest side.

Definitions, statements (each a `Prop` in `Iop.Spec` or `Cb.Spec`) and proofs (an assembly).
It uses Cb/Ld/LdLinCloseV.lean (one test as a link with the honest side of a batch: in every slot,
or once by the shared part), Cb/Ld/LdBatchBlocksPlan.lean (plans for a batch: annotations and keys)
and Cb/Ld/LdLinChainV.lean (chains of links with the honest side of a batch).

Main names:
  `l.loV N VA tieB qB`, for any link `l`: each slot runs the one-instance prover; the shared witness
    is handed on. (A step without rounds is the case of no round.) `Spec.linkLoV_pv`: it is a piece,
    from the one-instance bundle, "nothing hidden is withheld", "the tie is carried along honest
    runs", and "it bears what follows"; and `qB.Her`.
  `Spec.chainA_coh_append`: the annotations of two chains in a row are coherent (`Coh`) if and only
    if those of both are.
  `LdTcV N QA V`: the honest side of a plan for a batch QA (`LdTcA`, Cb/Ld/LdBatchBlocksPlan.lean),
    from what a batch adds at its first joint (V: shared witness, tie, demand on families of
    positions): what it adds at the trivial statement, a chain of links with honest sides, and the
    proof that its annotated links are QA's.
  `QV.OK`: every link is a piece; the annotations are coherent; the last demand holds of the empty
    family.
  `LdTcV.nil`, `LdTcV.consLo`, `LdTcV.consSh`; `Spec.ldPlanV_nil`, `Spec.ldPlanV_cons_local`,
    `Spec.ldPlanV_cons_shared`: the three rules: each is OK: `nil` if S has no oracle message and
    V's demand holds of the empty family; the two others if `QV.OK`, with the hypotheses of
    Cb/Ld/LdLinCloseV.lean's `ldRunV_local`, `ldRunV_shared` for the test in front.
  `C.cZV QA fq VA tieB qB QV`: the step without rounds in every slot, then the plan.
  `Spec.ldLinV_cZ_same`: its annotated links are those of `C.cZA QA fq`
    (Cb/Ld/LdBatchBlocksPlan.lean); so its links are those of `C.cZ QA.Q fq`.
  `Spec.ldLinV_cZ_ok`: if the step is a piece and the plan is OK, then `C.cZV ..` meets the three
    conditions that the test for linear constraints asks of its closing on the honest side of a
    batch (`ldLinT_all`, Cb/Ld/LdLinBHonTop.lean): it stands behind every chain (`OkFromV`), its
    annotations are coherent, its last demand holds of the empty family.

Limits: no plan is given here: ties and demands on families of positions are hypotheses. This file
says nothing on splitting. It says nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseVProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR

/-- Any link, in every slot, with the honest side of a batch. -/
def Link.loV {K : Type} {A B : Joint K} (l : Link K A B) (N : ℕ) (VA : JV N A)
    (tieB : VA.W0 → B.X → B.E.Str → B.W → Prop) (qB : QFam B.E N) :
    LinkV K N VA (⟨VA.W0, tieB, qB⟩ : JV N B) :=
  ⟨l.lo, l.H.localV VA.W0, budEach l.R N l.P.bud⟩

end IOR

namespace Spec
open IOR

/-- States, under the hypotheses below: any link, in every slot, is a piece. -/
def linkLoV_pv : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B) (N : ℕ) (VA : JV N A)
      (tieB : VA.W0 → B.X → B.E.Str → B.W → Prop) (qB : QFam B.E N),
    l.GoodT → (∀ w x, l.H.Hid w x = ∅) →
    (∀ x y w c ρ, VA.rel x y w → ρ ∉ l.H.Bad →
      tieB w.1 ((l.H.strat w.2 x c).run ρ).2.1
        (l.R.imp y ((l.H.strat w.2 x c).run ρ).1) ((l.H.strat w.2 x c).run ρ).2.2) →
    l.R.BearsV (RoundSplits.allLocal _) (budEach l.R N l.P.bud) VA.q qB → qB.Her → (l.loV N VA tieB qB).PV

def chainA_coh_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : ChainA K A B) (c' : ChainA K B C),
    (c.append c').Coh ↔ c.Coh ∧ c'.Coh

end Spec

open IOR

theorem linkLoV_pv : Spec.linkLoV_pv := fun _ A B l N VA tieB qB g hH htie hB hHer =>
  ⟨pieceV_local _ _ _ _ l.R _ _ VA.W0 l.H A.rels.rel B.rels.rel VA.rel
      (JV.rel (⟨VA.W0, tieB, qB⟩ : JV N B)) l.P.bud N VA.q qB g.isLocal g.acc g.exact hH
      (fun _ _ _ h => h.1) (fun x y w c ρ hR hρ hRo => ⟨hRo, htie x y w c ρ hR hρ⟩) hB,
    hHer⟩

theorem chainA_coh_append : Spec.chainA_coh_append := by
  intro K A B C c c'
  induction c' with
  | one a => rw [ChainA.append_one, ChainA.coh_snoc, ChainA.coh_one]
  | snoc c' a ih => rw [ChainA.append_snoc, ChainA.coh_snoc, ChainA.coh_snoc, ih, and_assoc]

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The honest side of a plan for a batch. -/
structure LdTcV {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (N : ℕ)
    (QA : LdTcA S E₀ Wp) (V : JV N (S.jointCf QA.Q.base)) where
  VT   : JV N ldTrivJ
  cV   : ChainV Unit N V VT
  same : cV.forget = QA.cA

namespace LdTcV
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type} {N : ℕ}

/-- every link is a piece; the annotations are coherent; the last demand holds of the empty
family -/
def OK {QA : LdTcA S E₀ Wp} {V : JV N (S.jointCf QA.Q.base)} (QV : LdTcV N QA V) : Prop :=
  QV.cV.AllPV ∧ QA.cA.Coh ∧ ∀ J, QV.VT.q J fun _ => ∅

/-- Nothing is left. -/
def nil (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp)
    (V : JV N (S.jointCf (LdTcA.nil S E₀ Wp w₀).Q.base)) :
    LdTcV N (LdTcA.nil S E₀ Wp w₀) V where
  VT := ⟨V.W0, fun _ _ _ _ => True, fun _ _ => True⟩
  cV := .one
    (Link.loV ⟨(LdTl.nil S E₀ Wp w₀).R, (LdTl.nil S E₀ Wp w₀).H,
        (LdTl.nil S E₀ Wp w₀).ext, (LdTl.nil S E₀ Wp w₀).N⟩
      N V (fun _ _ _ _ => True) fun _ _ => True)
  same := ChainV.forget_one _

variable [Fintype E]

/-- The test D in every slot, then QV. -/
def consLo (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (VA : JV N (S.jointCf (D.pre QA.Q.base)))
    (tieB : VA.W0 → QA.Q.St × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
      (S.sub D.kp).Wit × Wp → Prop)
    (qB : QFam (E₀.prod (S.sub D.kp).ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩) :
    LdTcV N (LdTcA.consLo D QA d d') VA where
  VT := QV.VT
  cV := (ChainV.one (D.loV QA.Q.base d d' N VA tieB qB)).append QV.cV
  same := (chainV_forget_append
      Unit N _ _ _ _ _ _ (ChainV.one (D.loV QA.Q.base d d' N VA tieB qB)) QV.cV).trans
    (congrArg₂ (fun c c' => ChainA.append c c') (ChainV.forget_one _) QV.same)

/-- The test D once, by the shared part, then QV. -/
def consSh (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (VA : JV N (S.jointCf (D.pre QA.Q.base))) (W0' : Type)
    (tieB : W0' → QA.Q.St × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
      (S.sub D.kp).Wit × Wp → Prop)
    (qB : QFam (E₀.prod (S.sub D.kp).ext) N)
    (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × QA.Q.St) × S.Smp) × (S.Wit × Wp))
    (nx : VA.W0 → W0') (QV : LdTcV N QA ⟨W0', tieB, qB⟩) :
    LdTcV N (LdTcA.consSh D QA d d') VA where
  VT := QV.VT
  cV := (ChainV.one (D.shV QA.Q.base d d' N VA W0' tieB qB rep nx)).append QV.cV
  same := (chainV_forget_append
      Unit N _ _ _ _ _ _ (ChainV.one (D.shV QA.Q.base d d' N VA W0' tieB qB rep nx)) QV.cV).trans
    (congrArg₂ (fun c c' => ChainA.append c c') (ChainV.forget_one _) QV.same)

end LdTcV

/-- The closing of the test for a batch, with its honest side. -/
def LdLinC.cZV {E ι κ J Y : Type} [Field E] [Fintype Y] [Fintype ι] [Fintype κ]
    [Fintype J] (C : LdLinC E ι κ J Y) {N : ℕ} (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
    (VA : JV N C.j6J)
    (tieB : VA.W0 → QA.Q.St × C.S.Smp → (C.E₀.prod C.S.ext).Str → C.S.Wit × C.Wpa → Prop)
    (qB : QFam (C.E₀.prod C.S.ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩) :
    ChainV Unit N VA QV.VT :=
  (ChainV.one ((C.link fq QA.Q.base).loV N VA tieB qB)).append QV.cV

namespace Spec

def ldPlanV_nil : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) [IsEmpty S.O] (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp)
      (N : ℕ) (V : JV N (S.jointCf (LdTcA.nil S E₀ Wp w₀).Q.base)),
    (∀ J, V.q J fun _ => ∅) → (LdTcV.nil S E₀ Wp w₀ V).OK

/-- A test in every slot, then a plan. -/
def ldPlanV_cons_local : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (N : ℕ) (D : LdRunD S)
      (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (VA : JV N (S.jointCf (D.pre QA.Q.base)))
      (tieB : VA.W0 → QA.Q.St × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
        (S.sub D.kp).Wit × Wp → Prop)
      (qB : QFam (E₀.prod (S.sub D.kp).ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩),
    D.OK → QV.OK → (∀ x y w, VA.rel x y w → tieB w.1 (D.outX x) (D.outY y) (D.outW w.2)) →
    (D.link QA.Q.base d d').R.BearsV (RoundSplits.allLocal _)
      (budEach (D.link QA.Q.base d d').R N (D.link QA.Q.base d d').P.bud) VA.q qB →
    qB.Her → (LdTcV.consLo D QA d d' VA tieB qB QV).OK

/-- A test once, by the shared part, then a plan. -/
def ldPlanV_cons_shared : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (N : ℕ) (D : LdRunD S)
      (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (VA : JV N (S.jointCf (D.pre QA.Q.base))) (W0' : Type)
      (tieB : W0' → QA.Q.St × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
        (S.sub D.kp).Wit × Wp → Prop)
      (qB : QFam (E₀.prod (S.sub D.kp).ext) N)
      (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × QA.Q.St) × S.Smp) × (S.Wit × Wp))
      (yrep : VA.W0 → S.ext.Str) (nx : VA.W0 → W0') (_ : E₀.Str) (QV : LdTcV N QA ⟨W0', tieB, qB⟩),
    D.OK → QV.OK →
    (∀ x y w, VA.rel x y w →
      D.G.claims x.1.1 x.2 = D.G.claims (rep w.1).1.1.1 (rep w.1).1.2 ∧
      D.G.wit w.2.1 = D.G.wit (rep w.1).2.1 ∧
      ∀ a : D.G.A, y.2 a.1 = yrep w.1 a.1) →
    (∀ x y w, VA.rel x y w → tieB (nx w.1) (D.outX x) (D.outY y) (D.outW w.2)) →
    (D.link QA.Q.base d d').R.BearsV (RoundSplits.const (RAnn.ofShared .sh) _)
      (budUnion (D.link QA.Q.base d d').R N (D.link QA.Q.base d d').P.bud) VA.q qB →
    qB.Her → (LdTcV.consSh D QA d d' VA W0' tieB qB rep nx QV).OK

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The annotated links of the closing with its honest side are those of the closing for a batch. -/
def ldLinV_cZ_same : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (N : ℕ) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
      (VA : JV N C.j6J)
      (tieB : VA.W0 → QA.Q.St × C.S.Smp → (C.E₀.prod C.S.ext).Str → C.S.Wit × C.Wpa → Prop)
      (qB : QFam (C.E₀.prod C.S.ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩),
    (C.cZV QA fq VA tieB qB QV).forget = C.cZA QA fq ∧
    (C.cZV QA fq VA tieB qB QV).forget.forget = C.cZ QA.Q fq

/-- The three conditions on the honest side of a batch. -/
def ldLinV_cZ_ok : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (N : ℕ) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
      (VA : JV N C.j6J)
      (tieB : VA.W0 → QA.Q.St × C.S.Smp → (C.E₀.prod C.S.ext).Str → C.S.Wit × C.Wpa → Prop)
      (qB : QFam (C.E₀.prod C.S.ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩) (Z : Joint Unit)
      (VZ : JV N Z) (c₀ : ChainV Unit N VZ VA),
    ((C.link fq QA.Q.base).loV N VA tieB qB).PV → QV.OK →
    (C.cZV QA fq VA tieB qB QV).OkFromV c₀ ∧
    (C.cZV QA fq VA tieB qB QV).forget.Coh ∧
    ∀ Jn, QV.VT.q Jn fun _ => ∅

end
end Spec

theorem ldPlanV_nil : Spec.ldPlanV_nil := by
  classical
  intro E _ S _ E₀ Wp w₀ N V hV
  obtain ⟨hT, hS⟩ := ldChain_nil E S E₀ Wp w₀
  have g := (Chain.allT_one _).1 hT
  have s := (Chain.sidesCT_one _ _).1 hS
  refine ⟨(ChainV.allPV_one _).2
      (linkLoV_pv Unit _ _ _ N V (fun _ _ _ _ => True) (fun _ _ => True) g s.noHid
        (fun _ _ _ _ _ _ _ => trivial) ?_ fun _ _ _ _ _ => trivial),
    (ChainA.coh_one _).2
      (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _),
    fun _ => trivial⟩
  intro J ρ Us _
  refine ⟨fun _ => trivial, ?_⟩
  have e : (fun j : J => (LdTl.nil S E₀ Wp w₀).R.need (ρ.slot j.1) (Us j)) =
      fun _ => ∅ := funext fun j => by
    have hU : Us j = ∅ := Finset.eq_empty_of_isEmpty (α := Empty) _
    rw [hU]
    rfl
  exact e ▸ hV J

theorem ldPlanV_cons_local : Spec.ldPlanV_cons_local := by
  intro E _ _ S E₀ Wp N D QA d d' VA tieB qB QV hD hQ htie hB hHer
  refine ⟨(chainV_all_append Unit N _ _ _ _ _ _
        (ChainV.one (D.loV QA.Q.base d d' N VA tieB qB)) QV.cV).2
      ⟨(ChainV.allPV_one _).2
          (ldRunV_local E S D QA.Q.St Wp E₀ QA.Q.base d d' N VA tieB qB hD htie hB hHer),
        hQ.1⟩,
    (chainA_coh_append Unit _ _ _ (ChainA.one (D.linkLo QA.Q.base d d')) QA.cA).2
      ⟨(ChainA.coh_one _).2
          (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _),
        hQ.2.1⟩,
    hQ.2.2⟩

theorem ldPlanV_cons_shared : Spec.ldPlanV_cons_shared := by
  intro E _ _ S E₀ Wp N D QA d d' VA W0' tieB qB rep yrep nx y₀ QV hD hQ hact htie hB hHer
  refine ⟨(chainV_all_append Unit N _ _ _ _ _ _
        (ChainV.one (D.shV QA.Q.base d d' N VA W0' tieB qB rep nx)) QV.cV).2
      ⟨(ChainV.allPV_one _).2
          (ldRunV_shared E S D QA.Q.St Wp E₀ QA.Q.base d d' N VA W0' tieB qB rep yrep nx
            y₀ hD hact htie hB hHer),
        hQ.1⟩,
    (chainA_coh_append Unit _ _ _ (ChainA.one (D.linkSh QA.Q.base d d')) QA.cA).2
      ⟨(ChainA.coh_one _).2 (RoundSplits.const_coherent (fun r => RAnn.ofShared_coherent .sh r) _),
        hQ.2.1⟩,
    hQ.2.2⟩

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Nonempty ι] in
theorem ldLinV_cZ_same : Spec.ldLinV_cZ_same E ι κ J Y := by
  intro C N QA fq VA tieB qB QV
  have h : (C.cZV QA fq VA tieB qB QV).forget = C.cZA QA fq :=
    (chainV_forget_append Unit N _ _ _ _ _ _
        (ChainV.one ((C.link fq QA.Q.base).loV N VA tieB qB)) QV.cV).trans
      (congrArg₂ (fun c c' => ChainA.append c c') (ChainV.forget_one _) QV.same)
  exact ⟨h, by rw [h]; exact ldLinB_cZ_same E ι κ J Y C QA fq⟩

omit [Fintype E] [Nonempty ι] in
theorem ldLinV_cZ_ok : Spec.ldLinV_cZ_ok E ι κ J Y := by
  intro C N QA fq VA tieB qB QV Z VZ c₀ hstep hQ
  refine ⟨chainV_okFrom_of_all Unit N Z _ _ VZ VA QV.VT c₀ _
      ((chainV_all_append Unit N _ _ _ _ _ _
          (ChainV.one ((C.link fq QA.Q.base).loV N VA tieB qB)) QV.cV).2
        ⟨(ChainV.allPV_one _).2 hstep, hQ.1⟩),
    ?_, hQ.2.2⟩
  rw [(ldLinV_cZ_same E ι κ J Y C N QA fq VA tieB qB QV).1]
  exact (chainA_coh_append Unit _ _ _ (ChainA.one (C.link fq QA.Q.base).lo) QA.cA).2
    ⟨(ChainA.coh_one _).2
        (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _),
      hQ.2.1⟩

end
end Cb
