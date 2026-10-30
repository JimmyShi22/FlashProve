-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefTenLook.lean: under the hypotheses of its statements, the batching of tensor rows
reads the entries that it names, and no other; so wide facts on masks of later blocks cross it, and
the whole closed body.

Statements and proofs. Rules of the framework only; nothing of a text is rendered here.
Names: `LdStage.wideFact`: Cb/Req1/LdSegCarry.lean; `LdProg.After`: Cb/Req1/LdReq.lean;
`Chain.FreshGiven`: Cb/Req1/LdSegFresh.lean.

Main names (Mk is finite and not empty in the statements):
  `Spec.pStrat_tr`: the transcript of a prover given by its messages in closed form does not depend
    on what it ends with.
  `Spec.psc_core_look`: the rounds of the sumcheck for a polynomial summand: for two vectors of
    entries that agree on Rd (`Y.OwnW Rd`) the honest runs have the same transcript and end with
    the same explicit part.
  `Spec.batt_look`: the same for the batching of tensor rows (`B.OwnOK Rd`).
  `Spec.ldSegRef_tn_carry`: under `X.Own`: the wide fact crosses the three moves of
    Cb/Req1/LdSegRefTen.lean, if the batching reads only entries of the wide reading that are not
    own (its own masks are another block's matter: they are spent).
  `Spec.ldSegRefX_out`: under `A.OK pp` (pp the characteristic of E), `A.Ghost κ`, `F.OK pp`,
    `A.Xa.A.MaskOK A.Xa.Dt`, `A.X.Own`, `Nonempty I.C.E0.Str`, and if what each block reads lies in
    the wide reading: a wide fact that is fresh at the entry of the closed body
    (exactly: `W.Pass F base own Mk val`, Cb/Req1/LdSegRefCross.lean: it is in "base"; "quiet"; the
    two senders do not look) and is read by neither late block is fresh after the body. (not all
    hypotheses are named here: see `Spec.ldSegRefX_out`)
Terms: lean/GLOSSARY.md: tensor row, block, body, explicit part, move.
-/
import Cb.Req1.LdSegRefCross
import Cb.Ld.LdPscProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk IOR IOR.Chain

namespace Spec

def pStrat_tr : Prop :=
  ∀ (E : Type) [Field E] (β β' : Type) (l : List (PFmt E)) (d : PDats l)
      (q : HPt (pVars l d) → RIdx (pVars l d) → E) (res : PPt l → β)
      (res' : PPt l → β') (ρ : Rho (pRounds l)),
    ((pStrat l d q res).run ρ).1 = ((pStrat l d q res').run ρ).1

def psc_core_look : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec) (Wt : Type)
      (msg : Wt → Y.J → E) (Rd : Y.J → Prop),
    Y.OwnW Rd →
    ∀ (w w' : Wt) (x : E × Y.St) (ρ : Rho (Y.core Ex).shape), (∀ j, Rd j → msg w' j = msg w j) →
      (((Y.honC Ex msg).strat w' x ()).run ρ).1 = (((Y.honC Ex msg).strat w x ()).run ρ).1 ∧
      (((Y.honC Ex msg).strat w' x ()).run ρ).2.1 = (((Y.honC Ex msg).strat w x ()).run ρ).2.1

/-- States, under `B.OwnOK Rd`: the batching reads the entries in Rd only, and hands the witness
on. -/
def batt_look : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BattPar E) (Ex : ExtSpec) (Wt : Type)
      (msg : Wt → B.J → E) (Rd : B.J → Prop),
    B.OwnOK Rd →
    ∀ (w w' : Wt) (x : (B.Q → E) × B.St) c (ρ : Rho (B.batt Ex).shape),
      ((∀ j, Rd j → msg w' j = msg w j) →
        (((B.hon Ex msg).strat w' x c).run ρ).1 = (((B.hon Ex msg).strat w x c).run ρ).1 ∧
        (((B.hon Ex msg).strat w' x c).run ρ).2.1 = (((B.hon Ex msg).strat w x c).run ρ).2.1) ∧
      (((B.hon Ex msg).strat w x c).run ρ).2.2 = w

/-- States, under the hypotheses below: the wide fact crosses the batching's three moves. -/
def ldSegRef_tn_carry : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (base : MaskFact X.src.J.W → Prop)
      (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (own : X.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → X.S.Ent → E),
    X.Own → (∀ n, X.Rd n → Rd n ∧ ¬ own n) → base (X.src.wideFact Rd Rr own Mk val) →
    (X.prog St₁ fz Az).After base ((X.tgt St₁ Az).wideFact Rd Rr own Mk val)

/-- Fresh after the closed body. (not all hypotheses are named here: see the statement below) -/
def ldSegRefX_out : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc)
      (base : MaskFact A.V.Fp.s0.J.W → Prop) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))),
    A.OK pp → A.Ghost κ → F.OK pp → W.Pass F base own Mk val → A.Xa.A.MaskOK A.Xa.Dt →
    (∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n) → A.X.Own →
    (∀ n, A.Rdt n → W.Rd2 n ∧ ¬ A.own2 own n) →
    (A.body St₁ fz Az).After base
      ((A.X.tgt St₁ Az).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val))

end Spec

theorem pStrat_tr : Spec.pStrat_tr := by
  intro E _ β β' l
  induction l with
  | nil => intro d q res res' ρ; rfl
  | cons f l ih =>
      intro d q res res' ρ
      have e := ih d.2 (fun γ i => q (f.val ρ.1, γ) (.inr i)) (fun γ => res (f.val ρ.1, γ))
        (fun γ => res' (f.val ρ.1, γ)) ρ.2
      show (_, ρ.1,
          ((pStrat l d.2 (fun γ i => q (f.val ρ.1, γ) (.inr i)) fun γ =>
            res (f.val ρ.1, γ)).run ρ.2).1) =
        (_, ρ.1,
          ((pStrat l d.2 (fun γ i => q (f.val ρ.1, γ) (.inr i)) fun γ =>
            res' (f.val ρ.1, γ)).run ρ.2).1)
      rw [e]

theorem psc_core_look : Spec.psc_core_look := by
  intro E _ _ Y Ex Wt msg Rd hO w w' x ρ hm
  have eW : Y.W x.2 (msg w') = Y.W x.2 (msg w) := funext fun i => hm _ (hO.own _)
  have eI : Y.inc x.2 (msg w') = Y.inc x.2 (msg w) := Finset.sum_congr rfl fun j _ => by
    by_cases hj : Rd j
    · rw [hm j hj]
    · rw [hO.rdS _ j hj, zero_mul, zero_mul]
  have eG := hO.rdG x.2 (msg w') (msg w) hm
  have eGb := hO.rdGb x.2 (msg w') (msg w) hm
  have eS : Y.sum x.2 (msg w') = Y.sum x.2 (msg w) := by
    funext X
    unfold PscPar.sum
    rw [eG, eGb]
  have eQ : Y.honQ x.2 (msg w') = Y.honQ x.2 (msg w) := by
    funext ε γ i
    unfold PscPar.honQ
    rw [eW, eI, eS]
  have eM : Y.honMid x.2 (msg w') = Y.honMid x.2 (msg w) := by
    funext ε γ
    unfold PscPar.honMid PscPar.whole
    rw [eW, eI, eS]
  constructor
  · show ((((), hMu (Y.vars x.2) (Y.W x.2 (msg w'))),
        ρ.1,
        ((pStrat Y.fmt (Y.dat x.2) (Y.honQ x.2 (msg w') ρ.1) fun γ =>
            (Y.honMid x.2 (msg w') ρ.1 γ, w')).run
          ρ.2).1) : Tr (Y.core Ex).shape) =
      (((), hMu (Y.vars x.2) (Y.W x.2 (msg w))),
        ρ.1,
        ((pStrat Y.fmt (Y.dat x.2) (Y.honQ x.2 (msg w) ρ.1) fun γ =>
          (Y.honMid x.2 (msg w) ρ.1 γ, w)).run ρ.2).1)
    rw [eW, eQ,
      pStrat_tr E _ _ Y.fmt (Y.dat x.2) (Y.honQ x.2 (msg w) ρ.1)
        (fun γ => (Y.honMid x.2 (msg w') ρ.1 γ, w')) (fun γ => (Y.honMid x.2 (msg w) ρ.1 γ, w)) ρ.2]
  · rw [(psc_run E Y Ex Wt msg w' x ρ).2.2.2, (psc_run E Y Ex Wt msg w x ρ).2.2.2, eM]

theorem batt_look : Spec.batt_look := by
  intro E _ _ B Ex Wt msg Rd hO w w' x c ρ
  have own := batt_own E B Rd hO
  have r : ∀ v : Wt, ((B.hon Ex msg).strat v x c).run ρ =
      (Tr.app (((IOR.Honest.draw B.Z.D B.nx Ex Wt).strat v x c.1).run (Rho.fst ρ)).1
          (((B.par.honC Ex msg).strat v (B.nx x (Rho.fst (s := [drawRound B.Z.D]) ρ).1) ()).run
            (Rho.snd (s := [drawRound B.Z.D]) ρ)).1,
        (((B.par.honC Ex msg).strat v (B.nx x (Rho.fst (s := [drawRound B.Z.D]) ρ).1) ()).run
          (Rho.snd (s := [drawRound B.Z.D]) ρ)).2) :=
    fun v => Honest.run_seq (IOR.Honest.draw B.Z.D B.nx Ex Wt) (B.par.honC Ex msg) v x c ρ
  refine ⟨fun hm => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := psc_core_look E B.par Ex Wt msg Rd own w w'
      (B.nx x (Rho.fst (s := [drawRound B.Z.D]) ρ).1) (Rho.snd (s := [drawRound B.Z.D]) ρ) hm
    rw [r w', r w]
    exact ⟨by rw [h1]; rfl, h2⟩
  · rw [r w, (psc_run E B.par Ex Wt msg w _ _).2.2.2]

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- under `hO`, `hR`, `hb`, Mk not empty: the wide fact crosses the block and the last step -/
theorem carry2 (St₁ : Type) (fz : X.bt.par.Mid → St₁)
    (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (base : MaskFact X.m0.J.W → Prop)
    (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (own : X.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val : Mk → X.S.Ent → E) (hO : X.Own) (hR : ∀ n, X.Rd n → Rd n ∧ ¬ own n)
    (hb : base (X.m0.wideFact Rd Rr own Mk val)) :
    (X.stepOut St₁ fz Az).After ((LdMv.sub X.m0 X.m1 (.one X.link)).After base)
      ((X.tgt St₁ Az).wideFact Rd Rr own Mk val) := by
  have own' := ldSegRef_tn_own E Kc X hO
  have f1 := segWide_lift X.m0 _ _ _ X.m1.A (X.bt.batt X.C.E0)
    (idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1))
    (idxExt X.C fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc) base Rd Rr own Mk val
    (fun μ μ' wp x c ρ al => by
      obtain ⟨l1, l2⟩ := batt_look E X.bt X.C.E0 _ (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
        X.RdJ own' (idxIn X.C (μ, wp)) (idxIn X.C (μ', wp)) x c ρ
      have l2' := (batt_look E X.bt X.C.E0 _ (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
        X.RdJ own' (idxIn X.C (μ', wp)) (idxIn X.C (μ', wp)) x c ρ).2
      obtain ⟨h1, h2⟩ := l1 (by
        rintro (a | n) hj
        · rfl
        · exact al n (hR n hj).1 (hR n hj).2)
      have q : ∀ v : X.S.Msg × (X.C.PIdx × X.Wp),
          ((idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)).strat
              v x c).run ρ = _ :=
        fun v =>
          mapW_run (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) (idxIn X.C)
            (fun w o => (w.1, (w.2.1, o.2))) v x c ρ
      have e3 : (wp.1,
            (((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat
                (idxIn X.C (μ', wp)) x c).run ρ).2.2.2) =
          (wp.1, (((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat
                (idxIn X.C (μ, wp)) x c).run ρ).2.2.2) := by
        rw [l2, l2']
        rfl
      exact ⟨(congrArg Prod.fst (q (μ', wp))).trans (h1.trans (congrArg Prod.fst (q (μ, wp))).symm),
        (congrArg (fun r => r.2.1) (q (μ', wp))).trans
          (h2.trans (congrArg (fun r => r.2.1) (q (μ, wp))).symm),
        (congrArg (fun r => r.2.2.2) (q (μ', wp))).trans (e3.trans (congrArg (fun r => r.2.2.2) (q (μ, wp))).symm)⟩) hb
  exact segWide_keep X.S _ _ _ _ X.C.E0 X.C.E0 X.m1.A (X.tgt St₁ Az).A
    (sideF X.S fun z => ((X.stOf z).1, fz z)) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun z => ((X.stOf z).1, fz z)) fun _ w => w.2) (sideB X.S fun _ w => w.2)
    (fun x => (((X.stOf x.1).1, fz x.1), x.2)) (fun _ w => w.2) _ Rd Rr own Mk val (fun _ _ => rfl)
    (fun _ _ _ _ _ => rfl) f1

end LdTenD

theorem ldSegRef_tn_carry : Spec.ldSegRef_tn_carry := by
  intro E Kc _ _ X St₁ fz Az base Rd Rr own Mk _ _ val hO hR hb
  unfold LdTenD.prog
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine X.carry2 St₁ fz Az _ Rd Rr own Mk val hO hR ?_
  exact segWide_keep X.S _ _ _ _ X.C.E0 X.C.E0 X.src.A X.m0.A
    (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)
    (fun x => ((x.1.2.1, (x.1.1, x.1.2.2)), x.2)) (fun _ w => w.2) _ Rd Rr own Mk val
    (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) hb

theorem ldSegRefX_out : Spec.ldSegRefX_out := by
  intro E Kc _ _ pp _ I A _ W F κ base own Mk _ _ val St₁ fz Az h hG hF hP hM hap hO hR
  have wT := ldSegRefX_tn E Kc pp _ A W F κ base own Mk val h hG hF hP hM hap
  have key : (A.X.prog St₁ fz Az).After
      (A.Y.step.After
        ((A.Xa.Q.prog A.Xa.mult A.Xa.ent A.Xa.A.nRows A.Xa.lk).After
          (A.Xa.Q.D.prog.After (A.V.prog.After base))))
      ((A.X.tgt St₁ Az).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)) := by
    unfold LdTenD.prog
    rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
    exact A.X.carry2 St₁ fz Az _ W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val) hO hR wT
  unfold LdRefD.body LdBodyD.body
  rw [ldProg_app_after, LdProg.after_snoc, ldProg_app_after, ldProg_app_after]
  exact key

end Cb
