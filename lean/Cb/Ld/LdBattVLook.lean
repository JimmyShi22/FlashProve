-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVLook.lean: the batching of tensor rows with a value shown reads the entries that it
names, and no other; so wide facts on masks of later blocks cross its three moves (each under the
hypotheses of its statement).

Statements and proofs. The analogue of `Spec.psc_core_look`, `Spec.batt_look`,
`Spec.ldSegRef_tn_carry` of Cb/Req1/LdSegRefTenLook.lean. Rules of the framework only; nothing of a
text is rendered here. The batching is the block `B.battV` of Cb/Ld/LdBattV.lean; its three moves
are `X.prog` of Cb/Ld/LdBattVSeg.lean; a wide fact is `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean).
A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type
`Mk`, and a map `put : Mk → Kc → Kc`. (Cb/Req1/LdSegFresh.lean.)

Main names:
  `Spec.pscV_look`: the whole sumcheck for a polynomial summand (rounds of the variables and the
    last round with the values): for two vectors of entries that agree on `O.Rd` (under `Y.OwnOK O`)
    the honest runs have the same transcript and end with the same explicit part.
  `Spec.battV_look`: the same for the batching with a value shown (under `B.OwnOK Rd`); the witness
    is handed on.
  `X.carry2`: under the hypotheses of the next row, with the fact in `base` at `X.m0`: the wide fact
    crosses the block and the last step.
  `Spec.ldBattVSeg_carry`: under `X.Own`, for a finite set Mk of values that is not empty, and if
    the fact is in `base`, a set of facts, at `X.src`: the wide fact crosses the three moves of
    Cb/Ld/LdBattVSeg.lean, if the batching reads only entries of the wide reading that are not own
    (its own masks, the inner entry too, are another block's matter: they are spent).

Limits: this file says nothing on a closed body.
The pending row still reads the inner entry: that entry is spent for zero
knowledge (it has blinded the value shown), but it stays a part of a claim until the last batching;
no wide fact on it crosses.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBattVSegProofs
import Cb.Req1.LdSegRefCarry

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk IOR IOR.Chain

namespace Spec

def pscV_look : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec) (Wt : Type)
      (msg : Wt → Y.J → E) (O : Y.Own),
    Y.OwnOK O →
    ∀ (w w' : Wt) (x : E × Y.St) c (ρ : Rho (Y.psc Ex).shape), (∀ j, O.Rd j → msg w' j = msg w j) →
      (((Y.hon Ex msg).strat w' x c).run ρ).1 = (((Y.hon Ex msg).strat w x c).run ρ).1 ∧
      (((Y.hon Ex msg).strat w' x c).run ρ).2.1 = (((Y.hon Ex msg).strat w x c).run ρ).2.1

/-- If `B.OwnOK Rd`: the batching reads the entries in Rd only, and hands the witness on. -/
def battV_look : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BattVPar E) (Ex : ExtSpec) (Wt : Type)
      (msg : Wt → B.J → E) (Rd : B.J → Prop),
    B.OwnOK Rd →
    ∀ (w w' : Wt) (x : (B.Q → E) × B.St) c (ρ : Rho (B.battV Ex).shape),
      ((∀ j, Rd j → msg w' j = msg w j) →
        (((B.hon Ex msg).strat w' x c).run ρ).1 = (((B.hon Ex msg).strat w x c).run ρ).1 ∧
        (((B.hon Ex msg).strat w' x c).run ρ).2.1 = (((B.hon Ex msg).strat w x c).run ρ).2.1) ∧
      (((B.hon Ex msg).strat w x c).run ρ).2.2 = w

/-- Under the hypotheses below, the wide fact crosses the batching's three moves. -/
def ldBattVSeg_carry : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (base : MaskFact X.src.J.W → Prop)
      (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (own : X.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → X.S.Ent → E),
    X.Own → (∀ n, X.Rd n → Rd n ∧ ¬ own n) → base (X.src.wideFact Rd Rr own Mk val) →
    (X.prog St₁ fz Az).After base ((X.tgt St₁ Az).wideFact Rd Rr own Mk val)

end Spec

open Classical in
theorem pscV_look : Spec.pscV_look := by
  intro E _ _ Y Ex Wt msg O hO w w' x c ρ hm
  have h := psc_blind E Y Ex Wt msg O hO O.Rd Empty Empty.elim (fun _ h => h) (fun i => i.elim) w w' Empty.elim x c ρ (by
    funext j
    show Y.cutAt O.Rd (msg w') j =
      Function.extend (Empty.elim : Empty → Y.J) (Empty.elim : Empty → E) (Y.cutAt O.Rd (msg w)) j
    rw [Function.extend_apply' _ _ _ (by rintro ⟨i, _⟩; exact i.elim)]
    show (if O.Rd j then msg w' j else 0) = if O.Rd j then msg w j else 0
    by_cases hj : O.Rd j
    · rw [if_pos hj, if_pos hj, hm j hj]
    · rw [if_neg hj, if_neg hj])
  exact ⟨h.1, h.2.1⟩

theorem battV_look : Spec.battV_look := by
  intro E _ _ B Ex Wt msg Rd hO w w' x c ρ
  have own := psc_our_own E B.our Rd (battV_own E B Rd hO)
  have r : ∀ v : Wt, ((B.hon Ex msg).strat v x c).run ρ =
      (Tr.app (((IOR.Honest.draw B.Z.D B.nx Ex Wt).strat v x c.1).run (Rho.fst ρ)).1
          (((B.our.par.hon Ex msg).strat v (B.nx x (Rho.fst (s := [drawRound B.Z.D]) ρ).1) c.2).run
            (Rho.snd (s := [drawRound B.Z.D]) ρ)).1,
        (((B.our.par.hon Ex msg).strat v (B.nx x (Rho.fst (s := [drawRound B.Z.D]) ρ).1) c.2).run
          (Rho.snd (s := [drawRound B.Z.D]) ρ)).2) :=
    fun v => Honest.run_seq (IOR.Honest.draw B.Z.D B.nx Ex Wt) (B.our.par.hon Ex msg) v x c ρ
  refine ⟨fun hm => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := pscV_look E B.our.par Ex Wt msg (B.our.own Rd) own w w'
      (B.nx x (Rho.fst (s := [drawRound B.Z.D]) ρ).1) c.2 (Rho.snd (s := [drawRound B.Z.D]) ρ) hm
    rw [r w', r w]
    exact ⟨by rw [h1]; rfl, h2⟩
  · rw [r w]
    exact psc_keeps E B.our.par Ex Wt msg w _ _ _

namespace LdTenVD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenVD E Kc)

/-- Under `hO` (`X.Own`), `hR` (every entry in `X.Rd` is in Rd and not own) and `hb` (the fact is in
`base` at `X.m0`), Mk finite and not empty: the wide fact crosses the block and the last step. -/
theorem carry2 (St₁ : Type) (fz : X.Mid → St₁)
    (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (base : MaskFact X.m0.J.W → Prop)
    (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (own : X.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val : Mk → X.S.Ent → E) (hO : X.Own) (hR : ∀ n, X.Rd n → Rd n ∧ ¬ own n)
    (hb : base (X.m0.wideFact Rd Rr own Mk val)) :
    (X.stepOut St₁ fz Az).After ((LdMv.sub X.m0 X.m1 (.one X.link)).After base)
      ((X.tgt St₁ Az).wideFact Rd Rr own Mk val) := by
  have own' := ldBattVSeg_own E Kc X hO
  have f1 := segWide_lift X.m0 _ _ _ X.m1.A (X.bt.battV X.C.E0)
    (idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1))
    (idxExt X.C fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc) base Rd Rr own Mk val
    (fun μ μ' wp x c ρ al => by
      obtain ⟨l1, l2⟩ := battV_look E X.bt X.C.E0 _
        (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) X.RdJ own' (idxIn X.C (μ, wp))
        (idxIn X.C (μ', wp)) x c ρ
      have l2' := (battV_look E X.bt X.C.E0 _ (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
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
    (sideF X.S fun z => (X.rowsOf z, fz z)) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun z => (X.rowsOf z, fz z)) fun _ w => w.2) (sideB X.S fun _ w => w.2)
    (fun x => ((X.rowsOf x.1, fz x.1), x.2)) (fun _ w => w.2) _ Rd Rr own Mk val (fun _ _ => rfl)
    (fun _ _ _ _ _ => rfl) f1

end LdTenVD

theorem ldBattVSeg_carry : Spec.ldBattVSeg_carry := by
  intro E Kc _ _ X St₁ fz Az base Rd Rr own Mk _ _ val hO hR hb
  unfold LdTenVD.prog
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine X.carry2 St₁ fz Az _ Rd Rr own Mk val hO hR ?_
  exact segWide_keep X.S _ _ _ _ X.C.E0 X.C.E0 X.src.A X.m0.A
    (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)
    (fun x => ((x.1.2.1, (x.1.1, x.1.2.2)), x.2)) (fun _ w => w.2) _ Rd Rr own Mk val
    (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) hb

end Cb
