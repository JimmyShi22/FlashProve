-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskAsm2Proofs.lean: the proofs of the statements of Cb/Ld/LdLkpMaskAsm2.lean (under the
hypotheses of its statements, the assembled lookup, `LkAsm2`, has the item "masked messages" as a
whole). The item: `Honest.MM`, Ior/Masked.lean.

The proof goes as in Cb/Ld/LdLkpMaskAsmProofs.lean and Cb/Ld/LdLkpMaskSegT.lean: each part is a link
(`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean) started with what the honest run of the parts before makes of
the first claim; the claims after the head and after the keys' side come from the parts'
completeness at the joint that asks nothing.

Main names (statements and hypotheses: Cb/Ld/LdLkpMaskAsm2.lean):
  `ldLkpMaskAsm2_link`: see its statement in Cb/Ld/LdLkpMaskAsm2.lean.
  `ldLkpMaskAsm2_mm`: see its statement in Cb/Ld/LdLkpMaskAsm2.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskAsm2
import Cb.Ld.LdLkpMaskAsmProofs
import Cb.Ld.LdLkpAsm2PullProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section Own
variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
theorem PscPar.ownW_mono {Y : PscPar E} {Rd Rd' : Y.J → Prop}
    (hs : ∀ j, Rd j → Rd' j) (h : Y.OwnW Rd) : Y.OwnW Rd' :=
  ⟨h.inj, fun i => hs _ (h.own i), fun st m m' hm => h.rdG st m m' fun j hj => hm j (hs j hj),
    fun st m m' hm => h.rdGb st m m' fun j hj => hm j (hs j hj),
    fun st j hj => h.rdS st j fun hj' => hj (hs j hj'), h.wG, h.wGb, h.wS⟩

namespace LdLkp.LkAsm2
variable (A : LkAsm2 E)

/-- Under `h`: the incoming form of the closing (`A.En`) reads the tie's and the forest's masks
only. -/
theorem inc_supp {Dt : A.J → Prop} (h : A.MaskOK Dt) (st : A.En.par.St)
    (j : A.J) (hj : ¬ (A.swTie j ∨ A.ownF j)) : A.En.par.slS st j = 0 :=
  pushJ_zero _ _ j fun j' e =>
    A.D.slS_supp A.swTie h.inc A.d st j' fun hh => hj (by rw [← e]; exact hh)

theorem end_own {Dt : A.J → Prop} (h : A.MaskOK Dt) :
    A.En.par.OwnW fun j => Dt j ∨ A.swTie j ∨ A.ownF j ∨ A.ownE j := by
  refine ⟨h.injE,
    fun i => Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)),
    fun _ _ _ _ => funext fun a => a.elim,
    fun st m m' hm => ?_,
    fun st j hj =>
      A.inc_supp h st j fun hh =>
        hj (hh.elim (fun a => Or.inr (Or.inl a)) fun a => Or.inr (Or.inr (Or.inl a))),
    fun _ _ _ _ => funext fun a => a.elim,
    fun st m m' hm => ?_,
    fun st i =>
      A.inc_supp h st _ fun hh => hh.elim (fun a => h.inE _ a ⟨i, rfl⟩) fun a => h.fE _ a ⟨i, rfl⟩⟩
  · funext b X
    show Alg.mle (fun b => m (A.En.tAt b)) _ = Alg.mle (fun b => m' (A.En.tAt b)) _
    rw [funext fun b => hm (A.En.tAt b) (Or.inl (h.bits _ _))]
  · funext b X
    show Alg.mle (fun b => m (A.En.tAt b)) _ = Alg.mle (fun b => m' (A.En.tAt b)) _
    rw [funext fun b => hm (A.En.tAt b) fun i hi => h.dtE _ (h.bits _ _) ⟨i, hi⟩]

theorem bit_own {Dt : A.J → Prop} (h : A.MaskOK Dt) :
    A.Bt.zc.next.OwnOur fun j' => (fun j => Dt j ∨ A.ownB j) ((Equiv.refl A.J) j') := by
  refine ⟨h.injB, fun i => Or.inr ⟨i, rfl⟩, fun st m m' hm => ?_,
    fun _ _ _ _ => funext fun b => b.elim, fun _ _ _ => rfl, fun st m m' hm => ?_,
    fun _ _ _ _ => funext fun b => b.elim, fun _ _ => rfl⟩
  · funext a X
    show Alg.mle (fun b => m (A.IT.tAt b)) _ = Alg.mle (fun b => m' (A.IT.tAt b)) _
    rw [funext fun b => hm (A.IT.tAt b) (Or.inl (h.bits _ _))]
  · funext a X
    show Alg.mle (fun b => m (A.IT.tAt b)) _ = Alg.mle (fun b => m' (A.IT.tAt b)) _
    rw [funext fun b => hm (A.IT.tAt b) fun i hi => h.dtB _ (h.bits _ _) ⟨i, hi⟩]

/-- Under `hA` there is a variable: 0 < w. -/
theorem w_pos {p : ℕ} (hA : A.H.lkb.Adm p) : 0 < A.w := by
  have h1 : A.n + 1 ≤ 2 ^ A.w := hA.1
  have h2 : 2 ^ (A.v' + 1) < 2 ^ (A.n + 1) := hA.2.1
  have h3 : A.v' + 1 < A.n + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
  by_contra h0
  have h4 : A.w = 0 := by omega
  rw [h4] at h1
  simp at h1
  omega

end LdLkp.LkAsm2
end Own

section Forest
variable (E : Type) [Field E] [Fintype E]

/-- Under `h0`: what the honest run of the keys' side, the step and the levels below l makes of a
claim gives the sum claim of level l. -/
theorem mjsp_forest2 (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)
    (Rd : A.J → Prop) (C : A.XR → (A.J → E) → Prop)
    (h0 : ∀ x' k, (A.mjForest Ex M Wp Kc msg Rd 0).sp C x' k → A.D.sumAt 0 x' k) :
    ∀ (l : ℕ) (x' : E × (A.D.lv l).T.St) (k : A.J → E),
      (A.mjForest Ex M Wp Kc msg Rd l).sp C x' k → A.D.sumAt l x' k
  | 0, x', k, h => h0 x' k h
  | l + 1, x', k, h =>
    A.D.next_sum E (ldLkpInst2_step E A.IT A.n) Ex Rd l _ x' k
      ((mjsp_seq (A.mjForest Ex M Wp Kc msg Rd l) (A.D.mjLev Ex Rd l) C x' k).1 h)

theorem mjl_forest2 (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)
    (Dt Rd : A.J → Prop) (C : A.XR → (A.J → E) → Prop) (SrK : A.J → Prop)
    (hK : (A.mjForest Ex M Wp Kc msg Rd 0).Link (A.forest Ex M Wp Kc msg 0).H
      (fun w => mjCut Rd (msg w.1)) (fun w => mjCut Rd (msg w.1)) SrK A.swK C)
    (h0 : ∀ x' k, (A.mjForest Ex M Wp Kc msg Rd 0).sp C x' k → A.D.sumAt 0 x' k) :
    ∀ l, (∀ l' < l, A.D.MaskOK l' Dt A.swTie) → (∀ l' < l, ∀ j, A.D.srAt Dt A.swTie l' j → Rd j) →
      (∀ l' < l, MjStab C (A.D.ownAt l')) → (∀ l' < l, ∀ j, SrK j → ¬ A.D.ownAt l' j) →
      (A.mjForest Ex M Wp Kc msg Rd l).Link (A.forest Ex M Wp Kc msg l).H
        (fun w => mjCut Rd (msg w.1)) (fun w => mjCut Rd (msg w.1))
        (fun j => SrK j ∨ ∃ l' < l, A.D.srAt Dt A.swTie l' j)
        (fun j => A.swK j ∨ ∃ l' < l, A.D.ownAt l' j) C
  | 0, _, _, _, _ => mjl_mono hK (fun _ h => Or.inl h) fun _ h => Or.inl h
  | l + 1, hM, hRd, hs, hd0 => by
      have ih := mjl_forest2 A Ex M Wp Kc msg Dt Rd C SrK hK h0 l
        (fun l' h => hM l' (Nat.lt_succ_of_lt h)) (fun l' h => hRd l' (Nat.lt_succ_of_lt h))
        (fun l' h => hs l' (Nat.lt_succ_of_lt h)) fun l' h => hd0 l' (Nat.lt_succ_of_lt h)
      have hd : ∀ j, (SrK j ∨ ∃ l' < l, A.D.srAt Dt A.swTie l' j) → ¬ A.D.ownAt l j := fun j hj =>
        hj.elim (hd0 l (Nat.lt_succ_self l) j) fun ⟨l', h1, hj⟩ =>
          A.D.sr_own (hM l (Nat.lt_succ_self l)) h1 (le_refl l) j hj
      have h2 := A.D.lev_link E Ex M Wp Kc msg l Dt A.swTie Rd
        ((A.mjForest Ex M Wp Kc msg Rd l).sp C) (hM l (Nat.lt_succ_self l))
        (hRd l (Nat.lt_succ_self l)) (mjsp_forest2 E A Ex M Wp Kc msg Rd C h0 l)
        (mjst_sp (hs l (Nat.lt_succ_self l)) ih.reads hd)
      exact mjl_mono (mjl_seq ih h2 hd (hs l (Nat.lt_succ_self l)))
        (fun _ h =>
          h.elim (fun a => a.elim Or.inl fun ⟨l', h1, hj⟩ => Or.inr ⟨l', Nat.lt_succ_of_lt h1, hj⟩)
            fun hj => Or.inr ⟨l, Nat.lt_succ_self l, hj⟩) fun _ h =>
              h.elim
                (fun a => a.elim Or.inl fun ⟨l', h1, hj⟩ => Or.inr ⟨l', Nat.lt_succ_of_lt h1, hj⟩)
                fun hj => Or.inr ⟨l, Nat.lt_succ_self l, hj⟩

end Forest

section Main
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpMaskAsm2_link : Spec.ldLkpMaskAsm2_link E := by
  intro p _ A Mu Ex hne M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs
  obtain ⟨y₀⟩ := hne
  -- sets
  have sTie : ∀ l ≤ A.n, MjStab C (A.H.tie.ownAt l) := fun l hl =>
    mjst_mono hs fun j hj => Or.inl ⟨l, hl, hj⟩
  have sK : ∀ l ≤ A.v', MjStab C ((A.IK.setV (A.v' + 1)).DK.ownAt l) := fun l hl =>
    mjst_mono hs fun j hj => Or.inr (Or.inl ⟨l, hl, hj⟩)
  have sF : ∀ l < A.d, MjStab C (A.D.ownAt l) := fun l hl =>
    mjst_mono hs fun j hj => Or.inr (Or.inr (Or.inl ⟨l, hl, hj⟩))
  have sE : MjStab C A.ownE := mjst_mono hs fun j hj => Or.inr (Or.inr (Or.inr (Or.inl hj)))
  have sB : MjStab C A.ownB := mjst_mono hs fun j hj => Or.inr (Or.inr (Or.inr (Or.inr hj)))
  have rTie : ∀ j, (∃ l ≤ A.n, A.H.tie.srAt Dt l j) → Dt j ∨ A.swTie j := fun j ⟨l, hl, hj⟩ =>
    hj.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩
  have rK : ∀ j, (∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) →
      Dt j ∨ A.swTie j ∨ A.swK j := fun j ⟨l, hl, hj⟩ =>
    hj.elim Or.inl fun a => Or.inr (a.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩)
  have rF : ∀ j,
      (∃ l' < A.d, A.D.srAt Dt A.swTie l' j) → Dt j ∨ A.swTie j ∨ A.ownF j := fun j ⟨l', h1, hj⟩ =>
    hj.elim Or.inl fun hj =>
      Or.inr (hj.elim Or.inl fun ⟨l'', h2, ho⟩ => Or.inr ⟨l'', Nat.lt_of_le_of_lt h2 h1, ho⟩)
  have dtK : ∀ j, (Dt j ∨ A.swTie j) → ¬ A.swK j := fun j hj ⟨l, hl, ho⟩ =>
    hj.elim (fun a => hOK.keyT.dt l hl j a ho) fun a => hOK.keyT.io l hl j a ho
  have dtF : ∀ j, (Dt j ∨ A.swTie j) → ∀ l < A.d, ¬ A.D.ownAt l j := fun j hj l hl ho =>
    hj.elim (fun a => (hOK.lev l hl).dt l (le_refl l) j a ho) fun a =>
      (hOK.lev l hl).io l (le_refl l) j a ho
  -- the head
  have hq : ∀ (x : A.H.St × E) (m : A.H.J → E), A.H.tie.Q x m 0 =
      ∏ j ∈ Finset.range (A.H.n + 1), tabProd A.H.d (A.H.tab x.1) (A.H.bit m) x.2 j ^ 2 ^ j :=
    fun x m => (ldLkpTie_hU E (A.H.n + 1) (A.H.PT x m) (Nat.succ_pos _)).2.2
  have hC1 : ∀ st k,
      C st k → ∀ lam : E, A.H.tie.claim 0 ((0 : E), (st, lam)) k := fun st k hc lam => by
    have h1 := (hMu st k (hC st k hc).1 (hC st k hc).2 lam).1.2.2
    show keyProd A.H.v (A.H.key st k) lam - A.H.tie.Q (st, lam) k 0 = 0
    rw [hq]
    exact sub_eq_zero.mpr h1
  have hRd1 : ∀ j, A.H.tie.srAt Dt A.H.n j → Rd j := fun j hj =>
    hRd j ((rTie j ⟨A.n, le_refl _, hj⟩).elim Or.inl fun a => Or.inr (Or.inl a))
  have L1 : ∀ (M Wp Kc : Type) (msg : M → A.J → E), _ := fun M Wp Kc msg =>
    mjl_head E A.H Ex M Wp Kc msg Dt Rd C hOK.tie hRd1 hC1 sTie
  have S1 := mjsp_good (b := A.H.headA Ex (A.J → E) Unit Unit fun m => m)
    (L1 (A.J → E) Unit Unit fun m => m)
    (fun w j hj => mjCut_of w.1 (hRd j ((rTie j hj).elim Or.inl fun a => Or.inr (Or.inl a))))
    (plain_head Ex (A.J → E) Unit Unit A.H fun m => m)
    (ldLkpHead2_good E p A.H Mu Ex Unit (A.J → E) Unit (mjTriv A.St Ex _) (fun m => m) hA hMu)
    fun st k hc _ => ⟨trivial, hC st k hc⟩
  -- the point: what waits after it
  have J2 : ∀ (M Wp Kc : Type) (msg : M → A.J → E) x k,
      ((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).sp C x k →
      A.ΨK Mu x k ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) k) (A.IK.lam x) + ∑ j, A.IK.fK x j * k j =
        A.tK (A.oR x) := fun M Wp Kc msg x k hx => by
    obtain ⟨x2, ρ, hx2, rfl⟩ := (mjsp_seq _ _ C x k).1 hx
    have hx3 := Eq.mp
      (congrFun (congrFun (A.H.sp_indep Ex M Wp Kc (A.J → E) Unit Unit msg (fun m => m) Rd C) x2) k)
      hx2
    obtain ⟨h1, h2⟩ := (A.junction1 hA.1 Mu x2 k).1 (S1 x2 k hx3 y₀).2
    exact (A.junction2 Mu _ k).1
      ⟨⟨h1, fun r hr => absurd hr List.not_mem_nil⟩,
        pscIn_fwd E A.R.toIn
          (ldLkpRoot_link E A.R (ldLkpInst2_step E A.I1 A.n) fun _ _ _ => rfl) x2 ρ.1 k h2⟩
  have L1R : ∀ (M Wp Kc : Type) (msg : M → A.J → E), _ := fun M Wp Kc msg =>
    mjl_seq (L1 M Wp Kc msg)
      (mjl_draw A.R.toIn.ev.D A.R.toIn.nxX Ex (M × Wp) A.R.toIn.AllHold
        ((A.H.mjHead Ex M Wp Kc msg Rd).sp C) fun w => mjCut Rd (msg w.1))
      (fun _ _ h => h) (mjst_false C)
  have r1R : ∀ j, ((∃ l ≤ A.H.n, A.H.tie.srAt Dt l j) ∨ False) → Dt j ∨ A.swTie j := fun j hj =>
    hj.elim (rTie j) False.elim
  have spR : ∀ (M Wp Kc : Type) (msg : M → A.J → E),
      ((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).sp C =
        ((A.H.mjHead Ex (A.J → E) Unit Unit (fun m => m) Rd).seq (A.R.toIn.mj Ex)).sp
          C := fun M Wp Kc msg => by
    rw [mjsp_seq_eq, mjsp_seq_eq, A.H.sp_indep Ex M Wp Kc (A.J → E) Unit Unit msg (fun m => m) Rd C]
  -- the keys' side
  have hRd2 : ∀ j, (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie A.v' j → Rd j := fun j hj =>
    hRd j ((rK j ⟨A.v', le_refl _, hj⟩).elim Or.inl fun a =>
        Or.inr (a.elim Or.inl fun b => Or.inr (Or.inl b)))
  have L2 : ∀ (M Wp Kc : Type) (msg : M → A.J → E), _ := fun M Wp Kc msg =>
    mjl_segK E A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg Dt A.swTie Rd
      (((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).sp C) hOK.keyT hRd2
      (fun x k hx => (J2 M Wp Kc msg x k hx).2) fun l hl =>
        mjst_sp (sK l hl) (L1R M Wp Kc msg).reads fun j hj ho => dtK j (r1R j hj) ⟨l, hl, ho⟩
  have S2 := mjsp_good
    (b := segK A.IK A.v' (fun x => A.tK (A.oR x)) Ex (A.J → E) Unit Unit fun m => m)
    (L2 (A.J → E) Unit Unit fun m => m)
    (fun w j hj =>
      mjCut_of w.1
        (hRd j ((rK j hj).elim Or.inl fun a => Or.inr (a.elim Or.inl fun b => Or.inr (Or.inl b)))))
    (plain_segK Ex (A.J → E) Unit Unit A.IK A.v' (fun x => A.tK (A.oR x)) fun m => m)
    (ldLkpSegK_good E A.IK A.v' (fun x => A.tK (A.oR x)) Ex Unit A.St (A.J → E) Unit
      (mjTriv A.St Ex _) (fun m => m) (fun x => (A.b2 (A.oR x)).1) (A.ΨK Mu) (A.ΨK fun _ _ => True))
    fun x k hx _ => ⟨trivial, J2 (A.J → E) Unit Unit (fun m => m) x k hx⟩
  -- the step into the forest
  have LK := mjl_post (L2 M Wp Kc msg) (fun x => some (A.enterT x)) (ExtMap.id Ex) A.enterT
    (fun o => (A.enterT o.1, o.2)) (fun w => mjCut Rd (msg w.1)) (fun _ => rfl) fun _ => rfl
  have h0 : ∀ x' k,
      (A.mjForest Ex M Wp Kc msg Rd 0).sp
        (((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).sp C) x' k →
      A.D.sumAt 0 x' k := fun x' k hx => by
    obtain ⟨x4, hx4, rfl⟩ := (mjsp_post _ _ _ _ _ x' k).1 hx
    have hx5 := Eq.mp
      (congrArg (fun Z => (mjSegK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg Rd).sp Z x4 k)
        (spR M Wp Kc msg)) hx4
    have hx6 := Eq.mp
      (congrFun (congrFun
          (segK_sp_indep A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc (A.J → E)
            Unit Unit msg (fun m => m) Rd _) x4) k) hx5
    exact (A.enter_iff x4 k).2 (S2 x4 k hx6 y₀).2.1.1.2
  have s1R : ∀ S : A.J → Prop, MjStab C S → (∀ j, (Dt j ∨ A.swTie j) → ¬ S j) →
      MjStab (((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).sp C) S := fun S h1 h2 =>
    mjst_sp h1 (L1R M Wp Kc msg).reads fun j hj => h2 j (r1R j hj)
  have dKF : ∀ l' < A.d, ∀ j, (∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) →
      ¬ A.D.ownAt l' j := fun l' hl j hj ho =>
    (rK j hj).elim (fun a => dtF j (Or.inl a) l' hl ho) fun a =>
      a.elim (fun b => dtF j (Or.inr b) l' hl ho) fun b => hOK.kT j b (Or.inl ⟨l', hl, ho⟩)
  have LF := mjl_forest2 E A Ex M Wp Kc msg Dt Rd _ _ LK h0 A.d hOK.lev
    (fun l' hl j hj =>
      hRd j ((rF j ⟨l', hl, hj⟩).elim Or.inl fun a =>
          Or.inr (a.elim Or.inl fun b => Or.inr (Or.inr (Or.inl b)))))
    (fun l' hl => s1R _ (sF l' hl) fun j hj => dtF j hj l' hl) dKF
  have rKF : ∀ j,
      ((∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) ∨
        ∃ l' < A.d, A.D.srAt Dt A.swTie l' j) →
      (Dt j ∨ A.swTie j) ∨ A.swK j ∨ A.ownF j := fun j hj =>
    hj.elim (fun a =>
      (rK j a).elim (fun b => Or.inl (Or.inl b)) fun b =>
          b.elim (fun c => Or.inl (Or.inr c)) fun c => Or.inr (Or.inl c)) fun a =>
            (rF j a).elim (fun b => Or.inl (Or.inl b)) fun b =>
              b.elim (fun c => Or.inl (Or.inr c)) fun c => Or.inr (Or.inr c)
  have dKFw : ∀ j, ((∃ l ≤ A.H.n, A.H.tie.srAt Dt l j) ∨ False) →
      ¬ (A.swK j ∨ ∃ l' < A.d, A.D.ownAt l' j) := fun j hj hw =>
    hw.elim (dtK j (r1R j hj)) fun ⟨l', hl, ho⟩ => dtF j (r1R j hj) l' hl ho
  have sKF : MjStab C fun j => A.swK j ∨ ∃ l' < A.d, A.D.ownAt l' j :=
    mjst_mono hs fun j hj =>
      hj.elim (fun a => Or.inr (Or.inl a)) fun a => Or.inr (Or.inr (Or.inl a))
  have L3 := mjl_seq (L1R M Wp Kc msg) LF dKFw sKF
  have r3 : ∀ j,
      (((∃ l ≤ A.H.n, A.H.tie.srAt Dt l j) ∨ False) ∨
        ((∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) ∨
          ∃ l' < A.d, A.D.srAt Dt A.swTie l' j)) →
      (Dt j ∨ A.swTie j) ∨ A.swK j ∨ A.ownF j :=
    fun j hj => hj.elim (fun a => Or.inl (r1R j a)) (rKF j)
  have d3E : ∀ j, ((Dt j ∨ A.swTie j) ∨ A.swK j ∨ A.ownF j) → ¬ A.ownE j := fun j hj ho =>
    hj.elim (fun a => a.elim (fun b => hOK.dtE j b ho) fun b => hOK.inE j b ho) fun a =>
      a.elim (fun b => hOK.kT j b (Or.inr (Or.inl ho))) fun b => hOK.fE j b ho
  have d3B : ∀ j, ((Dt j ∨ A.swTie j) ∨ A.swK j ∨ A.ownF j) → ¬ A.ownB j := fun j hj ho =>
    hj.elim (fun a => a.elim (fun b => hOK.dtB j b ho) fun b => hOK.inB j b ho) fun a =>
      a.elim (fun b => hOK.kT j b (Or.inr (Or.inr ho))) fun b => hOK.fB j b ho
  -- the closing
  have hne' : A.En.par.fmt ≠ [] := by
    have hw := A.w_pos hA
    show List.replicate (A.w + A.d) (pfCube E 2) ≠ []
    intro e
    have := congrArg List.length e
    simp at this
    omega
  have hsum3 : ∀ x k,
      (((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).seq
          (A.mjForest Ex M Wp Kc msg Rd A.d)).sp
        C x k →
      A.D.sumAt A.d x k := fun x k hx =>
    mjsp_forest2 E A Ex M Wp Kc msg Rd _ h0 A.d x k ((mjsp_seq _ _ C x k).1 hx)
  have LE := mjCore_link E A.En.par Ex (M × Wp) (fun w => msg w.1) Rd
    (fun j => Dt j ∨ A.swTie j ∨ A.ownF j ∨ A.ownE j)
    (ldLkpEndU_vars E A.En).1 (ldLkpEndU_deg E A.En)
    (PscPar.ownW_mono
      (fun j hj =>
        hRd j (hj.elim Or.inl fun a =>
            Or.inr
              (a.elim Or.inl fun b => Or.inr (Or.inr (b.elim Or.inl fun c => Or.inr (Or.inl c))))))
      (A.end_own hOK))
    (A.end_own hOK) hne'
    ((((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).seq
      (A.mjForest Ex M Wp Kc msg Rd A.d)).sp C)
    (fun x k hx =>
      (ldLkpEndU_sum E A.En x k).2 ((ldLkpInst2_top_iff E A.IT A.n A.wE x k).1 (hsum3 x k hx)))
    (mjst_sp sE L3.reads fun j hj => d3E j (r3 j hj))
  have L4 := mjl_seq L3 LE (fun j hj => d3E j (r3 j hj)) sE
  have r4 : ∀ j,
      ((((∃ l ≤ A.H.n, A.H.tie.srAt Dt l j) ∨ False) ∨
          ((∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) ∨
            ∃ l' < A.d, A.D.srAt Dt A.swTie l' j)) ∨
        (Dt j ∨ A.swTie j ∨ A.ownF j ∨ A.ownE j)) → ¬ A.ownB j :=
    fun j hj =>
      hj.elim (fun a => d3B j (r3 j a)) fun a =>
        a.elim (hOK.dtB j) fun b => b.elim (hOK.inB j) fun c => c.elim (hOK.fB j) (hOK.eB j)
  -- the bit test
  have hCb : ∀ st k, C st k → Bits A.d A.w (A.H.bit k) := fun st k hc =>
    (hMu st k (hC st k hc).1 (hC st k hc).2 0).1.1
  have s4 : MjStab
      (((((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).seq
          (A.mjForest Ex M Wp Kc msg Rd A.d)).seq
        (A.En.par.mjC Ex Rd)).sp C) A.ownB :=
    mjst_sp sB L4.reads r4
  have hB2 := mjl_our E A.Bt.zc.next Ex A.J (Equiv.refl _) (M × Wp) (fun w => msg w.1) Rd
    (fun j => Dt j ∨ A.ownB j) (ldZero_vars E A.Bt.zc).1 (ldLkpBit_degX E A.Bt)
    (ldLkpBit_degY E A.Bt) (A.bit_own hOK)
    (fun j hj => hRd j (hj.elim Or.inl fun a => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr a))))))
    ((A.Bt.zc.toIn.mj Ex).sp
      (((((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).seq
          (A.mjForest Ex M Wp Kc msg Rd A.d)).seq
        (A.En.par.mjC Ex Rd)).sp C))
    (by
      rintro _ k ⟨o, ρ, hc, rfl⟩
      have hb : Bits A.d A.w (A.H.bit k) :=
        mjsp_keeps _ (P := fun k => Bits A.d A.w (A.H.bit k)) hCb o k hc
      exact pscIn_fwd E A.Bt.zc.toIn (ldZero_link E A.Bt.zc) o ρ.1 k
        ((ldZero_all E A.Bt.zc o k).2
          ((ldLkpBit_zero E A.Bt o k).2 ((ldLkpInst_bits E A.IT _ A.wB A.cB k).2 hb))))
    (mjst_sp s4 (Sr := fun _ => False) (fun _ _ _ _ _ => rfl) fun _ hh => hh.elim)
  have LB := mjl_seq
    (mjl_draw A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex (M × Wp) A.Bt.zc.toIn.AllHold
      (((((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).seq
          (A.mjForest Ex M Wp Kc msg Rd A.d)).seq
        (A.En.par.mjC Ex Rd)).sp C)
      fun w => mjCut Rd (msg w.1))
    hB2 (fun _ hh => hh.elim) s4
  refine mjl_mono
    (mjl_seq L4 LB (fun j hj hw => hw.elim id (r4 j hj))
      (mjst_mono sB fun j hw => hw.elim False.elim id))
    (fun j hj => ?_) fun j hj => ?_
  · rcases hj with (hj | hj) | hj | hj
    · exact (r3 j hj).elim (fun a => a.elim Or.inl fun b => Or.inr (Or.inl b)) fun a =>
        a.elim (fun b => Or.inr (Or.inr (Or.inl b))) fun b => Or.inr (Or.inr (Or.inr (Or.inl b)))
    · exact hj.elim Or.inl fun a =>
        Or.inr (a.elim Or.inl fun b => Or.inr (Or.inr (b.elim Or.inl fun c => Or.inr (Or.inl c))))
    · exact hj.elim
    · exact hj.elim Or.inl fun a => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr a))))
  · rcases hj with (((hj | hj) | hj | hj) | hj) | hj | hj
    · exact Or.inl hj
    · exact hj.elim
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hj)))
    · exact hj.elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr hj)))

theorem ldLkpMaskAsm2_mm : Spec.ldLkpMaskAsm2_mm E := by
  intro p _ A Mu Ex hne M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs
  have h := ldLkpMaskAsm2_link E p A Mu Ex M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs
  exact ⟨mjl_mm h,
    mjl_mm (mjl_post h (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd (fun o => (A.rd o.1, o.2))
        (fun w => mjCut Rd (msg w.1)) (fun _ => rfl) fun _ => rfl)⟩

end Main
end Cb
