-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskAsmProofs.lean: proofs for Cb/Ld/LdLkpMaskAsm.lean.

The order: (1) What the honest run of one of the first two parts makes of a claim does not depend on
the tuple type at which the part's `MJ` record is written (`LkHead.sp_indep`, `segK_sp_indep`). (2)
The claims at the two junctions (`LkAsm.junction1`, `LkAsm.junction2`, Cb/Ld/LdLkpAsmProofs.lean):
by the parts' completeness at the tuple type J → E. (3) The three parts in a row (`A.H.mjHead`,
`mjSegK`, `A.Q.mjSegT`).

Main names (statements and hypotheses: Cb/Ld/LdLkpMaskAsm.lean):
  `ldLkpMaskAsm_link`: see its statement in Cb/Ld/LdLkpMaskAsm.lean.
  `ldLkpMaskAsm_mm`: see its statement in Cb/Ld/LdLkpMaskAsm.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskAsm
import Cb.Ld.LdLkpAsmProofs
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

/-! ## 1. The claims after the first two parts do not depend on the tuple type -/

section Indep
variable {E J : Type}

theorem mjsp_seq_eq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂}
    {R₂ : IOR X₂ E₂ X₃ E₃} (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) (C : X₁ → (J → E) → Prop) :
    (D₁.seq D₂).sp C = D₂.sp (D₁.sp C) :=
  funext fun x' => funext fun k => propext (mjsp_seq D₁ D₂ C x' k)

theorem mjsp_pre_eq {Xi Xi' Xo : Type} {Ei Ei' Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} (D : MJ E J R)
    (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (φ : Xi' → Xi) (C : Xi' → (J → E) → Prop) :
    (D.pre f g φ).sp C = D.sp fun x k => ∃ x₀, C x₀ k ∧ x = φ x₀ :=
  funext fun x' => funext fun k => propext (mjsp_pre D f g φ C x' k)

theorem mjsp_to_indep {K K' M M' Wp Wp' : Type} {Ex : ExtSpec} (X : ℕ → Type)
    (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (b' : ∀ l, BkA K' M' (X l) (X (l + 1)) Ex Wp')
    (D : ∀ l, MJ E J (b l).R) (D' : ∀ l, MJ E J (b' l).R) (C : X 0 → (J → E) → Prop)
    (h : ∀ l (C' : X l → (J → E) → Prop), (D l).sp C' = (D' l).sp C') :
    ∀ l, MJ.spTo X b D C l = MJ.spTo X b' D' C l
  | 0 => rfl
  | l + 1 => by
      show (D l).sp (MJ.spTo X b D C l) = (D' l).sp (MJ.spTo X b' D' C l)
      rw [mjsp_to_indep X b b' D D' C h l, h]

theorem mjsp_chain_indep {K K' M M' Wp Wp' : Type} {Ex : ExtSpec} (X : ℕ → Type)
    (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (b' : ∀ l, BkA K' M' (X l) (X (l + 1)) Ex Wp')
    (D : ∀ l, MJ E J (b l).R) (D' : ∀ l, MJ E J (b' l).R) (C : X 0 → (J → E) → Prop)
    (h : ∀ l (C' : X l → (J → E) → Prop), (D l).sp C' = (D' l).sp C') (n : ℕ) :
    (MJ.chain X b D n).sp C = (MJ.chain X b' D' n).sp C := by
  rw [mjsp_chain, mjsp_chain, mjsp_to_indep X b b' D D' C h]

end Indep

section Parts
variable {E : Type} [Field E] [Fintype E]

theorem LdLkp.LkHead.sp_indep (H : LkHead E) (Ex : ExtSpec) (M Wp Kc M' Wp' Kc' : Type)
    (msg : M → H.J → E) (msg' : M' → H.J → E) (Rd : H.J → Prop) (C : H.St → (H.J → E) → Prop) :
    (H.mjHead Ex M Wp Kc msg Rd).sp C = (H.mjHead Ex M' Wp' Kc' msg' Rd).sp C := by
  refine (mjsp_seq_eq (MJ.silent E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True)
      ((H.tie.mjTie Ex M Wp Kc msg Rd H.n).pre (fun x => some ((0 : E), x))
        (ExtMap.id Ex) fun x => ((0 : E), x)) C).trans
    (Eq.trans ?_
      (mjsp_seq_eq (MJ.silent E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True)
        ((H.tie.mjTie Ex M' Wp' Kc' msg' Rd H.n).pre (fun x => some ((0 : E), x))
          (ExtMap.id Ex) fun x => ((0 : E), x)) C).symm)
  refine (mjsp_pre_eq _ _ _ _ _).trans (Eq.trans ?_ (mjsp_pre_eq _ _ _ _ _).symm)
  exact mjsp_chain_indep (fun l => E × (H.tie.lv l).T.St) (H.tie.stepA Ex Wp Kc msg)
    (H.tie.stepA Ex Wp' Kc' msg') (fun l => H.tie.mjAt Ex Rd l)
    (fun l => H.tie.mjAt Ex Rd l) _ (fun _ _ => rfl) H.n

theorem LdLkp.segK_sp_indep (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec)
    (M Wp Kc M' Wp' Kc' : Type) (msg : M → I.J → E) (msg' : M' → I.J → E)
    (Rd : I.J → Prop) (C : I.X → (I.J → E) → Prop) :
    (mjSegK I v' tK Ex M Wp Kc msg Rd).sp C = (mjSegK I v' tK Ex M' Wp' Kc' msg' Rd).sp C := by
  refine (mjsp_pre_eq ((I.setV (v' + 1)).DK.mjTree Ex M Wp Kc msg Rd v') _ _ _ C).trans
    (Eq.trans ?_ (mjsp_pre_eq ((I.setV (v' + 1)).DK.mjTree Ex M' Wp' Kc' msg' Rd v') _ _ _ C).symm)
  exact mjsp_chain_indep (fun l => E × ((I.setV (v' + 1)).DK.lv l).T.St)
    ((I.setV (v' + 1)).DK.levA Ex Wp Kc msg) ((I.setV (v' + 1)).DK.levA Ex Wp' Kc' msg')
    (fun l => (I.setV (v' + 1)).DK.mjLev Ex Rd l)
    (fun l => (I.setV (v' + 1)).DK.mjLev Ex Rd l) _ (fun _ _ => rfl) v'

end Parts

/-! ## 2, 3. The junctions; the three parts in a row -/

section Main
variable (E : Type) [Field E] [Fintype E]

/-- The joint that asks nothing. -/
def mjTriv (X : Type) (Ex : ExtSpec) (W : Type) : Rels Unit X Ex W :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

theorem ldLkpMaskAsm_link : Spec.ldLkpMaskAsm_link E := by
  intro p _ A Mu Ex hne M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs
  obtain ⟨y₀⟩ := hne
  -- sets
  have sTie : ∀ l ≤ A.n, MjStab C (A.H.tie.ownAt l) := fun l hl =>
    mjst_mono hs fun j hj => Or.inl ⟨l, hl, hj⟩
  have sK : ∀ l ≤ A.v', MjStab C ((A.IK.setV (A.v' + 1)).DK.ownAt l) := fun l hl =>
    mjst_mono hs fun j hj => Or.inr (Or.inl ⟨l, hl, hj⟩)
  have sT : MjStab C A.Q.swT := mjst_mono hs fun j hj => Or.inr (Or.inr hj)
  have rTie : ∀ j, (∃ l ≤ A.n, A.H.tie.srAt Dt l j) → Dt j ∨ A.swTie j := fun j ⟨l, hl, hj⟩ =>
    hj.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩
  have rK : ∀ j, (∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) →
      Dt j ∨ A.swTie j ∨ A.swK j := fun j ⟨l, hl, hj⟩ =>
    hj.elim Or.inl fun a => Or.inr (a.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩)
  have dtK : ∀ j, (Dt j ∨ A.swTie j) → ¬ A.swK j := fun j hj ⟨l, hl, ho⟩ =>
    hj.elim (fun a => hOK.keyT.dt l hl j a ho) fun a => hOK.keyT.io l hl j a ho
  have dtT : ∀ j, (Dt j ∨ A.swTie j) → ¬ A.Q.swT j := fun j hj hw => by
    rcases hw with ⟨l, hl, ho⟩ | ho | ho
    · exact hj.elim (fun a => (hOK.tab.lev l hl).dt l (le_refl l) j a ho) fun a =>
        (hOK.tab.lev l hl).io l (le_refl l) j a ho
    · exact hj.elim (fun a => hOK.tab.dtE j a ho) fun a => hOK.tab.inE j a ho
    · exact hj.elim (fun a => hOK.tab.dtB j a ho) fun a => hOK.tab.inB j a ho
  -- the head
  have hq : ∀ (x : A.H.St × E) (m : A.H.J → E), A.H.tie.Q x m 0 =
      ∏ j ∈ Finset.range (A.H.n + 1), tabProd A.H.d (A.H.tab x.1) (A.H.bit m) x.2 j ^ 2 ^ j :=
    fun x m => (ldLkpTie_hU E (A.H.n + 1) (A.H.PT x m) (Nat.succ_pos _)).2.2
  have hC1 : ∀ st k,
      C st k → ∀ lam : E, A.H.tie.claim 0 ((0 : E), (st, lam)) k := fun st k hc lam => by
    have h1 := (hMu st k (hC st k hc).1 (hC st k hc).2 lam).1.1.2.2
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
    (ldLkpHead_good E p A.H Mu Ex Unit (A.J → E) Unit (mjTriv A.St Ex _) (fun m => m) hA hMu)
    fun st k hc _ => ⟨trivial, hC st k hc⟩
  have J1 : ∀ x k, (A.H.mjHead Ex M Wp Kc msg Rd).sp C x k →
      A.ΨK Mu x k ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) k) (A.IK.lam x) + ∑ j, A.fK x j * k j =
        A.tK x := fun x k hx => by
    rw [A.H.sp_indep Ex M Wp Kc (A.J → E) Unit Unit msg (fun m => m) Rd C] at hx
    exact (A.junction1 Mu x k).1 (S1 x k hx y₀).2
  -- the keys' side
  have hRd2 : ∀ j, (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie A.v' j → Rd j := fun j hj =>
    hRd j ((rK j ⟨A.v', le_refl _, hj⟩).elim Or.inl fun a =>
        Or.inr (a.elim Or.inl fun b => Or.inr (Or.inl b)))
  have L2 : ∀ (M Wp Kc : Type) (msg : M → A.J → E), _ := fun M Wp Kc msg => mjl_segK E A.IK A.v'
    A.tK Ex M Wp Kc msg Dt A.swTie Rd ((A.H.mjHead Ex M Wp Kc msg Rd).sp C) hOK.keyT hRd2
    (fun x k hx => by
      rw [A.H.sp_indep Ex M Wp Kc (A.J → E) Unit Unit msg (fun m => m) Rd C] at hx
      exact ((A.junction1 Mu x k).1 (S1 x k hx y₀).2).2)
    fun l hl =>
      mjst_sp (sK l hl) (L1 M Wp Kc msg).reads fun j hj ho => dtK j (rTie j hj) ⟨l, hl, ho⟩
  have S2 := mjsp_good (b := segK A.IK A.v' A.tK Ex (A.J → E) Unit Unit fun m => m)
    (L2 (A.J → E) Unit Unit fun m => m)
    (fun w j hj =>
      mjCut_of w.1
        (hRd j ((rK j hj).elim Or.inl fun a => Or.inr (a.elim Or.inl fun b => Or.inr (Or.inl b)))))
    (plain_segK Ex (A.J → E) Unit Unit A.IK A.v' A.tK fun m => m)
    (ldLkpSegK_good E A.IK A.v' A.tK Ex Unit A.St (A.J → E) Unit (mjTriv A.St Ex _) (fun m => m)
      (fun x => (A.b2 x).1) (A.ΨK Mu) (A.ΨK fun _ _ => True))
    fun x k hx _ => ⟨trivial, (A.junction1 Mu x k).1 (S1 x k hx y₀).2⟩
  have L12 :=
    mjl_seq (L1 M Wp Kc msg) (L2 M Wp Kc msg) (fun j hj => dtK j (rTie j hj)) (mjst_upto _ A.v' sK)
  have J2 : ∀ x k,
      ((A.H.mjHead Ex M Wp Kc msg Rd).seq (mjSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd)).sp C x k →
      A.ΨT Mu x k ∧ Bits A.Q.I.d A.Q.I.w (A.Q.I.bit k) ∧ A.Q.R.Holds x k := fun x k hx => by
    have hx0 := (mjsp_seq _ _ C x k).1 hx
    have hx1 := Eq.mp
      (congrArg (fun Z => (mjSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd).sp Z x k)
        (A.H.sp_indep Ex M Wp Kc (A.J → E) Unit Unit msg (fun m => m) Rd C)) hx0
    have hx2 := Eq.mp
      (congrFun (congrFun
          (segK_sp_indep A.IK A.v' A.tK Ex M Wp Kc (A.J → E) Unit Unit msg (fun m => m) Rd
            ((A.H.mjHead Ex (A.J → E) Unit Unit (fun m => m) Rd).sp C)) x) k) hx1
    exact (A.junction2 hA.1 Mu x k).1 (S2 x k hx2 y₀).2
  -- the table's side
  have r12 : ∀ j,
      ((∃ l ≤ A.H.n, A.H.tie.srAt Dt l j) ∨
        ∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) →
      (Dt j ∨ A.swTie j) ∨ A.swK j := fun j hj =>
    hj.elim (fun a => Or.inl (rTie j a)) fun a =>
      (rK j a).elim (fun b => Or.inl (Or.inl b)) fun b => b.elim (fun c => Or.inl (Or.inr c)) Or.inr
  have d12T : ∀ j,
      ((∃ l ≤ A.H.n, A.H.tie.srAt Dt l j) ∨
        ∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.srAt Dt A.swTie l j) → ¬ A.Q.swT j :=
    fun j hj => (r12 j hj).elim (dtT j) (hOK.kT j)
  have s4 : MjStab
      (((A.H.mjHead Ex M Wp Kc msg Rd).seq (mjSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd)).sp C)
      A.Q.swT :=
    mjst_sp sT L12.reads d12T
  have L3 := mjl_segT E A.Q Ex M Wp Kc msg Dt A.swTie Rd _ hOK.tab
    (fun j hj => hRd j (hj.elim Or.inl fun a => Or.inr (a.elim Or.inl fun b => Or.inr (Or.inr b))))
    (fun x k hx => (J2 x k hx).2.2) (fun x k hx => (J2 x k hx).2.1)
    (fun l hl => mjst_mono s4 fun j hj => Or.inl ⟨l, hl, hj⟩)
    (mjst_mono s4 fun j hj => Or.inr (Or.inl hj)) (mjst_mono s4 fun j hj => Or.inr (Or.inr hj))
  refine mjl_mono (mjl_seq L12 L3 d12T sT) (fun j hj => ?_) fun j hj => ?_
  · rcases hj with hj | hj
    · exact (r12 j hj).elim (fun a => a.elim Or.inl fun b => Or.inr (Or.inl b)) fun a =>
        Or.inr (Or.inr (Or.inl a))
    · exact hj.elim Or.inl fun a => Or.inr (a.elim Or.inl fun b => Or.inr (Or.inr b))
  · rcases hj with (hj | hj) | hj
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr hj)

theorem ldLkpMaskAsm_mm : Spec.ldLkpMaskAsm_mm E := by
  intro p _ A Mu Ex hne M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs
  have h := ldLkpMaskAsm_link E p A Mu Ex M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs
  exact ⟨mjl_mm h,
    mjl_mm (mjl_post h (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd (fun o => (A.rd o.1, o.2))
        (fun w => mjCut Rd (msg w.1)) (fun _ => rfl) fun _ => rfl)⟩

end Main
end Cb
