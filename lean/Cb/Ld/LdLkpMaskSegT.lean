-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskSegT.lean: the table's side of the assembled lookup (`LkAsm`, Cb/Ld/LdLkpAsm.lean) as
a link of a chain of masked blocks (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
This file is about the part of the lookup argument that treats the table.

Definitions, statements and proofs. Glue between Cb/Ld/LdLkpMaskTree.lean and
Cb/Ld/LdLkpMaskAsm.lean.
The table's side (`SegTab`, Cb/Ld/LdLkpSegT.lean): the point (`Q.R`) of the forest (`Q.D`), d
levels, the closing (`Q.En`) of the top claim (one sumcheck), the bit test (a zerocheck point, one
sumcheck).

Main names:
  `TreeP.lev_link`: under the hypotheses of its statement: one level of a tree is a link.
  `TreeP.slS_supp`: under `hinc`, the incoming form of level l reads In (level 0) or the two inner
    masks of the level before; as stated: it reads only the entries in In and the own masks of the
    levels below l.
  `Q.mjForest`, `mjl_forest`, `mjsp_forest`: the point and the levels below l; under `hC`, what
    their honest run makes of a claim gives the sum claim of level l.
  `Q.TabOK Dt In`: the conditions on the places for the table's side: those of the forest's levels;
    the incoming form of level 0 reads the entries in In only (`inc`); the bits are data; the own
    masks of the closing and of the bit test lie at different places, outside the data, outside In,
    outside the forest's masks, and apart from each other.
  `Q.mjSegT`, `mjl_segT`: under `h` and `hRd`: the table's side is a link, started with any claim
    that gives the masked claims on the roots and "all are bits", and reads no own mask of the side.

Limits: what the head of Cb/Ld/LdLkpMaskTree.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskSeg
import Cb.Ld.LdLkpSegTProofs
import Cb.Ld.LdLkpBitProofs
import Cb.Ld.LdLkpEndProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section Tree
variable (E : Type) [Field E] [Fintype E]

/-- Under `hM` and `hRd`: one level of a tree is a link, started with any claim that gives its sum
claim and does not read its own masks. -/
theorem LdLkp.TreeP.lev_link (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
    (l : ℕ) (Dt In Rd : D.J → Prop) (C : E × (D.lv l).T.St → (D.J → E) → Prop)
    (hM : D.MaskOK l Dt In) (hRd : ∀ j, D.srAt Dt In l j → Rd j)
    (hC : ∀ x k, C x k → D.sumAt l x k) (hs : MjStab C (D.ownAt l)) :
    (D.mjLev Ex Rd l).Link (D.levA Ex Wp Kc msg l).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (D.srAt Dt In l) (D.ownAt l) C := by
  have ok := ldLkpP_ok E D l
  exact mjl_mono
    (mjl_seq (mjl_our E (D.lv l).T Ex D.J (D.eJ l) (M × Wp) (fun w => msg w.1) Rd (D.srAt Dt In l)
        ok.1 ok.2.2.1 ok.2.2.2 (D.own_our hM l (le_refl l)) hRd C hC hs)
      (mjl_draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (M × Wp) (fun _ _ => True)
        _ fun w => mjCut Rd (msg w.1))
      (fun _ _ h => h) (mjst_false C))
    (fun _ h => h.elim id False.elim) fun _ h => h.elim id False.elim

variable {E}

theorem LdLkp.TreeP.slS_supp
    (D : TreeP E) (In : D.J → Prop) (hinc : ∀ st ϱ j, ¬ In j → D.inc0 st ϱ j = 0) :
    ∀ (l : ℕ) (s : (D.lv l).T.St) (j' : (D.lv l).T.J),
      ¬ (In ((D.lv l).toJ j') ∨ ∃ l' < l, D.ownAt l' ((D.lv l).toJ j')) → (D.lv l).T.slS s j' = 0
  | 0, s, j', h => hinc s.1 s.2 j' fun hi => h (Or.inl hi)
  | l + 1, s, j', h => by
      classical
      have hj : ¬ D.ownAt l j' := fun ho => h (Or.inr ⟨l, Nat.lt_succ_self l, ho⟩)
      show (D.lv l).T.lst s.1.st ((D.lv l).T.par.hp s.1.st s.1.pt) *
          ((if j' = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) then 1 - s.2 else 0) +
            if j' = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) then s.2 else 0) = 0
      have n0 : j' ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) := fun e =>
        hj (by rw [e]; exact D.c_own l false)
      have n1 : j' ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) := fun e =>
        hj (by rw [e]; exact D.c_own l true)
      rw [if_neg n0, if_neg n1, add_zero, mul_zero]

omit [Fintype E] in
theorem LdLkp.pushJ_zero {J' J : Type} [Fintype J'] (f : J' → J) (c : J' → E)
    (j : J) (h : ∀ j', f j' = j → c j' = 0) : pushJ f c j = 0 := by
  classical
  unfold pushJ
  refine Finset.sum_eq_zero fun j' _ => ?_
  by_cases e : f j' = j
  · rw [if_pos e, h j' e]
  · rw [if_neg e]

end Tree

namespace LdLkp.SegTab
variable {E : Type} [Field E] [Fintype E] (Q : SegTab E)

/-- The `MJ` record of the point of the forest and of the levels below l. -/
def mjForest (Ex : ExtSpec) {M : Type} (Wp Kc : Type)
    (msg : M → Q.I.J → E) (Rd : Q.I.J → Prop) :
    (l : ℕ) → MJ E Q.I.J (Q.forest Ex Wp Kc msg l).R
  | 0 => Q.R.toIn.mj Ex
  | l + 1 => (mjForest Ex Wp Kc msg Rd l).seq (Q.D.mjLev Ex Rd l)

/-- The places of the own masks of the closing, and of the bit test. -/
def ownE : Q.I.J → Prop := fun j => ∃ i, j = Sum.elim Q.wE (fun _ : Unit => Q.cE) i
def ownB : Q.I.J → Prop := fun j => ∃ i, j = Sum.elim Q.wB (fun _ : Unit => Q.cB) i
/-- The places of the own masks of the forest's levels. -/
def ownF : Q.I.J → Prop := fun j => ∃ l < Q.I.d, Q.D.ownAt l j

/-- The conditions on the places, for the table's side. -/
structure TabOK (Dt In : Q.I.J → Prop) : Prop where
  lev  : ∀ l < Q.I.d, Q.D.MaskOK l Dt In
  inc  : ∀ st ϱ j, ¬ In j → Q.D.inc0 st ϱ j = 0
  bits : ∀ u j, Dt (Q.I.bAt u j)
  injE : Function.Injective (Sum.elim Q.wE fun _ : Unit => Q.cE)
  injB : Function.Injective (Sum.elim Q.wB fun _ : Unit => Q.cB)
  dtE  : ∀ j, Dt j → ¬ Q.ownE j
  dtB  : ∀ j, Dt j → ¬ Q.ownB j
  inE  : ∀ j, In j → ¬ Q.ownE j
  inB  : ∀ j, In j → ¬ Q.ownB j
  fE   : ∀ j, Q.ownF j → ¬ Q.ownE j
  fB   : ∀ j, Q.ownF j → ¬ Q.ownB j
  eB   : ∀ j, Q.ownE j → ¬ Q.ownB j

/-- What the messages of the side read; where its own masks lie. -/
def srT (Dt In : Q.I.J → Prop) : Q.I.J → Prop := fun j =>
  Dt j ∨ In j ∨ Q.ownF j ∨ Q.ownE j ∨ Q.ownB j
def swT : Q.I.J → Prop := fun j => Q.ownF j ∨ Q.ownE j ∨ Q.ownB j

/-- The `MJ` record of the table's side. -/
def mjSegT (Ex : ExtSpec) {M : Type} (Wp Kc : Type)
    (msg : M → Q.I.J → E) (Rd : Q.I.J → Prop) :
    MJ E Q.I.J (Q.segT Ex Wp Kc msg).R :=
  ((Q.mjForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.mjJ Ex (Equiv.refl _) Rd)).seq
    ((Q.Bt.zc.toIn.mj Ex).seq (Q.Bt.zc.next.mjJ Ex (Equiv.refl _) Rd))

end LdLkp.SegTab

section Forest
variable (E : Type) [Field E] [Fintype E]

/-- Under `hC`: what the honest run of the point and of the levels below l makes of a claim gives
the sum claim of level l. -/
theorem mjsp_forest (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E)
    (Rd : Q.I.J → Prop) (C : Q.I.X → (Q.I.J → E) → Prop) (hC : ∀ x k, C x k → Q.R.Holds x k) :
    ∀ (l : ℕ) (x' : E × (Q.D.lv l).T.St) (k : Q.I.J → E),
      (Q.mjForest Ex Wp Kc msg Rd l).sp C x' k → Q.D.sumAt l x' k
  | 0, _, k, ⟨x, ρ, hc, e⟩ => by
      rw [e]
      exact pscIn_fwd E Q.R.toIn
        (ldLkpRoot_link E Q.R (ldLkpInst_stepT E Q.I) fun _ _ _ => rfl) x ρ.1 k (hC x k hc)
  | l + 1, x', k, h =>
    Q.D.next_sum E (ldLkpInst_stepT E Q.I) Ex Rd l _ x' k
      ((mjsp_seq (Q.mjForest Ex Wp Kc msg Rd l) (Q.D.mjLev Ex Rd l) C x' k).1 h)

theorem mjl_forest (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E)
    (Dt In Rd : Q.I.J → Prop) (C : Q.I.X → (Q.I.J → E) → Prop) (hC : ∀ x k, C x k → Q.R.Holds x k) :
    ∀ l, (∀ l' < l, Q.D.MaskOK l' Dt In) → (∀ l' < l, ∀ j, Q.D.srAt Dt In l' j → Rd j) →
      (∀ l' < l, MjStab C (Q.D.ownAt l')) →
      (Q.mjForest Ex Wp Kc msg Rd l).Link (Q.forest Ex Wp Kc msg l).H (fun w => mjCut Rd (msg w.1))
        (fun w => mjCut Rd (msg w.1)) (fun j => ∃ l' < l, Q.D.srAt Dt In l' j)
        (fun j => ∃ l' < l, Q.D.ownAt l' j) C
  | 0, _, _, _ =>
    mjl_mono (mjl_draw Q.R.toIn.ev.D Q.R.toIn.nxX Ex (M × Wp)
        Q.R.toIn.AllHold C fun w => mjCut Rd (msg w.1))
      (fun _ h => h.elim) fun _ h => h.elim
  | l + 1, hM, hRd, hs => by
      have ih := mjl_forest Q Ex M Wp Kc msg Dt In Rd C hC l
        (fun l' h => hM l' (Nat.lt_succ_of_lt h))
        (fun l' h => hRd l' (Nat.lt_succ_of_lt h)) fun l' h => hs l' (Nat.lt_succ_of_lt h)
      have hd : ∀ j, (∃ l' < l, Q.D.srAt Dt In l' j) → ¬ Q.D.ownAt l j := fun j ⟨l', h1, hj⟩ =>
        Q.D.sr_own (hM l (Nat.lt_succ_self l)) h1 (le_refl l) j hj
      have h2 := Q.D.lev_link E Ex M Wp Kc msg l Dt In Rd ((Q.mjForest Ex Wp Kc msg Rd l).sp C)
        (hM l (Nat.lt_succ_self l)) (hRd l (Nat.lt_succ_self l))
        (mjsp_forest E Q Ex M Wp Kc msg Rd C hC l) (mjst_sp (hs l (Nat.lt_succ_self l)) ih.reads hd)
      exact mjl_mono (mjl_seq ih h2 hd (hs l (Nat.lt_succ_self l)))
        (fun _ h =>
          h.elim (fun ⟨l', h1, hj⟩ => ⟨l', Nat.lt_succ_of_lt h1, hj⟩) fun hj =>
            ⟨l, Nat.lt_succ_self l, hj⟩) fun _ h =>
              h.elim (fun ⟨l', h1, hj⟩ => ⟨l', Nat.lt_succ_of_lt h1, hj⟩) fun hj =>
                ⟨l, Nat.lt_succ_self l, hj⟩

end Forest

section Closers
variable {E : Type} [Field E] [Fintype E] (Q : SegTab E)

/-- Under `h`: the incoming form of the closing reads In and the forest's masks only. -/
theorem LdLkp.SegTab.inc_supp {Dt In : Q.I.J → Prop} (h : Q.TabOK Dt In) (st : Q.En.psc.St)
    (j : Q.I.J) (hj : ¬ (In j ∨ Q.ownF j)) : Q.En.psc.slS st j = 0 :=
  pushJ_zero _ _ j fun j' e =>
    Q.D.slS_supp In h.inc Q.I.d st j' fun hh => hj (by rw [← e]; exact hh)

theorem LdLkp.SegTab.end_own {Dt In : Q.I.J → Prop} (h : Q.TabOK Dt In) :
    Q.En.psc.OwnOur fun j' =>
      (fun j => Dt j ∨ In j ∨ Q.ownF j ∨ Q.ownE j) ((Equiv.refl Q.I.J) j') := by
  refine ⟨h.injE,
    fun i => Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)),
    fun st m m' hm => ?_,
    fun _ _ _ _ => funext fun b => b.elim,
    fun st j hj =>
      Q.inc_supp h st j fun hh =>
        hj (hh.elim (fun a => Or.inr (Or.inl a)) fun a => Or.inr (Or.inr (Or.inl a))),
    fun st m m' hm => ?_,
    fun _ _ _ _ => funext fun b => b.elim,
    fun st i =>
      Q.inc_supp h st _ fun hh => hh.elim (fun a => h.inE _ a ⟨i, rfl⟩) fun a => h.fE _ a ⟨i, rfl⟩⟩
  · funext a X
    show Alg.mle (fun b => m (Q.I.tAt b)) _ = Alg.mle (fun b => m' (Q.I.tAt b)) _
    rw [funext fun b => hm (Q.I.tAt b) (Or.inl (h.bits _ _))]
  · funext a X
    show Alg.mle (fun b => m (Q.I.tAt b)) _ = Alg.mle (fun b => m' (Q.I.tAt b)) _
    rw [funext fun b => hm (Q.I.tAt b) fun i hi => h.dtE _ (h.bits _ _) ⟨i, hi⟩]

theorem LdLkp.SegTab.bit_own {Dt In : Q.I.J → Prop} (h : Q.TabOK Dt In) :
    Q.Bt.zc.next.OwnOur fun j' => (fun j => Dt j ∨ Q.ownB j) ((Equiv.refl Q.I.J) j') := by
  refine ⟨h.injB, fun i => Or.inr ⟨i, rfl⟩, fun st m m' hm => ?_,
    fun _ _ _ _ => funext fun b => b.elim, fun _ _ _ => rfl, fun st m m' hm => ?_,
    fun _ _ _ _ => funext fun b => b.elim, fun _ _ => rfl⟩
  · funext a X
    show Alg.mle (fun b => m (Q.I.tAt b)) _ = Alg.mle (fun b => m' (Q.I.tAt b)) _
    rw [funext fun b => hm (Q.I.tAt b) (Or.inl (h.bits _ _))]
  · funext a X
    show Alg.mle (fun b => m (Q.I.tAt b)) _ = Alg.mle (fun b => m' (Q.I.tAt b)) _
    rw [funext fun b => hm (Q.I.tAt b) fun i hi => h.dtB _ (h.bits _ _) ⟨i, hi⟩]

variable (E)

/-- Under the hypotheses below, the table's side is a link. -/
theorem mjl_segT (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E) (Dt In Rd : Q.I.J → Prop)
    (C : Q.I.X → (Q.I.J → E) → Prop) (h : Q.TabOK Dt In) (hRd : ∀ j, Q.srT Dt In j → Rd j)
    (hC : ∀ x k, C x k → Q.R.Holds x k) (hCb : ∀ x k, C x k → Bits Q.I.d Q.I.w (Q.I.bit k))
    (hsF : ∀ l < Q.I.d, MjStab C (Q.D.ownAt l)) (hsE : MjStab C Q.ownE) (hsB : MjStab C Q.ownB) :
    (Q.mjSegT Ex Wp Kc msg Rd).Link (Q.segT Ex Wp Kc msg).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (Q.srT Dt In) Q.swT C := by
  have srF : ∀ j,
      (∃ l' < Q.I.d, Q.D.srAt Dt In l' j) → Dt j ∨ In j ∨ Q.ownF j := fun j ⟨l', h1, hj⟩ =>
    hj.elim Or.inl fun hj =>
      Or.inr (hj.elim Or.inl fun ⟨l'', h2, ho⟩ => Or.inr ⟨l'', Nat.lt_of_le_of_lt h2 h1, ho⟩)
  have h1 := mjl_forest E Q Ex M Wp Kc msg Dt In Rd C hC Q.I.d h.lev
    (fun l' hl j hj =>
      hRd j ((srF j ⟨l', hl, hj⟩).elim Or.inl fun a =>
          Or.inr (a.elim Or.inl fun b => Or.inr (Or.inl b)))) hsF
  have dFE : ∀ j, (∃ l' < Q.I.d, Q.D.srAt Dt In l' j) → ¬ Q.ownE j := fun j hj =>
    (srF j hj).elim (h.dtE j) fun a => a.elim (h.inE j) (h.fE j)
  have dFB : ∀ j, (∃ l' < Q.I.d, Q.D.srAt Dt In l' j) → ¬ Q.ownB j := fun j hj =>
    (srF j hj).elim (h.dtB j) fun a => a.elim (h.inB j) (h.fB j)
  have hE := mjl_our E Q.En.psc Ex Q.I.J (Equiv.refl _) (M × Wp) (fun w => msg w.1) Rd
    (fun j => Dt j ∨ In j ∨ Q.ownF j ∨ Q.ownE j) (ldLkpEnd_vars E Q.En).1 (ldLkpEnd_degX E Q.En)
    (ldLkpEnd_degY E Q.En) (Q.end_own h)
    (fun j hj =>
      hRd j (hj.elim Or.inl fun a =>
          Or.inr (a.elim Or.inl fun b => Or.inr (b.elim Or.inl fun c => Or.inr (Or.inl c)))))
    ((Q.mjForest Ex Wp Kc msg Rd Q.I.d).sp C)
    (fun x k hx =>
      (ldLkpEnd_sum E Q.En x k).2
        ((ldLkpInst_topT_iff E Q.I Q.wE Q.cE x k).1
          (mjsp_forest E Q Ex M Wp Kc msg Rd C hC Q.I.d x k hx)))
    (mjst_sp hsE h1.reads dFE)
  have h12 := mjl_seq h1 hE dFE hsE
  have d12B : ∀ j, ((∃ l' < Q.I.d, Q.D.srAt Dt In l' j) ∨ (Dt j ∨ In j ∨ Q.ownF j ∨ Q.ownE j)) →
      ¬ Q.ownB j := fun j hj =>
    hj.elim (dFB j) fun a =>
      a.elim (h.dtB j) fun b => b.elim (h.inB j) fun c => c.elim (h.fB j) (h.eB j)
  have s2 : MjStab
      (((Q.mjForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.mjJ Ex (Equiv.refl _) Rd)).sp C) Q.ownB :=
    mjst_sp hsB h12.reads d12B
  have hB2 := mjl_our E Q.Bt.zc.next Ex Q.I.J (Equiv.refl _) (M × Wp) (fun w => msg w.1) Rd
    (fun j => Dt j ∨ Q.ownB j) (ldZero_vars E Q.Bt.zc).1 (ldLkpBit_degX E Q.Bt)
    (ldLkpBit_degY E Q.Bt) (Q.bit_own h)
    (fun j hj => hRd j (hj.elim Or.inl fun a => Or.inr (Or.inr (Or.inr (Or.inr a)))))
    ((Q.Bt.zc.toIn.mj Ex).sp
      (((Q.mjForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.mjJ Ex (Equiv.refl _) Rd)).sp C))
    (by
      rintro _ k ⟨o, ρ, hc, rfl⟩
      have hb : Bits Q.I.d Q.I.w (Q.I.bit k) :=
        mjsp_keeps _ (P := fun k => Bits Q.I.d Q.I.w (Q.I.bit k)) hCb o k hc
      exact pscIn_fwd E Q.Bt.zc.toIn (ldZero_link E Q.Bt.zc) o ρ.1 k
        ((ldZero_all E Q.Bt.zc o k).2
          ((ldLkpBit_zero E Q.Bt o k).2 ((ldLkpInst_bits E Q.I _ Q.wB Q.cB k).2 hb))))
    (mjst_sp s2 (Sr := fun _ => False) (fun _ _ _ _ _ => rfl) fun _ hh => hh.elim)
  have hB := mjl_seq
    (mjl_draw Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex (M × Wp) Q.Bt.zc.toIn.AllHold
      (((Q.mjForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.mjJ Ex (Equiv.refl _) Rd)).sp C)
      fun w => mjCut Rd (msg w.1))
    hB2 (fun _ hh => hh.elim) s2
  refine mjl_mono
    (mjl_seq h12 hB (fun j hj hw => hw.elim id (d12B j hj))
      (mjst_mono hsB fun j hw => hw.elim False.elim id))
    (fun j hj => ?_) fun j hj => ?_
  · rcases hj with (hj | hj) | hj | hj
    · exact (srF j hj).elim Or.inl fun a => Or.inr (a.elim Or.inl fun b => Or.inr (Or.inl b))
    · exact hj.elim Or.inl fun a =>
        Or.inr (a.elim Or.inl fun b => Or.inr (b.elim Or.inl fun c => Or.inr (Or.inl c)))
    · exact hj.elim
    · exact hj.elim Or.inl fun a => Or.inr (Or.inr (Or.inr (Or.inr a)))
  · rcases hj with (hj | hj) | hj | hj
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact hj.elim
    · exact Or.inr (Or.inr hj)

end Closers
end Cb
