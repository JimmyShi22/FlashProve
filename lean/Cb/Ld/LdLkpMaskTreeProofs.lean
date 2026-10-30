-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskTreeProofs.lean: proofs for Cb/Ld/LdLkpMaskTree.lean.

Main names (statements and hypotheses: Cb/Ld/LdLkpMaskTree.lean):
  `ldLkpMaskTree_own`: the places (`D.ownAt`), written out.
  `ldLkpMaskTree_link`: see its statement in Cb/Ld/LdLkpMaskTree.lean.
  `ldLkpMaskTree_mm`: see its statement in Cb/Ld/LdLkpMaskTree.lean.
  `ldLkpMaskTree_sound`: it speaks of the honest run of the tree; it says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskTree
import Cb.Ld.LdLkpMaskTieProofs
import Cb.Ld.LdLkpTreePProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E]

theorem LdLkp.TreeP.own_iff (D : TreeP E) :
    ∀ (l : ℕ) (j : D.J), D.ownAt l j ↔ (∃ i, j = D.wAt l i) ∨ ∃ b, j = D.cAt l b
  | 0, _ =>
    ⟨fun ⟨i, h⟩ => i.casesOn (fun i h => Or.inl ⟨i, h⟩) (fun b h => Or.inr ⟨b, h⟩) h,
      fun h => h.elim (fun ⟨i, h⟩ => ⟨.inl i, h⟩) fun ⟨b, h⟩ => ⟨.inr b, h⟩⟩
  | _ + 1, _ =>
    ⟨fun ⟨i, h⟩ => i.casesOn (fun i h => Or.inl ⟨i, h⟩) (fun b h => Or.inr ⟨b, h⟩) h,
      fun h => h.elim (fun ⟨i, h⟩ => ⟨.inl i, h⟩) fun ⟨b, h⟩ => ⟨.inr b, h⟩⟩

/-- The places of the two inner masks of level l are own places of level l. -/
theorem LdLkp.TreeP.c_own (D : TreeP E) (l : ℕ) (b : Bool) :
    D.ownAt l ((D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two b))) :=
  ⟨.inr ((D.lv l).two b), rfl⟩

theorem LdLkp.TreeP.sr_own (D : TreeP E) {n : ℕ} {Dt In : D.J → Prop} (h : D.MaskOK n Dt In)
    {l l' : ℕ} (h1 : l < l') (h2 : l' ≤ n) (j : D.J) (hj : D.srAt Dt In l j) : ¬ D.ownAt l' j := by
  rcases hj with hj | hj | ⟨l'', hl, hj⟩
  · exact h.dt l' h2 j hj
  · exact h.io l' h2 j hj
  · exact h.disj l'' l' (Nat.lt_of_le_of_lt hl h1) h2 j hj

/-- Under `h`: the conditions `OwnOur` of the item "masked messages" (`Honest.MM`, Ior/Masked.lean),
at the set `D.srAt Dt In l`, hold at every level l ≤ n. -/
theorem LdLkp.TreeP.own_our (D : TreeP E) {n : ℕ} {Dt In : D.J → Prop} (h : D.MaskOK n Dt In) :
    ∀ l ≤ n, (D.lv l).T.OwnOur fun j' => D.srAt Dt In l (D.eJ l j')
  | 0, hl => by
      refine ⟨h.inj 0 hl,
        fun i => Or.inr (Or.inr ⟨0, le_refl 0, i, rfl⟩),
        fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim,
        fun st j hj => h.inc st.1 st.2 j fun hi => hj (Or.inr (Or.inl hi)),
        fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim,
        fun st i => h.inc st.1 st.2 _ fun hi => h.io 0 hl _ hi ⟨i, rfl⟩⟩
      · have a := h.rd st.1 m m' fun j hj => hm j (Or.inl hj)
        funext (b : Bool) X
        show D.half st.1 m 0 b _ = D.half st.1 m' 0 b _
        unfold TreeP.half
        rw [a]
      · have a := h.rd st.1 m m' fun j hj => hm j fun i hi => h.dt 0 hl j hj ⟨i, hi⟩
        funext (b : Bool) X
        show D.half st.1 m 0 b _ = D.half st.1 m' 0 b _
        unfold TreeP.half
        rw [a]
  | l + 1, hl => by
      classical
      have hz : ∀ (st : (D.lv (l + 1)).T.St) (j : D.J),
          ¬ D.ownAt l j → (D.lv (l + 1)).T.slS st j = 0 := by
        intro st j hj
        show (D.lv l).T.lst st.1.st ((D.lv l).T.par.hp st.1.st st.1.pt) *
            ((if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) then 1 - st.2 else 0) +
              if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) then st.2 else 0) = 0
        have n0 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) := fun e =>
          hj (by rw [e]; exact D.c_own l false)
        have n1 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) := fun e =>
          hj (by rw [e]; exact D.c_own l true)
        rw [if_neg n0, if_neg n1, add_zero, mul_zero]
      refine ⟨h.inj (l + 1) hl,
        fun i => Or.inr (Or.inr ⟨l + 1, le_refl _, i, rfl⟩),
        fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim,
        fun st j hj => hz st j fun ho => hj (Or.inr (Or.inr ⟨l, Nat.le_succ l, ho⟩)),
        fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim,
        fun st i => hz st _ fun ho => h.disj l (l + 1) (Nat.lt_succ_self l) hl _ ho ⟨i, rfl⟩⟩
      · have a := h.rd ((D.lv l).base st.1.st) m m' fun j hj => hm j (Or.inl hj)
        funext (b : Bool) X
        show D.half ((D.lv l).base st.1.st) m (l + 1) b _ =
          D.half ((D.lv l).base st.1.st) m' (l + 1) b _
        unfold TreeP.half
        rw [a]
      · have a := h.rd ((D.lv l).base st.1.st) m m' fun j hj =>
          hm j fun i hi => h.dt (l + 1) hl j hj ⟨i, hi⟩
        funext (b : Bool) X
        show D.half ((D.lv l).base st.1.st) m (l + 1) b _ =
          D.half ((D.lv l).base st.1.st) m' (l + 1) b _
        unfold TreeP.half
        rw [a]

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpMaskTree_own : Spec.ldLkpMaskTree_own E := fun D l j => D.own_iff l j

/-- Under `h` and `hl`: the messages of a level read what the level's sumcheck reads (`srAt`). -/
theorem LdLkp.TreeP.lev_reads (D : TreeP E) (Ex : ExtSpec) (Rd : D.J → Prop) {n : ℕ}
    {Dt In : D.J → Prop} (h : D.MaskOK n Dt In) (l : ℕ) (hl : l ≤ n) :
    (D.mjLev Ex Rd l).MReads (D.srAt Dt In l) := by
  intro k k' x ρ hk
  show Plains.app (((D.lv l).T.mjJ Ex (D.eJ l) Rd).msg k x (Rho.fst ρ)) _ =
    Plains.app (((D.lv l).T.mjJ Ex (D.eJ l) Rd).msg k' x (Rho.fst ρ)) _
  rw [mjOur_reads E (D.lv l).T Ex D.J (D.eJ l) Rd (D.srAt Dt In l) (D.own_our h l hl) k k' x _ hk]
  rfl

/-- Under `hS` and `h`: after a level, at what the honest messages fix, the sum claim of the next
level holds. -/
theorem LdLkp.TreeP.next_sum (D : TreeP E) (hS : D.Step) (Ex : ExtSpec) (Rd : D.J → Prop)
    (l : ℕ) (C : E × (D.lv l).T.St → (D.J → E) → Prop) (x' : E × (D.lv (l + 1)).T.St)
    (k : D.J → E) (h : (D.mjLev Ex Rd l).sp C x' k) : D.sumAt (l + 1) x' k := by
  obtain ⟨o, ρ₂, ⟨x, ρ₁, -, rfl⟩, rfl⟩ := (mjsp_seq _ _ C x' k).1 h
  have ok := ldLkpP_ok E D l
  have h1 := (mjOur_out E (D.lv l).T Ex D.J (D.eJ l) Rd ok.1 ok.2.2.1 ok.2.2.2 k x ρ₁).1.2
  exact pscIn_fwd E (D.cube l).toLine.toIn
    (ldLine_link E (D.cube l).toLine
      (ldLineC_virt E (D.cube l) (ldLkpP_halves E D hS l)) (ldLineC_form E (D.cube l)))
    _ ρ₂.1 k fun b => h1 ((D.lv l).two b)

theorem ldLkpMaskTree_link : Spec.ldLkpMaskTree_link E := by
  intro D Ex M Wp Kc msg n Dt In Rd C hS hM hRd hC hCs
  refine mjl_chain (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg) (fun l => D.mjLev Ex Rd l) C
    (fun w => mjCut Rd (msg w.1)) (D.srAt Dt In) D.ownAt n (fun l hl => ?_)
    (fun l l' h1 h2 j hj => D.sr_own hM h1 h2 j hj) hCs
  have ok := ldLkpP_ok E D l
  refine mjl_mono
    (mjl_seq (mjl_our E (D.lv l).T Ex D.J (D.eJ l) (M × Wp) (fun w => msg w.1) Rd (D.srAt Dt In l)
        ok.1 ok.2.2.1 ok.2.2.2 (D.own_our hM l hl)
        (fun j hj =>
          hRd j (hj.elim Or.inl fun h =>
              Or.inr (h.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩)))
        _ ?_ ?_)
      (mjl_draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (M × Wp) (fun _ _ => True)
        _ fun w => mjCut Rd (msg w.1))
      (fun _ _ h => h) fun _ k k' hk hc => by rwa [← funext fun j => hk j fun h => h])
    (fun _ h => h.elim id False.elim) fun _ h => h.elim id False.elim
  · intro x k hx
    cases l with
    | zero => exact hC x k hx
    | succ l => exact D.next_sum E hS Ex Rd l _ x k hx
  · exact mjst_spTo (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg) (fun l => D.mjLev Ex Rd l) C
      (D.ownAt l) (D.srAt Dt In) (hCs l hl) l
      (fun l' h => D.lev_reads E Ex Rd hM l' ((Nat.le_of_lt h).trans hl))
      fun l' h j hj => D.sr_own hM h hl j hj

theorem ldLkpMaskTree_mm : Spec.ldLkpMaskTree_mm E := by
  intro D Ex M Wp Kc msg n Dt In Rd hS hM hRd
  refine mjl_mm
    (ldLkpMaskTree_link E D Ex M Wp Kc msg n Dt In Rd (D.sumAt 0) hS hM hRd
      (fun _ _ h => h) fun l hl x k k' hk hc => ?_)
  have a := hM.rd x.2.1 k k' fun j hj => hk j (hM.dt l hl j hj)
  have eF : D.T0.F x.2 k = D.T0.F x.2 k' := by
    funext (b : Bool) X
    show D.half x.2.1 k 0 b _ = D.half x.2.1 k' 0 b _
    unfold TreeP.half
    rw [a]
  have eS : D.T0.sum x.2 k = D.T0.sum x.2 k' := by
    funext X
    unfold PscOur.sum
    rw [eF]
    rfl
  have eI : ∑ j, D.inc0 x.2.1 x.2.2 j * k j =
      ∑ j, D.inc0 x.2.1 x.2.2 j * k' j := Finset.sum_congr rfl fun j _ => by
    by_cases hi : In j
    · rw [hk j (hM.io l hl j hi)]
    · rw [hM.inc x.2.1 x.2.2 j hi, zero_mul, zero_mul]
  show hSumAll (D.T0.vars x.2) (D.T0.sum x.2 k') + ∑ j, D.inc0 x.2.1 x.2.2 j * k' j = x.1
  rw [← eS, ← eI]
  exact hc

theorem ldLkpMaskTree_sound : Spec.ldLkpMaskTree_sound E := by
  intro D Ex Kc A0 n Dt In Rd C hS hM hRd hC0 hC hCs
  refine mjsp_good (b := D.treeA Ex Unit Kc (fun m => m) n)
    (ldLkpMaskTree_link E D Ex (D.J → E) Unit Kc (fun m => m) n Dt In Rd C hS hM hRd hC0 hCs)
    (fun w j ⟨l, hl, hj⟩ => mjCut_of w.1 (hRd j ?_))
    (plain_tree Ex (D.J → E) Unit Kc D (fun m => m) n)
    (ldLkpP_tree E D Ex (D.J → E) Unit Kc (fun m => m) A0 n hS) hC
  exact hj.elim Or.inl fun h =>
    Or.inr (h.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩)

end
end Cb
