-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPutLkpProofs.lean: the proofs of the statements of Cb/Ld/LdLkpMaskPutLkp.lean.
-/
import Cb.Ld.LdLkpMaskPutLkp
import Cb.Ld.LdLkpMaskPutProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- One step of the tie. -/
theorem ldLkpPl_tieAt (D : TieP E) (Ex : ExtSpec) (Rd : D.J → Prop) (l : ℕ)
    (hi : Function.Injective (Sum.elim (D.lv l).T.wAt (D.lv l).T.cAt)) :
    (D.plAt Ex Rd l).OK ∧ ∀ j, (D.plAt Ex Rd l).At j ↔ D.ownAt l j := by
  obtain ⟨h1, h2⟩ := mjPl_our E (D.lv l).T Ex D.J (D.eJ l) Rd hi
  obtain ⟨h3, h4⟩ := mjPl_post E D.J _ _ _ _ _ _ _ _ ((D.lv l).T.plJ Ex (D.eJ l) Rd)
    (fun o => some (D.nxt l o)) (ExtMap.id Ex) (D.nxt l) h1
  exact ⟨h3, fun j => (h4 j).trans (h2 j)⟩

theorem ldLkpPl_tie : Spec.ldLkpPl_tie E := by
  intro D Ex M Wp Kc msg Rd Dt n h
  have ha : ∀ l ≤ n, ∀ j, (D.plAt Ex Rd l).At j ↔ D.ownAt l j := fun l hl =>
    (ldLkpPl_tieAt E D Ex Rd l (h.inj l hl)).2
  refine ⟨mjPl_chain E D.J Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg)
      (fun l => D.mjAt Ex Rd l) (fun l => D.plAt Ex Rd l) n
      (fun l hl => (ldLkpPl_tieAt E D Ex Rd l (h.inj l hl)).1) fun l l' hll hl' j hj hj' => ?_,
    fun j => ?_⟩
  · exact h.disj l l' hll hl' j ((ha l (le_trans (le_of_lt hll) hl') j).1 hj) ((ha l' hl' j).1 hj')
  · refine (mjPl_at_chain E D.J Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg)
        (fun l => D.mjAt Ex Rd l) (fun l => D.plAt Ex Rd l) n j).trans
      ⟨fun ⟨l, hl, hj⟩ => ⟨l, hl, (ha l hl j).1 hj⟩, fun ⟨l, hl, hj⟩ => ⟨l, hl, (ha l hl j).2 hj⟩⟩

/-- One level of a tree. -/
theorem ldLkpPl_lev (D : TreeP E) (Ex : ExtSpec) (Rd : D.J → Prop) (l : ℕ)
    (hi : Function.Injective (Sum.elim (D.lv l).T.wAt (D.lv l).T.cAt)) :
    (D.plLev Ex Rd l).OK ∧ ∀ j, (D.plLev Ex Rd l).At j ↔ D.ownAt l j := by
  obtain ⟨h1, h2⟩ := mjPl_our E (D.lv l).T Ex D.J (D.eJ l) Rd hi
  obtain ⟨h3, h4⟩ :=
    mjPl_silent E D.J _ _ (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex fun _ _ => True
  refine ⟨mjPl_seq E D.J _ _ _ _ _ _ _ _ _ _ _ _ h1 h3 fun j _ => h4 j, fun j => ?_⟩
  refine (mjPl_at_seq E D.J _ _ _ _ _ _ _ _ _ _ ((D.lv l).T.plJ Ex (D.eJ l) Rd)
    (MJ.Pl.silent (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex fun _ _ => True)
    j).trans ?_
  exact ⟨fun h => h.elim (h2 j).1 fun h => absurd h (h4 j), fun h => Or.inl ((h2 j).2 h)⟩

theorem ldLkpPl_tree : Spec.ldLkpPl_tree E := by
  intro D Ex M Wp Kc msg Rd Dt In n h
  have ha : ∀ l ≤ n, ∀ j, (D.plLev Ex Rd l).At j ↔ D.ownAt l j := fun l hl =>
    (ldLkpPl_lev E D Ex Rd l (h.inj l hl)).2
  refine ⟨mjPl_chain E D.J Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg)
      (fun l => D.mjLev Ex Rd l) (fun l => D.plLev Ex Rd l) n
      (fun l hl => (ldLkpPl_lev E D Ex Rd l (h.inj l hl)).1) fun l l' hll hl' j hj hj' => ?_,
    fun j => ?_⟩
  · exact h.disj l l' hll hl' j ((ha l (le_trans (le_of_lt hll) hl') j).1 hj) ((ha l' hl' j).1 hj')
  · refine (mjPl_at_chain E D.J Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg)
        (fun l => D.mjLev Ex Rd l) (fun l => D.plLev Ex Rd l) n j).trans
      ⟨fun ⟨l, hl, hj⟩ => ⟨l, hl, (ha l hl j).1 hj⟩, fun ⟨l, hl, hj⟩ => ⟨l, hl, (ha l hl j).2 hj⟩⟩

theorem ldLkpPl_head : Spec.ldLkpPl_head E := by
  intro H Ex M Wp Kc msg Rd Dt h
  obtain ⟨h1, h2⟩ := ldLkpPl_tie E H.tie Ex M Wp Kc msg Rd Dt H.n h
  obtain ⟨h3, h4⟩ := mjPl_pre E H.J _ _ _ _ _ _ _ _ (H.tie.plTie Ex M Wp Kc msg Rd H.n)
    (fun x => some ((0 : E), x)) (ExtMap.id Ex) (fun x => ((0 : E), x)) h1
  obtain ⟨h5, h6⟩ := mjPl_silent E H.J _ _ E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True
  refine ⟨mjPl_seq E H.J _ _ _ _ _ _ _ _ _ _ _ _ h5 h3 fun j hj => absurd hj (h6 j), fun j => ?_⟩
  refine (mjPl_at_seq E H.J _ _ _ _ _ _ _ _ _ _
    (MJ.Pl.silent E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True)
    ((H.tie.plTie Ex M Wp Kc msg Rd H.n).pre (fun x => some ((0 : E), x))
      (ExtMap.id Ex) fun x => ((0 : E), x)) j).trans ?_
  exact ⟨fun h => h.elim (fun h => absurd h (h6 j)) fun h => (h2 j).1 ((h4 j).1 h),
    fun h => Or.inr ((h4 j).2 ((h2 j).2 h))⟩

theorem ldLkpPl_segK : Spec.ldLkpPl_segK E := by
  intro I v' tK Ex M Wp Kc msg Rd Dt In h
  obtain ⟨h1, h2⟩ := ldLkpPl_tree E (I.setV (v' + 1)).DK Ex M Wp Kc msg Rd Dt In v' h
  obtain ⟨h3, h4⟩ := mjPl_pre E I.J _ _ _ _ _ _ _ _
    ((I.setV (v' + 1)).DK.plTree Ex M Wp Kc msg Rd v')
    (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex) (enterK (I.setV (v' + 1)) tK) h1
  exact ⟨h3, fun j => (h4 j).trans (h2 j)⟩

theorem ldLkpPl_forest : Spec.ldLkpPl_forest E := by
  intro Q Ex M Wp Kc msg Rd Dt In l
  induction l with
  | zero =>
      intro _
      obtain ⟨h1, h2⟩ := mjPl_silent E Q.I.J _ _ Q.R.toIn.ev.D Q.R.toIn.nxX Ex Q.R.toIn.AllHold
      exact ⟨h1,
        fun j => ⟨fun h => absurd h (h2 j), fun ⟨_, hl, _⟩ => absurd hl (Nat.not_lt_zero _)⟩⟩
  | succ l ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun l' hl' => h l' (Nat.lt_succ_of_lt hl')
      have hl := h l (Nat.lt_succ_self l)
      obtain ⟨h3, h4⟩ := ldLkpPl_lev E Q.D Ex Rd l (hl.inj l (le_refl _))
      refine ⟨mjPl_seq E Q.I.J _ _ _ _ _ _ _ _ _ _ (Q.plForest Ex Wp Kc msg Rd l)
          (Q.D.plLev Ex Rd l) h1 h3 fun j hj hj' => ?_,
        fun j => ?_⟩
      · obtain ⟨l', hl', hj⟩ := (h2 j).1 hj
        exact hl.disj l' l hl' (le_refl _) j hj ((h4 j).1 hj')
      · refine (mjPl_at_seq E Q.I.J _ _ _ _ _ _ _ _ _ _ (Q.plForest Ex Wp Kc msg Rd l)
          (Q.D.plLev Ex Rd l) j).trans ?_
        constructor
        · rintro (hj | hj)
          · obtain ⟨l', hl', hj⟩ := (h2 j).1 hj
            exact ⟨l', Nat.lt_succ_of_lt hl', hj⟩
          · exact ⟨l, Nat.lt_succ_self l, (h4 j).1 hj⟩
        · rintro ⟨l', hl', hj⟩
          rcases Nat.lt_or_ge l' l with h5 | h5
          · exact Or.inl ((h2 j).2 ⟨l', h5, hj⟩)
          · obtain rfl := Nat.le_antisymm (Nat.lt_succ_iff.1 hl') h5
            exact Or.inr ((h4 j).2 hj)

theorem ldLkpPl_segT : Spec.ldLkpPl_segT E := by
  intro Q Ex M Wp Kc msg Rd Dt In h
  obtain ⟨f1, f2⟩ := ldLkpPl_forest E Q Ex M Wp Kc msg Rd Dt In Q.I.d h.lev
  obtain ⟨e1, e2⟩ := mjPl_our E Q.En.psc Ex Q.I.J (Equiv.refl _) Rd h.injE
  obtain ⟨s1, s2⟩ :=
    mjPl_silent E Q.I.J _ _ Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.AllHold
  obtain ⟨b1, b2⟩ := mjPl_our E Q.Bt.zc.next Ex Q.I.J (Equiv.refl _) Rd h.injB
  have e3 : ∀ j, (Q.En.psc.plJ Ex (Equiv.refl _) Rd).At j ↔ Q.ownE j := e2
  have b3 : ∀ j, (Q.Bt.zc.next.plJ Ex (Equiv.refl _) Rd).At j ↔ Q.ownB j := b2
  have f3 : ∀ j, (Q.plForest Ex Wp Kc msg Rd Q.I.d).At j ↔ Q.ownF j := f2
  have a1 := mjPl_at_seq E Q.I.J _ _ _ _ _ _ _ _ _ _
    (Q.plForest Ex Wp Kc msg Rd Q.I.d) (Q.En.psc.plJ Ex (Equiv.refl _) Rd)
  have a2 := mjPl_at_seq E Q.I.J _ _ _ _ _ _ _ _ _ _
    (MJ.Pl.silent Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.AllHold)
    (Q.Bt.zc.next.plJ Ex (Equiv.refl _) Rd)
  have o1 := mjPl_seq E Q.I.J _ _ _ _ _ _ _ _ _ _ (Q.plForest Ex Wp Kc msg Rd Q.I.d)
    (Q.En.psc.plJ Ex (Equiv.refl _) Rd) f1 e1 fun j hj hj' => h.fE j ((f3 j).1 hj) ((e3 j).1 hj')
  have o2 := mjPl_seq E Q.I.J _ _ _ _ _ _ _ _ _ _
    (MJ.Pl.silent Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.AllHold)
    (Q.Bt.zc.next.plJ Ex (Equiv.refl _) Rd) s1 b1 fun j hj => absurd hj (s2 j)
  have hb : ∀ j,
      ((MJ.Pl.silent Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.AllHold).seq
        (Q.Bt.zc.next.plJ Ex (Equiv.refl _) Rd)).At j ↔
      Q.ownB j := fun j =>
    (a2 j).trans
      ⟨fun hj => hj.elim (fun hj => absurd hj (s2 j)) (b3 j).1, fun hj => Or.inr ((b3 j).2 hj)⟩
  have hfe : ∀ j,
      ((Q.plForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.plJ Ex (Equiv.refl _) Rd)).At j ↔
      Q.ownF j ∨ Q.ownE j :=
    fun j => (a1 j).trans (or_congr (f3 j) (e3 j))
  refine ⟨mjPl_seq E Q.I.J _ _ _ _ _ _ _ _ _ _ _ _ o1 o2 fun j hj hj' => ?_, fun j => ?_⟩
  · exact ((hfe j).1 hj).elim (fun hj => h.fB j hj ((hb j).1 hj')) fun hj =>
      h.eB j hj ((hb j).1 hj')
  · refine (mjPl_at_seq E Q.I.J _ _ _ _ _ _ _ _ _ _
      ((Q.plForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.plJ Ex (Equiv.refl _) Rd))
      ((MJ.Pl.silent Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.AllHold).seq
        (Q.Bt.zc.next.plJ Ex (Equiv.refl _) Rd)) j).trans ?_
    exact (or_congr (hfe j) (hb j)).trans or_assoc

theorem ldLkpPl_asm : Spec.ldLkpPl_asm E := by
  intro A Ex M Wp Kc msg Rd Dt h
  obtain ⟨t1, t2⟩ := ldLkpPl_head E A.H Ex M Wp Kc msg Rd Dt h.tie
  obtain ⟨k1, k2⟩ := ldLkpPl_segK E A.IK A.v' A.tK Ex M Wp Kc msg Rd Dt A.swTie h.keyT
  obtain ⟨q1, q2⟩ := ldLkpPl_segT E A.Q Ex M Wp Kc msg Rd Dt A.swTie h.tab
  have t3 : ∀ j, (A.H.plHead Ex M Wp Kc msg Rd).At j ↔ A.swTie j := t2
  have k3 : ∀ j, (plSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd).At j ↔ A.swK j := k2
  have a1 := mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _ (A.H.plHead Ex M Wp Kc msg Rd)
    (plSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd)
  have o1 := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ (A.H.plHead Ex M Wp Kc msg Rd) (plSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd) t1 k1 fun j hj hj' => by
    obtain ⟨l, hl, hk⟩ := (k3 j).1 hj'
    exact h.keyT.io l hl j ((t3 j).1 hj) hk
  have htk : ∀ j,
      ((A.H.plHead Ex M Wp Kc msg Rd).seq (plSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd)).At j ↔
      A.swTie j ∨ A.swK j :=
    fun j => (a1 j).trans (or_congr (t3 j) (k3 j))
  have hTT : ∀ j, A.swTie j → ¬ A.Q.swT j := by
    rintro j hj (⟨l, hl, hf⟩ | he | hb)
    · exact (h.tab.lev l hl).io l (le_refl _) j hj hf
    · exact h.tab.inE j hj he
    · exact h.tab.inB j hj hb
  have o2 : (A.plChain Ex M Wp Kc msg
      Rd).OK := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ _ _ o1 q1 fun j hj hj' =>
    ((htk j).1 hj).elim (fun hj => hTT j hj ((q2 j).1 hj')) fun hj => h.kT j hj ((q2 j).1 hj')
  have a2 : ∀ j, (A.plChain Ex M Wp Kc msg Rd).At j ↔ A.swAll j := fun j => by
    refine (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _
      ((A.H.plHead Ex M Wp Kc msg Rd).seq (plSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd))
      (A.Q.plSegT Ex Wp Kc msg Rd) j).trans ?_
    exact (or_congr (htk j) (q2 j)).trans or_assoc
  obtain ⟨p1, p2⟩ := mjPl_post E A.J _ _ _ _ _ _ _ _ (A.plChain Ex M Wp Kc msg Rd)
    (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd o2
  exact ⟨⟨o2, a2⟩, p1, fun j => (p2 j).trans (a2 j)⟩

end
end Cb
