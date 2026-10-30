-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanRowsProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanRows.lean
(a finite family of rows on all entries, closed by one whole test for each group).
Named tools: `LdLinC.upA_val` (the value of a form on what the preamble left, lifted to all
entries). Nothing is defined here that a statement reads.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldRowsQ_nil : Spec.ldRowsQ_nil := fun _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun _ _ _ _ => ⟨fun _ b => isEmptyElim b, fun _ => trivial⟩,
    fun _ _ _ _ => ⟨fun _ b => isEmptyElim b, fun _ => trivial⟩,
    fun _ _ => trivial⟩

theorem ldRowsQ_cons : Spec.ldRowsQ_cons := by
  intro E _ _ S E₀ Wp Cl B _ rows tg X rest hS hR
  have key : ∀ (cl : Cl) (m : S.Msg),
      (Slf.All X.run.sl (fun b => tg cl b.1, fun _ => cl) (X.G.msg m) ∧
        rowsHold X.rest (fun cl b => tg cl b.1) cl
          ((S.sub X.kp).ents (S.res (T := OMsg.Msg) X.kp m))) ↔
      rowsHold rows tg cl (S.ents m) := by
    intro cl m
    have e1 : ∀ b, X.now b → ((rows b).onG X.G).val cl (X.G.msg m) = (rows b).val cl (S.ents m) :=
      fun b hb => ldPeel_onG E S X.G Cl (rows b) cl m fun n hn => hS.mine b hb cl n hn
    have e2 : ∀ b, ¬ X.now b →
        ((rows b).onSub X.kp).val cl ((S.sub X.kp).ents (S.res (T := OMsg.Msg) X.kp m)) =
          (rows b).val cl (S.ents m) :=
      fun b hb => ldPeel_onSub E S X.kp Cl (rows b) cl m fun n hn => hS.other b hb cl n hn
    constructor
    · rintro ⟨h1, h2⟩ b
      by_cases hb : X.now b
      · exact (e1 b hb).symm.trans (h1 ⟨b, hb⟩)
      · exact (e2 b hb).symm.trans (h2 ⟨b, hb⟩)
    · intro h
      exact ⟨fun b => (e1 b.1 b.2).trans (h b.1), fun b => (e2 b.1 b.2).trans (h b.1)⟩
  refine ⟨fun cl y m wp => ?_, fun cl y m wp => ?_, fun cl y => hR.on cl y⟩
  · rw [← key cl m, ← hR.rel cl y (S.res (T := OMsg.Msg) X.kp m) wp]
    exact Iff.rfl
  · rw [← key cl m, ← hR.relR cl y (S.res (T := OMsg.Msg) X.kp m) wp]
    exact Iff.rfl

theorem ldRowsQ_ok : Spec.ldRowsQ_ok := fun E _ _ S E₀ Wp _ _ _ _ _ X rest h1 h2 =>
  ldChain_cons E S E₀ Wp X.run rest.Q X.d X.d' h1 h2

theorem ldRowsQ_demand : Spec.ldRowsQ_demand := fun E _ _ S E₀ Wp _ _ _ _ _ X rest q₀ b' h =>
  ldDemand_cons E S E₀ Wp X.run rest.Q X.d X.d' q₀ b' h

theorem LdLinC.upA_val {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) {St : Type}
    (sl : Slf E St C.Sa.Ent) (st : St) (m : C.S.Msg) :
    (C.upA sl).val st (C.S.ents m) = sl.val st (C.Sa.ents (C.aM m)) := by
  show ∑ n : (Σ o : ((C.Sa.O ⊕ C.NW.O) ⊕ C.NU.O) ⊕ C.NO.O, (C.S.om o).C.J),
      C.upA sl st n * m n.1 n.2 =
    ∑ n : (Σ a, (C.Sa.om a).C.J), sl st n * m (.inl (.inl (.inl n.1))) n.2
  rw [Fintype.sum_sigma, Fintype.sum_sigma, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  have z1 : ∑ a : C.NO.O, ∑ j : (C.S.om (.inr a)).C.J, C.upA sl st ⟨.inr a, j⟩ * m (.inr a) j = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j _ => zero_mul _
  have z2 : ∑ a : C.NU.O,
        ∑ j : (C.S.om (.inl (.inr a))).C.J, C.upA sl st ⟨.inl (.inr a), j⟩ * m (.inl (.inr a)) j =
      0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j _ => zero_mul _
  have z3 : ∑ a : C.NW.O, ∑ j : (C.S.om (.inl (.inl (.inr a)))).C.J,
        C.upA sl st ⟨.inl (.inl (.inr a)), j⟩ * m (.inl (.inl (.inr a))) j = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j _ => zero_mul _
  rw [z1, z2, z3, add_zero, add_zero, add_zero]
  rfl

theorem ldRowsQ_saysA : Spec.ldRowsQ_saysA := by
  intro E ι κ J Y _ C p B rowsA tgA R hrel hrelR hk hR
  have s1 : ∀ b st (n : C.S.Ent), ¬ p.kp₁ n.1 → C.upA (rowsA b) st n = 0 := by
    rintro b st ⟨((a | a) | a) | a, j⟩ hn
    · by_contra hne
      exact hn (hk b st a j hne).1
    · rfl
    · rfl
    · rfl
  have s2 : ∀ b st (n : p.S₁.Ent), ¬ p.kp₂ n.1 → ((C.upA (rowsA b)).onSub p.kp₁) st n = 0 := by
    rintro b st ⟨⟨((a | a) | a) | a, h⟩, j⟩ hn
    · by_contra hne
      exact hn (hk b st a j hne).2
    · rfl
    · rfl
    · rfl
  have key : ∀ sa (m : C.S.Msg),
      rowsHold (p.rowsL rowsA) tgA sa (p.S₂.ents (p.last m)) ↔
      rowsHold rowsA tgA sa (C.Sa.ents (C.aM m)) := by
    intro sa m
    have e : ∀ b, (p.rowsL rowsA b).val sa (p.S₂.ents (p.last m)) =
        (rowsA b).val sa (C.Sa.ents (C.aM m)) := fun b =>
      (ldPeel_onSub E p.S₁ p.kp₂ C.Sta ((C.upA (rowsA b)).onSub p.kp₁) sa
          (C.S.res (T := OMsg.Msg) p.kp₁ m) fun n hn => s2 b sa n hn).trans
        ((ldPeel_onSub E C.S p.kp₁ C.Sta (C.upA (rowsA b)) sa m fun n hn => s1 b sa n hn).trans
          (C.upA_val (rowsA b) sa m))
    exact ⟨fun h b => (e b).symm.trans (h b), fun h b => (e b).trans (h b)⟩
  exact ⟨fun sa y m wp h => (hR.rel sa y _ wp).2 ((key sa m).2 ((hrel sa y _ wp).1 h)),
    fun sa y m wp _ h => (hrelR sa y _ wp).2 ((key sa m).1 ((hR.relR sa y _ wp).1 h)),
    fun sa y _ => hR.on sa y⟩

end Cb
