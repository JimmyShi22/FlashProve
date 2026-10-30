-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpInstProofs.lean: proofs for Cb/Ld/LdLkpInst.lean (the two product trees of the lookup as
instances (of `TreeP`, Cb/Ld/LdLkpTreeP.lean); what their roots and their tops say).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdLkpInst.lean):
  `ldLkpInst_stepK`, `ldLkpInst_stepT`: the tree's one condition, for the keys' tree (K) and the
    table's forest (T).
  `ldLkpInst_rootK`: level 0 of the keys' tree: the product over the keys.
  `ldLkpInst_rootT`: level 0 of the table's forest: the product over the table at a bit position.
  `ldLkpInst_topK`: the top of the keys' tree (level v: the leaves).
  `ldLkpInst_topT_iff`: the sum claim at the top of the forest (level d): the closing block's claim.
  `ldLkpInst_topT`: the tree's joint at level d: the closing block's input joint.
  `ldLkpInst_bits`: the bit test's claim: all bits are bits.

Limits: what the head of Cb/Ld/LdLkpInst.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpInst
import Cb.Ld.LdLkpNumProofs
import Cb.Gen.LkpAlgProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

theorem numLE_surj {k c : ℕ} (hc : c < 2 ^ k) : ∃ b : Fin k → Bool, numLE b = c :=
  ⟨revCube k (Alg.bits k c), by rw [numLE_revCube, Alg.num_bits hc]⟩

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpInst_stepK : Spec.ldLkpInst_stepK E := fun I x m l b =>
  ldLkpNum_step E 0 I.v (facK (I.key (I.st x) m) (I.lam x)) l b
theorem ldLkpInst_stepT : Spec.ldLkpInst_stepT E := fun I x m l b =>
  ldLkpNum_step E I.w I.d (facT I.w (I.tab (I.st x)) (I.bit m) (I.lam x)) l b

theorem ldLkpInst_rootK : Spec.ldLkpInst_rootK E := fun I x m θ =>
  ldLkpNum_rootK E I.v (I.key (I.st x) m) (I.lam x) θ
theorem ldLkpInst_rootT : Spec.ldLkpInst_rootT E := fun I x m θ =>
  ldLkpNum_rootT E I.w I.d (I.tab (I.st x)) (I.bit m) (I.lam x) θ

omit [Fintype E] in
theorem ext_zero_add (v : ℕ) (a p : ℕ → E) : Blocks.ext (0 + v) a p = Blocks.ext v a p := by
  rw [Nat.zero_add]

theorem ldLkpInst_topK : Spec.ldLkpInst_topK E := by
  intro I x m
  rw [ldLkpP_sum E I.DK (ldLkpInst_stepK E I) I.v x m]
  have hU : I.DK.U ((I.DK.lv I.v).base x.2) m I.v =
      fun b : Fin (0 + I.v) → Bool =>
        facK (I.key (I.st ((I.DK.lv I.v).base x.2)) m) (I.lam ((I.DK.lv I.v).base x.2)) (numLE b) :=
    funext fun b => ldLkpNum_top E 0 I.v _ b
  have hm : Alg.mle (I.DK.U ((I.DK.lv I.v).base x.2) m I.v) ((I.DK.lv I.v).pnt x.2) =
      Blocks.ext I.v
        (facK (I.key (I.st ((I.DK.lv I.v).base x.2)) m) (I.lam ((I.DK.lv I.v).base x.2)))
        (Blocks.nat fun i : Fin (0 + I.v) => (I.DK.lv I.v).pnt x.2 i.rev) := by
    rw [hU]
    exact (ldLkpNum_ext E (0 + I.v) _ ((I.DK.lv I.v).pnt x.2)).trans (ext_zero_add E I.v _ _)
  have hp := ldLkpP_push E _ _ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) m
  rw [hm, ← hp]
  show _ ↔ Blocks.ext I.v (I.key (I.st ((I.DK.lv I.v).base x.2)) m)
          (Blocks.nat fun i : Fin (0 + I.v) => (I.DK.lv I.v).pnt x.2 i.rev) +
        ∑ j, (- pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j) * m j =
      I.lam ((I.DK.lv I.v).base x.2) - x.1
  simp only [neg_mul, Finset.sum_neg_distrib]
  constructor
  · intro h
    have h' := (key_end E I.v _ _ (I.lam ((I.DK.lv I.v).base x.2)) _).1 (eq_sub_of_add_eq h)
    rw [h']
    ring
  · intro h
    have h' := (key_end E I.v (I.key (I.st ((I.DK.lv I.v).base x.2)) m)
        (Blocks.nat fun i : Fin (0 + I.v) => (I.DK.lv I.v).pnt x.2 i.rev)
        (I.lam ((I.DK.lv I.v).base x.2))
        (x.1 - ∑ j, pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j * m j)).2
      (by linear_combination h)
    rw [h']
    ring

theorem ldLkpInst_topT_iff : Spec.ldLkpInst_topT_iff E := by
  intro I wE cE x m
  rw [ldLkpP_sum E I.DT (ldLkpInst_stepT E I) I.d x m]
  have hU : I.DT.U ((I.DT.lv I.d).base x.2) m I.d =
      fun b : Fin (I.w + I.d) → Bool => 1 + m (I.tAt b) * (I.endB wE cE).cp x.2 b :=
    funext fun b => ldLkpNum_topT E I.w I.d _ _ _ b
  rw [hU, ← ldLkpP_push E _ _ (I.DT.lv I.d).toJ ((I.DT.lv I.d).T.slS x.2) m]
  exact Iff.rfl

theorem ldLkpInst_topT : Spec.ldLkpInst_topT E := fun I wE cE _ _ _ _ msg _ =>
  LdLkp.rels_ext (funext fun x =>
      funext fun _ =>
        funext fun w => propext (and_congr_right fun _ => ldLkpInst_topT_iff E I wE cE x (msg w.1)))
    (funext fun a =>
      funext fun w => propext (and_congr_right fun _ => ldLkpInst_topT_iff E I wE cE a.1 (msg w.1)))
    rfl rfl

theorem ldLkpInst_bits : Spec.ldLkpInst_bits E := by
  intro I Sb wB cB m
  constructor
  · intro h u hu j hj
    have hlt : u * 2 ^ I.w + j < 2 ^ (I.w + I.d) := by
      have h1 : (u + 1) * 2 ^ I.w ≤ 2 ^ I.d * 2 ^ I.w := Nat.mul_le_mul_right _ hu
      rw [← pow_add, Nat.add_comm I.d I.w, Nat.succ_mul] at h1
      omega
    obtain ⟨b, hb⟩ := numLE_surj hlt
    have hq : numLE b / 2 ^ I.w = u := by
      rw [hb, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos I.w),
        Nat.div_eq_of_lt hj, Nat.zero_add]
    have hr : numLE b % 2 ^ I.w = j := by
      rw [hb, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have := h b
    show m (I.bAt u j) * (m (I.bAt u j) - 1) = 0
    rw [← hq, ← hr]
    exact this
  · intro h b
    refine h (numLE b / 2 ^ I.w) ?_ (numLE b % 2 ^ I.w) (Nat.mod_lt _ (Nat.two_pow_pos I.w))
    have hb : numLE b < 2 ^ (I.w + I.d) := ldLkpNum_lt _ b
    rw [pow_add] at hb
    exact Nat.div_lt_of_lt_mul hb

end
end Cb
