-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectWfRowsProofs.lean: the proofs of the statements of Cb/Obj/LdObjectWfRows.lean (under
`EntAt`, what weights-formedness leaves beside the tensor row is a finite family of rows on named
places). By instantiation.
Nothing is defined here that a statement reads.
-/
import Cb.Obj.LdObjectWfRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOWfRows_more : Spec.ldOWfRows_more F E := by
  classical
  intro W nAt hE cl m
  have hrow : ∀ r : W.RB,
      (W.P.rowAt r.1.1 r.2 (W.P.stOf cl)).Holds (W.P.ent m) ↔
      (W.rRow cl r).Holds fun n => W.P.S.ents m (W.rPl nAt r n) := by
    intro r
    have e := ldRowsAt_cut E W.P.N (W.P.gR r.1.1 r.2) ((W.P.stOf cl).2.2 r.1.1 r.2) (W.P.ent m)
    have e2 : (fun n : W.RN r => W.P.S.ents m (W.rPl nAt r n)) = fun n : W.RN r => W.P.ent m n.1 :=
      funext fun n => (hE.ent m n.1).symm
    rw [e2]
    refine Iff.trans ?_ (Iff.trans e ?_)
    · have e0 : ∀ n, (W.P.rowAt r.1.1 r.2 (W.P.stOf cl)).cf n =
          if W.P.gR r.1.1 r.2 n then ((W.P.stOf cl).2.2 r.1.1 r.2).cf n else 0 := by
        intro n
        by_cases hg : W.P.gR r.1.1 r.2 n
        · rw [if_pos hg]
          exact if_pos hg
        · rw [if_neg hg]
          exact if_neg hg
      exact ⟨fun h => (Finset.sum_congr rfl fun n _ => by rw [e0 n]).symm.trans h,
        fun h => (Finset.sum_congr rfl fun n _ => by rw [e0 n]).trans h⟩
    · exact ⟨fun h => (Finset.sum_congr (by ext; simp) fun n _ => rfl).trans h,
        fun h => (Finset.sum_congr (by ext; simp) fun n _ => rfl).trans h⟩
  rw [show rowsHold (W.rowsA nAt) W.tgA cl (W.P.S.ents m) ↔
      ∀ r, (W.rRow cl r).Holds fun n =>
        W.P.S.ents m (W.rPl nAt r n)
          from ldRowsAt_hold E W.P.S W.P.Cl W.RB W.RN (W.rPl nAt) W.rRow cl m]
  constructor
  · intro h r
    exact (hrow r).1 (h r.1.1 (Nat.le_of_lt_succ r.1.2) r.2)
  · intro h f hf b
    exact (hrow ⟨⟨f, Nat.lt_succ_of_le hf⟩, b⟩).2 (h ⟨⟨f, Nat.lt_succ_of_le hf⟩, b⟩)

theorem ldOWfRows_ab : Spec.ldOWfRows_ab F E := fun W nAt hE =>
  ⟨fun sa _ m _ => ldOWfRows_more F E W nAt hE sa m,
    fun sa _ m _ => ldOWfRows_more F E W nAt hE sa m⟩

theorem ldOWfRows_read : Spec.ldOWfRows_read F E := by
  intro W nAt r cl e hne
  by_contra hno
  have h0 : W.rowsA nAt r cl e = 0 :=
    Slf.push_zero (W.rPl nAt r) (fun cl n => (W.rRow cl r).cf n) cl e fun n hn => hno ⟨n.1, n.2, hn⟩
  exact hne h0

theorem ldOWfRows_three : Spec.ldOWfRows_three F E := by
  intro W nAt p X w₀ hE hn hk hpl hX
  obtain ⟨h1, h2⟩ := ldOWfRows_ab F E W nAt hE
  refine ldRowsOne_three E _ _ _ _ W.O.toC p W.RB (W.rowsA nAt) W.tgA X w₀ (fun U => U = ∅)
    hn hk h1 h2 (fun r st a j hne => ?_) hX rfl
  obtain ⟨n, hg, hat⟩ := ldOWfRows_read F E W nAt r st ⟨a, j⟩ hne
  have ha : (nAt n).1 = a := congrArg Sigma.fst hat
  subst ha
  exact hpl r n hg

end
end Cb
