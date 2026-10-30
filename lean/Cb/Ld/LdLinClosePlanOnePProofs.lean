-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanOnePProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanOneP.lean
(the technical report's plan: "the rest" as one more test on one group).
Nothing is defined here.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanOneP.lean):
  `ldRowsQP_saysA`: what a closing R of the rows `p.rowsL rowsA` says
  `ldRowsOneP_three`: one test X on all that is left, with all rows
  `ldRowsOneP_v`: the honest side `X.oneVP N q₀ w₀`, for a batch
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdLinClosePlanOneP

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldRowsQP_saysA : Spec.ldRowsQP_saysA := by
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
      exact hn (hk b st a j hne).2.1
    · rfl
    · rfl
    · rfl
  have s3 : ∀ b st (n : p.S₂.Ent),
      ¬ p.kp₃ n.1 → (((C.upA (rowsA b)).onSub p.kp₁).onSub p.kp₂) st n = 0 := by
    rintro b st ⟨⟨⟨((a | a) | a) | a, h⟩, h'⟩, j⟩ hn
    · by_contra hne
      exact hn (hk b st a j hne).2.2
    · rfl
    · rfl
    · rfl
  have key : ∀ sa (m : C.S.Msg),
      rowsHold (p.rowsL rowsA) tgA sa (p.S₃.ents (p.last₃ m)) ↔
      rowsHold rowsA tgA sa (C.Sa.ents (C.aM m)) := by
    intro sa m
    have e : ∀ b, (p.rowsL rowsA b).val sa (p.S₃.ents (p.last₃ m)) =
        (rowsA b).val sa (C.Sa.ents (C.aM m)) := fun b =>
      (ldPeel_onSub E p.S₂ p.kp₃ C.Sta (((C.upA (rowsA b)).onSub p.kp₁).onSub p.kp₂) sa
          (p.left₂ m) fun n hn => s3 b sa n hn).trans
        ((ldPeel_onSub E p.S₁ p.kp₂ C.Sta ((C.upA (rowsA b)).onSub p.kp₁) sa
            (C.S.res (T := OMsg.Msg) p.kp₁ m) fun n hn => s2 b sa n hn).trans
          ((ldPeel_onSub E C.S p.kp₁ C.Sta (C.upA (rowsA b)) sa m fun n hn => s1 b sa n hn).trans
            (C.upA_val (rowsA b) sa m)))
    exact ⟨fun h b => (e b).symm.trans (h b), fun h b => (e b).trans (h b)⟩
  exact ⟨fun sa y m wp h => (hR.rel sa y _ wp).2 ((key sa m).2 ((hrel sa y _ wp).1 h)),
    fun sa y m wp _ h => (hrelR sa y _ wp).2 ((key sa m).1 ((hR.relR sa y _ wp).1 h)),
    fun sa y _ => hR.on sa y⟩

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldRowsOneP_three : Spec.ldRowsOneP_three E ι κ J Y := by
  intro C p B _ rowsA tgA X w₀ q₀ hn hk hrel hrelR hkeep hX hq
  haveI : IsEmpty {b // ¬ X.now b} := ⟨fun b => b.2 (hn b.1)⟩
  haveI : IsEmpty (p.S₃.sub X.kp).O := ⟨fun o => hk o.1 o.2⟩
  have hS : (X.one tgA w₀).Says :=
    ldRowsQ_cons E p.S₃ C.E₀ C.Wpa C.Sta B (p.rowsL rowsA) tgA X _ (X.supp_all hn hk)
      (ldRowsQ_nil E _ C.E₀ C.Wpa C.Sta _ X.rest (fun cl b => tgA cl b.1) w₀)
  refine ⟨ldRowsQP_saysA E ι κ J Y C p B rowsA tgA (X.one tgA w₀) hrel hrelR hkeep hS,
    ldRowsQ_ok E p.S₃ C.E₀ C.Wpa C.Sta B (p.rowsL rowsA) tgA X _ hX (ldChain_nil E _ C.E₀ C.Wpa w₀),
    fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := ldRowsQ_demand E p.S₃ C.E₀ C.Wpa C.Sta B (p.rowsL rowsA) tgA X _ q₀
    (fun _ => 0) (ldDemand_nil E _ C.E₀ C.Wpa w₀ q₀ _ hq) V hV
  exact ⟨h1,
    fun o =>
      (h2 o).trans
        ((ldDemand_le E p.S₃ X.run (fun _ => 0) o).trans (by rw [dif_neg (hk o)]; exact le_refl _))⟩

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldRowsOneP_v : Spec.ldRowsOneP_v E ι κ J Y := by
  intro C p Cl B _ rows X w₀ N q₀ hk hX hq
  haveI : IsEmpty (p.S₃.sub X.kp).O := ⟨fun o => hk o.1 o.2⟩
  refine ldPlanV_cons_local E p.S₃ C.E₀ C.Wpa N X.run (LdTcA.nil (p.S₃.sub X.kp) C.E₀ C.Wpa w₀)
    X.d X.d'
    ⟨C.P.Sh6, fun _ _ _ _ => True, p.S₃.qV (fun a => C.isSh a.1.1.1) (QFam.each q₀) (X.bOneP N)⟩
    (fun _ _ _ _ => True) (X.qEndP N q₀) (LdTcV.nil (p.S₃.sub X.kp) C.E₀ C.Wpa w₀ _) hX ?_
    (fun _ _ _ _ => trivial) ?_ ?_
  · exact ldPlanV_nil E _ C.E₀ C.Wpa w₀ N _ fun Jn =>
      ldDemandV_empty E _ _ N _ _ _ (fun _ _ => hq) Jn
  · exact ldRunV_bears_local E p.S₃ X.run _ _ _ _ X.d X.d' N _ _ hX
      (ldDemandV_local E p.S₃ X.run _ _ _ _ X.d X.d' N (fun a => C.isSh a.1.1.1)
        (QFam.each q₀) (fun _ => 0) _ hX)
  · exact ldDemandV_her E _ _ N _ _ _ ((qfam_her _ extNone N).1 _)

end
end Cb
