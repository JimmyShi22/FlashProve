-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldFoldProofs.lean: the proofs of the statements of Cb/Ld/LdBldFold.lean (the fold of one
stage from numbers and two codes; the packing in one fixed order). Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs. What is said and what is
not: the head of that file.
-/
import Cb.Ld.LdBldFold
import Cb.Ld.LdSumPackProofs

set_option autoImplicit false

namespace Cb.Bld
open Prob

theorem bld_colCt : Spec.bld_colCt := by
  intro h g m
  unfold colCt
  ring

theorem bld_colNo : Spec.bld_colNo := fun _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem bld_fin : Spec.bld_fin := fun _ _ h =>
  ⟨Fin.val_injective, fun c hc => ⟨⟨c, lt_of_lt_of_le hc h⟩, rfl⟩⟩

section
variable {E : Type} [Field E] {J : Type}

theorem pkN_of_lt (h g m : ℕ) (idx : J → ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E)
    (β : Fin h → Bool) (j : J) (hc : idx j < colCt h g m) :
    pkN h g m idx W (β, j) = pkC h g m W (β, (colNo h g m).symm ⟨idx j, hc⟩) := dif_pos hc

theorem pkN_of_ge (h g m : ℕ) (idx : J → ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E)
    (β : Fin h → Bool) (j : J) (hc : ¬ idx j < colCt h g m) : pkN h g m idx W (β, j) = 0 :=
  dif_neg hc

theorem QwN_of_lt (h g m : ℕ) (idx : J → ℕ) (z : Fin (h + g) → E)
    (j : J) (hc : idx j < colCt h g m) :
    QwN h g m idx z j = QwC h g m z ((colNo h g m).symm ⟨idx j, hc⟩) := dif_pos hc

theorem QwN_of_ge (h g m : ℕ) (idx : J → ℕ) (z : Fin (h + g) → E)
    (j : J) (hc : ¬ idx j < colCt h g m) : QwN h g m idx z j = 0 := dif_neg hc

end

theorem bld_at (E : Type) [Field E] : Spec.bld_at E := by
  intro h g m J _ _ idx hN
  choose f hf using fun c : Fin (colCt h g m) => hN.2 c.val c.isLt
  have hfi : Function.Injective fun c => f (colNo h g m c) := fun c c' e =>
    (colNo h g m).injective
      (Fin.ext (by rw [← hf (colNo h g m c), ← hf (colNo h g m c')]; exact congrArg idx e))
  have back : ∀ (j : J) (hc : idx j < colCt h g m),
      f (colNo h g m ((colNo h g m).symm ⟨idx j, hc⟩)) = j := fun j hc =>
    hN.1 (by rw [Equiv.apply_symm_apply, hf])
  have off : ∀ (j : J), ¬ idx j < colCt h g m → ∀ c, f (colNo h g m c) ≠ j := fun j hc c e =>
    hc (by rw [← e, hf]; exact (colNo h g m c).isLt)
  refine ⟨fun c => f (colNo h g m c), hfi, fun c => hf _, ?_, ?_⟩
  · funext W a
    obtain ⟨β, j⟩ := a
    show pkN h g m idx W (β, j) =
      placeV (fun c => f (colNo h g m c)) (fun c => pkC h g m W (β, c)) j
    by_cases hc : idx j < colCt h g m
    · have e : placeV (fun c => f (colNo h g m c)) (fun c => pkC h g m W (β, c))
            (f (colNo h g m ((colNo h g m).symm ⟨idx j, hc⟩))) = _ :=
        placeV_at hfi _ _
      rw [back j hc] at e
      rw [pkN_of_lt h g m idx W β j hc, e]
    · rw [pkN_of_ge h g m idx W β j hc]
      exact (Finset.sum_eq_zero fun c _ => if_neg (off j hc c)).symm
  · funext z j
    show QwN h g m idx z j = placeV (fun c => f (colNo h g m c)) (QwC h g m z) j
    by_cases hc : idx j < colCt h g m
    · have e : placeV (fun c => f (colNo h g m c)) (QwC h g m z)
            (f (colNo h g m ((colNo h g m).symm ⟨idx j, hc⟩))) = _ :=
        placeV_at hfi _ _
      rw [back j hc] at e
      rw [QwN_of_lt h g m idx z j hc, e]
    · rw [QwN_of_ge h g m idx z j hc]
      exact (Finset.sum_eq_zero fun c _ => if_neg (off j hc c)).symm

theorem bld_law (E : Type) [Field E] : Spec.bld_law E := by
  intro h g m J _ idx hN
  classical
  obtain ⟨plc, hp, _, e1, e2⟩ := bld_at E h g m J idx hN
  rw [e1, e2]
  exact ld_pack_place E h g (m + 1) _ _ plc _ _ hp (ld_pack_law E h g m)

theorem bld_deg (E : Type) [Field E] : Spec.bld_deg E := by
  intro h g m J idx j
  by_cases hc : idx j < colCt h g m
  · simp only [QwN_of_lt h g m idx _ j hc]
    exact ld_pack_deg E h g m _
  · simp only [QwN_of_ge h g m idx _ j hc]
    exact Alg.DegLE.const _ 0

theorem bld_inj (E : Type) [Field E] : Spec.bld_inj E := by
  intro h g m J idx hN W W' e
  refine ld_pack_inj E h g m (funext fun a => ?_)
  obtain ⟨β, c⟩ := a
  obtain ⟨j, hj⟩ := hN.2 (colNo h g m c).val (colNo h g m c).isLt
  have hc : idx j < colCt h g m := hj ▸ (colNo h g m c).isLt
  have e1 := congrFun e (β, j)
  rw [pkN_of_lt h g m idx W β j hc, pkN_of_lt h g m idx W' β j hc] at e1
  have e2 : (colNo h g m).symm ⟨idx j, hc⟩ = c := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext hj
  rw [e2] at e1
  exact e1

theorem bld_fold (E : Type) [Field E] [Fintype E] : Spec.bld_fold E := by
  intro P h g m C Z AaW TW srcW idx hm hN St sl
  refine ⟨fun _ _ e => e, Nat.succ_le_succ hm, ?_, ?_⟩
  · exact (ld_pack_ok_iff E P _).2 (bld_law E h g m Z.J idx hN)
  · exact bld_deg E h g m Z.J idx

end Cb.Bld
