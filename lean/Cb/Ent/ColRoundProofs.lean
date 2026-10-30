-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/ColRoundProofs.lean: the proofs of the statements of Cb/Ent/ColRound.lean: a round of columns
and the maps that cut them.

All seven by unfolding, with `Carry.tr_id`, `Carry.fib_id` (Iop/CarryProofs.lean) for the later
rounds and the two laws of a string (`Round.IsPoint.rd_ofSyms`, `ofSyms_rd`).

Main names: one theorem for each statement, of the same name.

Limits: those in the head of Cb/Ent/ColRound.lean.

Terms: lean/GLOSSARY.md.

-/
import Cb.Ent.ColRound
import Iop.CarryProofs

set_option autoImplicit false

namespace Cb
open Iop Prob

theorem ldEnt_col_tr : Spec.ldEnt_col_tr := by
  intro r W L pt t τ
  obtain ⟨m, c, τ⟩ := τ
  show (some c).bind (fun c' =>
    ((Carry.id t).tr τ).map fun τ' => ((L.main pt m.1, m.2), c', τ')) = _
  rw [Carry.tr_id]
  rfl

theorem ldEnt_col_fib : Spec.ldEnt_col_fib := fun _ _ _ _ t =>
  ⟨fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
    fun _ _ => Carry.fib_id t⟩

theorem ldEnt_col_chal : Spec.ldEnt_col_chal := fun _ _ _ _ => rfl

theorem ldEnt_col_read : Spec.ldEnt_col_read := fun _ _ _ pt _ q => pt.rd_ofSyms _ q

theorem ldEnt_col_join : Spec.ldEnt_col_join := fun _ _ _ pt o _ => ⟨pt.ofSyms_rd o, rfl⟩

theorem ldEnt_col_whole : Spec.ldEnt_col_whole := by
  intro r W L pt o
  funext p
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · obtain ⟨q, rfl⟩ := q
    exact pt.rd_ofSyms _ q
  · obtain ⟨q, rfl⟩ := q
    rfl

theorem ldEnt_col_riderAt : Spec.ldEnt_col_riderAt := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

end Cb
