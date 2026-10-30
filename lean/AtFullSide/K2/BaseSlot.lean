-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BaseSlot.lean: what a K of record asks of the lot baseSimLot of the kind "the code
switch" (K2): that a lot of the base filling bears its name, and that it has that lot's sides.

  lots_names_apart     the base filling's lots bear different names
  baseSimLot_named     a lot of the filling bears its name
  baseSimLot_fit       at a lot of that name its rows' sides are the lot's

By: lot_is_the_fillings, lot_toHLot. Names are public words.

Limits. Nothing on the simulators: these ask sides alone.
-/
import AtFullSide.K2.SimulatorAtTheBaseProof

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.Term ProofFile.Honest.K2 ProofFile.Honest.FirstFill
open AtPublicFiles.AtFiles AtPublicFiles.Cut

/-- The filling's lots, as a name. -/
abbrev baseLots := (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
  openHonest).lots

/-- **The base filling's lots bear different names.** -/
theorem lots_names_apart : (baseLots.map (·.name)).Nodup := by
  decide

theorem switch_lot_mem : switchFillLot matrixInput OnBytes.HonestTrace.Sz.ref ∈ baseLots := by
  unfold baseLots
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_map.2 ⟨(switchFillLot matrixInput OnBytes.HonestTrace.Sz.ref, .K2),
    List.Mem.tail _ (List.Mem.head _), rfl⟩

theorem name_eq : (switchFillLot matrixInput OnBytes.HonestTrace.Sz.ref).name = baseSimLot.name := rfl

/-- **A lot of the filling bears the lot's name.** -/
theorem baseSimLot_named : baseLots.any (fun L => L.name == baseSimLot.name) = true :=
  List.any_eq_true.2 ⟨_, switch_lot_mem, beq_iff_eq.2 name_eq⟩

/-- **At a lot of that name the rows' sides are the lot's.** -/
theorem baseSimLot_fit (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ L ∈ baseLots, L.name = baseSimLot.name →
      (baseSimLot.rows Z G).map (·.half) = L.halves Z G := by
  intro L hL e
  obtain rfl : L = switchFillLot matrixInput OnBytes.HonestTrace.Sz.ref :=
    List.inj_on_of_nodup_map lots_names_apart hL switch_lot_mem (e.trans name_eq.symm)
  have t : (baseSimLot.rows Z G).map (·.half) = baseSimLot.toHLot.halves Z G := rfl
  rw [t, lot_toHLot]
  rfl

end AtFullSide.K2

#print axioms AtFullSide.K2.lots_names_apart
#print axioms AtFullSide.K2.baseSimLot_named
#print axioms AtFullSide.K2.baseSimLot_fit
