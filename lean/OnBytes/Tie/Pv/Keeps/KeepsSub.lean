-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsSub.lean: the three calls of OnBytes/Model/Hide.lean that are written as
functions of the sub-proof's state and of the context. Each hands the context on as it is.
-/
import OnBytes.Tie.Pv.Keeps.KeepsLift
import OnBytes.Model.Hide

namespace OnBytes.L5

open OnBytes OnBytes.Model

instance keepsM_change (f : Fork → Option Fork) : KeepsM (SubM.change f) :=
  KeepsM.prim fun F c y c' h => by
    unfold SubM.change at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Kept.refl _

instance keepsM_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsM (SubM.take f) :=
  KeepsM.prim fun F c y c' h => by
    unfold SubM.take at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Kept.refl _

instance keepsM_ask {α : Type} (f : Fork → Option α) : KeepsM (SubM.ask f) :=
  KeepsM.prim fun F c y c' h => by
    unfold SubM.ask at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Kept.refl _

#print axioms keepsM_change
#print axioms keepsM_take
#print axioms keepsM_ask

end OnBytes.L5
