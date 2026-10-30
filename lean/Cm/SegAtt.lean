-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAtt.lean: two statements on the keys and identities of the attention segment of group g, and
small facts for it.

Definitions, two statements and proofs.
A segment has the shape of its matrix of cells, its families of identities and its families of keys
with their tables; its conditions (`SegSpec.Holds`) are zero tests and table lookups at the
vertices of Boolean cubes: every identity is 0 at every vertex, every key is an entry of its table.
The attention segment of group g (four consecutive layers of the model) is segment 2 g + 1 of
Cm/SegLayout.lean. Its families come from Cm/SegAttKey.lean, Cm/SegAttKeySum.lean and
Cm/SegAttIdn.lean.
From Inst/Model/Att/Trace.lean: a trace is a function on the names of cells (`Raw`), and `Raw.Valid`
says which names are cells; a call c : Fin 4 has a table (`AttSeg.lut`) and a key vector
(`AttSeg.keyVec`), whose keys are the entries at the indices in pieces (below `AttSeg.Dim.used`);
the identities have the names `AttSeg.Idn` and the values `AttSeg.idnVal`. The table of scales is
the class argument `scl : Scl` (Inst/Model/Scl.lean).

Main names:
  `Spec.keyVec_agree`, `Spec.idnVal_agree`: keys and identities read valid names only (the
    identities: those with valid names). Proofs: Cm/SegAttAgree.lean, Cm/SegAttOK.lean.
The segment itself, over p = 2^64 - 2^32 + 1: Cm/TargetSegAtt.lean.
-/
import Cm.SegAttIdn
import Cm.RelBase

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.AttSeg (Raw Reg)

namespace Spec
/-- States: a key vector reads valid names only. -/
def keyVec_agree : Prop :=
  ∀ (scl : Scl) (u0 : ℕ) (tb : Tables) (t t' : Raw → ℤ), Agree t t' →
    ∀ (c : Fin 4) (X : ℕ),
      AttSeg.keyVec (scl := scl) (DU u0) tb t c X = AttSeg.keyVec (scl := scl) (DU u0) tb t' c X
/-- States: an identity with a valid name (`j.Valid DA`) reads valid names only. -/
def idnVal_agree : Prop :=
  ∀ (t t' : Raw → ℤ),
    Agree t t' → ∀ j : AttSeg.Idn, j.Valid DA → AttSeg.idnVal DA t j = AttSeg.idnVal DA t' j
end Spec

variable [scl : Scl]

/-- integer matrices, read as an integer trace of the attention segment of group g -/
def tMA (g : ℕ) (M : ℕ → ℕ → ℕ → ℤ) : Raw → ℤ := fun c => at' M (ownAtt g c).place

theorem rowsA (u0 : ℕ) (tb : Tables) (c : Fin 4) : (AttSeg.lut (DU u0) tb c).rows = 2 ^ 16 := by
  fin_cases c <;> rfl

omit scl in
theorem split_iff (P : ℕ → Prop) (a b : ℕ) :
    ((∀ B < a, P (0 + B)) ∧ ∀ B < b, P (a + B)) ↔ ∀ Y < a + b, P Y := by
  constructor
  · rintro ⟨h1, h2⟩ Y hY
    by_cases h : Y < a
    · simpa using h1 Y h
    · have := h2 (Y - a) (by omega)
      rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt h)] at this
  · exact fun H => ⟨fun B hB => H _ (by omega), fun B hB => H _ (by omega)⟩

end Cm.Seg
