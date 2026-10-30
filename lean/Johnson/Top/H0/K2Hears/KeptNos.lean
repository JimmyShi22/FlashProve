-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeptNos.lean: the code switch: THE KEPT MEMBERS THAT THE SWITCH's
FRAME LISTS (OnBytes/Iop/Cs.lean's switchKept) ARE THE LAYOUT's MEMBERS AT KeptAtIndex.lean's
keptNos, IN ORDER.
  zip_filter        on lists: the first components of the pairs whose second is true are the entries
                    at the places at which the second list says true
  switchKept_list   the statement
  switchKept_at     by index
LIMITS. On lists of numbers alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.KeptAtIndex
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem zip_filter (d : Nat) : ∀ (M : List Nat) (K : List Bool),
    ((M.zip K).filter (·.2)).map (·.1) =
      ((List.range M.length).filter fun w => K.getD w false).map fun w => M.getD w d
  | [], _ => by simp
  | m :: M, [] => by simp
  | m :: M, k :: K => by
    have ih := zip_filter d M K
    rw [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons]
    cases k
    · simp only [List.filter_cons, List.getD_cons_zero, Bool.false_eq_true, if_false,
        List.filter_map, List.map_map]
      rw [ih]
      rfl
    · simp only [List.filter_cons, List.getD_cons_zero, if_true, List.map_cons, List.filter_map,
        List.map_map]
      rw [ih]
      rfl

/-- **The frame's kept members are the layout's members at keptNos.** -/
theorem switchKept_list (old : SingleRows) :
    (switchKept old).toList = (keptNos old.layout).map fun w => old.layout.members.getD w 0 := by
  unfold switchKept keptNos
  have h := zip_filter 0 old.layout.members.toList old.layout.kept.toList
  simpa using h

theorem switchKept_at (old : SingleRows) (a w : Nat) (hw : (keptNos old.layout)[a]? = some w) :
    (switchKept old)[a]? = some (old.layout.members.getD w 0) := by
  rw [← Array.getElem?_toList, switchKept_list, List.getElem?_map, hw]
  rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.switchKept_at
