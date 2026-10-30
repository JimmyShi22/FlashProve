-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/OrderLays.lean: WHAT A YES OF THE CLOSING OF THE LIST OF TABLES LAYS: just the
list that it is handed, closed; every other field of the smallness test's record as it was. For
Johnson/Desc/First/K8/Order.lean's close.
NO RUNNING TEXT IMPORTS THIS FILE. Nothing on soundness is said.
  close_lays · close_funs · close_table
Limits. WHICH LIST THE STEP HANDS TO close IS NOT SAID HERE: that it is the list which the link's
own kind has heard is a law on the block that calls close.

-/
import Johnson.Desc.First.K8.OrderMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Order
open OnBytes OnBytes.Model

/-- A yes of close: the record with the mark laid and the handed list in the list's place. -/
theorem close_lays (tl tl' : HTailF2) (funs : Array HFun) (h : close tl funs = .ok tl') :
    tl' = { tl with funClosed := true, funs := funs } :=
  ((close_ok_iff tl tl' funs).mp h).2

/-- The list is the handed one, as a whole, and it is closed. -/
theorem close_funs (tl tl' : HTailF2) (funs : Array HFun) (h : close tl funs = .ok tl') :
    tl'.funs = funs ∧ tl'.funClosed = true := by
  rw [close_lays tl tl' funs h]
  exact ⟨rfl, rfl⟩

/-- Table for table, in all five fields. -/
theorem close_table (tl tl' : HTailF2) (funs : Array HFun) (h : close tl funs = .ok tl') :
    tl'.funs.size = funs.size ∧ ∀ i : Nat,
      (tl'.funs.getD i {}).mat = (funs.getD i {}).mat ∧
      (tl'.funs.getD i {}).len = (funs.getD i {}).len ∧
      (tl'.funs.getD i {}).phi = (funs.getD i {}).phi ∧
      (tl'.funs.getD i {}).tree = (funs.getD i {}).tree ∧
      (tl'.funs.getD i {}).start = (funs.getD i {}).start := by
  rw [(close_funs tl tl' funs h).1]
  exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

end VerifiableInference.Desc.First.K8.Order

#print axioms VerifiableInference.Desc.First.K8.Order.close_lays
#print axioms VerifiableInference.Desc.First.K8.Order.close_funs
#print axioms VerifiableInference.Desc.First.K8.Order.close_table
