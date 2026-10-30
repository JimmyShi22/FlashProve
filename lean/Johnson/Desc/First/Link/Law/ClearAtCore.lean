-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ClearAtCore.lean: THE TABLE's TEST laysClear
(Johnson/Desc/First/Borders.lean: no open item that a sub-protocol does not close reads a component
of the witness that the sub-protocol's extractor lays) BY THE KERNEL AT THE WRITTEN CORE AND THE
WRITTEN SEATS' NUMBERS OF THE FULL SIZE (P5T.N0Full · P5T.arrOf P5T.seatsAllFull,
Johnson/P5T/PlanSeatsFull.lean). Theorems.

  laysClear_told   withRows and withTold turn rowsAt, treesAt, msgsAt and indexNo alone, which the
                   test does not read: by definition
  clear_full       **BY THE KERNEL: the test accepts at the written values**
  clear_one_fails, clear_unkept_fails   two tests that fail, by the kernel: with every message under
                   the number 0; with nothing kept

Limits. THE WRITTEN VALUES ALONE: the tie to At.arr Zp and At.N Zp cF is another file's. The full
size alone. No soundness statement.

-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.RowsAtPlan
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (Numbers ModelPart Item flatPlacesOf start laysClear)

theorem laysClear_told (arr : ℕ → ℕ → ℕ) (N : Numbers) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ)
    (n : ℕ) (ps : List Place) (told : List (List Oracle)) (links : List ModelPart) (pl : List Place)
    (O : List Item) :
    laysClear arr ((N.withRows s t n).withTold ps told) links pl O = laysClear arr N links pl O :=
  rfl

set_option maxRecDepth 1000000 in
/-- **At the written values of the full size.** -/
theorem clear_full : laysClear (P5T.arrOf P5T.seatsAllFull) P5T.N0Full linksFull
    (flatPlacesOf linksFull true) (start linksFull) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem clear_one_fails : laysClear (fun _ _ => 0) P5T.N0Full linksFull
    (flatPlacesOf linksFull true) (start linksFull) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem clear_unkept_fails : laysClear (P5T.arrOf P5T.seatsAllFull)
    { P5T.N0Full with keptOf := fun _ => [] } linksFull
    (flatPlacesOf linksFull true) (start linksFull) = false := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.laysClear_told
#print axioms VerifiableInference.Desc.LinkJoin.clear_full
#print axioms VerifiableInference.Desc.LinkJoin.clear_one_fails
#print axioms VerifiableInference.Desc.LinkJoin.clear_unkept_fails
