-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/SeedsRoomAll.lean: the proposition `SeedsRoom` (OnBytes/K/Oracle/SeedsRoom.lean: at
the shape of tables of the plan that the planner returns, the seeds of a table's record take at most
2^31 bytes) holds at all files: at every plan that the planner returns, on whatever files. No
premise.

Why. The format's rule R4.11 lays the record's seeds into the input of which the commitment ID is
the hash: 24 bytes for each element. Theorems that tie the hash over the realised oracle to the
direct call ask that this input lie in the hash's domain: `id_leafO`
(OnBytes/K/Oracle/LeavesDigests.lean [not in this library]) asks it as a premise on the shape.
`digestsO_of_within` (the same file) and `recordCrosses` (OnBytes/K/Oracle/SpineRecord.lean
[not in this library]) pay that premise by `seedsRoom`, at the plan's shape of tables, and carry
none on the seeds themselves. This file applies the theorem nowhere and turns no other theorem.

How. At every plan that the planner returns, the shape of tables has at most 4 answers, and the
point of the record's sample at most 32 coordinates (`planned_table`,
OnBytes/Model/Fit/TableFew.lean). So the seeds have at most 4 * 33 elements, which take at most
3,168 bytes.

Main theorem: `seedsRoom`.

Limits: a bound at every plan that the planner returns, at that plan's shape of tables
(`Chains.tableShape`) alone: of an ID that is formed at another shape nothing is said
(OnBytes/ShellOf/EntryBody.lean [not in this library] forms one at the shape in the entry's chain).
On files at which the planner refuses it says nothing: there is no plan. That the planner returns at
any files is shown by no term here (see the head of OnBytes/Model/Fit/TableFew.lean).
`Verify.planned` is the planner at the program's own hash: a like bound at the planner over a monad,
or at `Tie.plannedAt` under a given digest, is not paid here. `OnBytes.K.Left.SeedsFit`
(OnBytes/K/Left/SeedsAt.lean) is another proposition: nothing of it is paid here. Nothing on
soundness. For proofs only.
The program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.SeedsRoom
import OnBytes.Model.Fit.TableFew

set_option autoImplicit false

namespace OnBytes.K.Oracle

/-- **At every plan that the planner returns, on whatever files, the record's seeds take at most
2^31 bytes.** Where the planner refuses there is no plan, and nothing is said. -/
theorem seedsRoom (pol KL : ByteArray) (layout : Option ByteArray) : SeedsRoom pol KL layout := by
  intro p hp
  obtain ⟨a, c⟩ := OnBytes.Model.Verify.planned_table hp
  have m : p.chains.tableShape.answers * (p.chains.tableShape.cubeBits + 1) ≤ 4 * 33 :=
    Nat.mul_le_mul a (Nat.succ_le_succ c)
  exact Nat.le_trans (Nat.mul_le_mul_left 24 m) (by omega)

end OnBytes.K.Oracle

#print axioms OnBytes.K.Oracle.seedsRoom
