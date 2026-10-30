-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/TablesHeld.lean: **the four comparisons of public tables' digests in `publicOfO`
return**, at the second hash function and at the stored example's tables, AT EVERY SCAN OF A
PARAMETER FILE `VerifierAndGoals.policyFile v`, whatever the eight free numbers v.
  `expectedOf tbl t`: `PolScan.tableExpected`'s text as a function of the 32 words alone.
  `expectedOf_ref`: a closed fact by Lean's kernel: the library's own 32 written words
    (`VerifierAndGoals.Lines.tableWordsRef`, Johnson/Goal/Meaning/ScopeScan.lean) spell the four written
    digests `Silu.D`, `Fs.D`, `Rope.D`, `Exp.D`.
  `expected_of_scan`: so does `P.tableExpected`, where `polScan (policyFile v) = .ok P`
    (`VerifierAndGoals.Lines.scan_closed`).
  **`silu_held`, `fs_held`, `rope_held`, `exp_held`**: by `tableHeldO_iff`
    (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) and the four digests.
Limits. That the scan returns is a premise here: Johnson/Unfolds/TablesInScope.lean pays it at all
public files in the goals' scope. That the layout made of P gives the numbers at which these tables
are made is not said here: for 8, 4095, routed experts, the gate's clamp and 12, 500000, 128, 10:
Johnson/Unfolds/TablesAtLayout.lean; for the exponentials' 12, 8: nowhere yet. At `secondHashFunction` alone.

-/
import Johnson.Unfolds.Silu.Digest
import Johnson.Unfolds.Fs.Digest
import Johnson.Unfolds.Rope.Digest
import Johnson.Unfolds.Exp.Digest
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Goal.Meaning.ScopeScan

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Layer
open VerifiableInference.PlanWritten
open VerifierAndGoals (FreeLines policyFile)
open VerifierAndGoals.Lines (tableWordsRef scan_closed)

/-- `PolScan.tableExpected`'s text as a function of the words alone. -/
def expectedOf (tbl : Array Nat) (t : PublicTable) : Option ByteArray :=
  if tbl.size == 32 then
    some (Fmt.cat ((tbl.extract (8 * t.index) (8 * t.index + 8)).toList.map word32))
  else none

theorem tableExpected_eq (P : PolScan) (t : PublicTable) :
    P.tableExpected t = expectedOf P.tblPol t := rfl

/-- A closed fact by Lean's kernel: the library's written words spell the four written digests. -/
theorem expectedOf_ref :
    expectedOf tableWordsRef.toArray .silu = some Silu.D ∧
      expectedOf tableWordsRef.toArray .sigmoid = some Fs.D ∧
      expectedOf tableWordsRef.toArray .rope = some Rope.D ∧
      expectedOf tableWordsRef.toArray .exp = some Exp.D := by
  decide +kernel

section
variable {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
include h

theorem tblPol_of_scan : P.tblPol = tableWordsRef.toArray := by
  rw [scan_closed h]
  rfl

theorem expected_of_scan :
    P.tableExpected .silu = some Silu.D ∧ P.tableExpected .sigmoid = some Fs.D ∧
      P.tableExpected .rope = some Rope.D ∧ P.tableExpected .exp = some Exp.D := by
  simp only [tableExpected_eq, tblPol_of_scan h]
  exact expectedOf_ref

theorem silu_held (p3 gcl : Bool) :
    tableHeldO secondHashFunction P .silu (gateTables 8 4095 p3 gcl).1 = .ok () :=
  (tableHeldO_iff secondHashFunction P .silu _).2 fun d e => by
    rw [(expected_of_scan h).1] at e
    rw [← Option.some.inj e]
    exact (Silu.silu_digest p3 gcl).symm

theorem fs_held : tableHeldO secondHashFunction P .sigmoid (gateTables 8 4095 true true).2 = .ok () :=
  (tableHeldO_iff secondHashFunction P .sigmoid _).2 fun d e => by
    rw [(expected_of_scan h).2.1] at e
    rw [← Option.some.inj e]
    exact Fs.fs_digest.symm

theorem rope_held : tableHeldO secondHashFunction P .rope (ropeTable 12 500000 128 10) = .ok () :=
  (tableHeldO_iff secondHashFunction P .rope _).2 fun d e => by
    rw [(expected_of_scan h).2.2.1] at e
    rw [← Option.some.inj e]
    exact Rope.rope_digest.symm

theorem exp_held (Tt : Array Nat) (ht : OnBytes.Attention.expTable 12 8 = some Tt) :
    tableHeldO secondHashFunction P .exp Tt = .ok () :=
  (tableHeldO_iff secondHashFunction P .exp _).2 fun d e => by
    rw [(expected_of_scan h).2.2.2] at e
    rw [← Option.some.inj e]
    exact (Exp.exp_digest Tt ht).symm

end

end Johnson.Unfolds

#print axioms Johnson.Unfolds.tableExpected_eq
#print axioms Johnson.Unfolds.expectedOf_ref
#print axioms Johnson.Unfolds.tblPol_of_scan
#print axioms Johnson.Unfolds.expected_of_scan
#print axioms Johnson.Unfolds.silu_held
#print axioms Johnson.Unfolds.fs_held
#print axioms Johnson.Unfolds.rope_held
#print axioms Johnson.Unfolds.exp_held
