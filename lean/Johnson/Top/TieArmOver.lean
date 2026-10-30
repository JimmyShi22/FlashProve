-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieArmOver.lean: the tie of the entry file in the form in which a verifier that is
stated arm by arm asks it: the entry file's arm as one algorithm over the one hash function, run at
Lean's BLAKE2b.

Johnson/Top/TieArm.lean ends at the run of the arm `armL` at the typed oracle functions that the
coding `r.m` reads out of Lean's BLAKE2b. A description arm by arm holds each arm as an algorithm
that asks the one hash function itself. Here the arm of an `ArmIn` is written so (`ArmIn.armE`:
`armL` through `r.m`), and `EntryPart` (OnBytes/K/Parts.lean) at `r.shape` gives two statements on
it, each in the spelling "for all files, options, ID and tables at which the program says yes".

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean).

Main definitions and theorems.
 `ArmIn.armE`      the entry file's arm at r over the one hash function: the two seeds' tests and
                   Link's compiled verifier without the test of the strict format, each typed query
                   written as a bit string by `r.m`.
 `armE_det`        run at a function g, it returns what `armL` returns at what `r.m` reads out of g.
 `records_of_entryPart`  on a served statement the program's two tables are read as records.
 `entry_of_entryPart`    on a served statement, at the records of the program's two tables, the
                   fixed reading gives the program's own further table and a typed string, and
                   `r.armE`, run at Lean's BLAKE2b, says yes.

What is not claimed. `EntryPart r.shape R` is a hypothesis here; where it is proved, and at which r,
the files that prove it say. No description arm by arm is named in this file: that its entry file's
arm is `r.armE` at some r is for the file that writes such a description. The lax Link, not the
strict format. The coding `r.m` is r's own; nothing says that it serves another arm. All that the
heads of Johnson/Top/TieArm.lean and OnBytes/K/Parts.lean do not claim. For proofs only; the program
does not import this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.TieArm

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)

/-- The entry file's arm at r, as an algorithm over the one hash function. -/
def ArmIn.armE (r : ArmIn) (cm cm' : Dig 256) (c c' : r.L.Rec) (π : OneProtocolProof 256 (batLC r.L r.aL)) :
    Rom.OComp (rom 256) Bool :=
  (armL r.W r.Sd r.cA (cm, cm', c, c', π)).overOne r.m

/-- Run at a function g, the arm over the one hash function returns what `armL` returns at what
`r.m` reads out of g. -/
theorem armE_det (r : ArmIn) (g : Fam (rom 256)) (cm cm' : Dig 256) (c c' : r.L.Rec)
    (π : OneProtocolProof 256 (batLC r.L r.aL)) :
    (r.armE cm cm' c c' π).det g =
      (armL r.W r.Sd r.cA (cm, cm', c, c', π)).det (readBlocks r.m g) :=
  Rom.det_overOne _ _ _

/-- On a served statement the program's two tables are read as records. -/
theorem records_of_entryPart (r : ArmIn) (R : Reading5 r.shape) (A : EntryPart r.shape R) :
    ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
      r.Served (stmOf F o) →
      (∃ c, r.recOf (stmOf F o) table = some c) ∧ ∃ cj, r.recOf (stmOf F o) further = some cj :=
  fun F o id table further hi hb hp hs =>
    ⟨(A.seed0 F o id table further hi hb hp hs).imp fun _ h => h.1,
      (A.seed1 F o id table further hi hb hp hs).imp fun _ h => h.1⟩

/-- On a served statement the entry file's arm over the one hash function, run at Lean's BLAKE2b,
says yes on what the fixed reading gives. -/
theorem entry_of_entryPart (r : ArmIn) (R : Reading5 r.shape) (A : EntryPart r.shape R) :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 → PortYesAt F id table further →
      r.Served (stmOf F o) → r.recOf (stmOf F o) table = some c →
      r.recOf (stmOf F o) further = some cj →
      ∃ πL, R.ent (stmOf F o) F.key F.ent = some (further, πL) ∧
        (r.armE (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
          (fun _ => oBits ()) = true := by
  intro F o id table further c cj hi hb hp hs hc hcj
  obtain ⟨c0, hc0, s0⟩ := A.seed0 F o id table further hi hb hp hs
  obtain ⟨c1, hc1, s1⟩ := A.seed1 F o id table further hi hb hp hs
  have hc0 : r.recOf (stmOf F o) table = some c0 := hc0
  have hc1 : r.recOf (stmOf F o) further = some c1 := hc1
  obtain rfl : c0 = c := Option.some.inj (hc0.symm.trans hc)
  obtain rfl : c1 = cj := Option.some.inj (hc1.symm.trans hcj)
  obtain ⟨πL, he, vl⟩ := A.link F o id table further c0 c1 hi hb hp hs hc0 hc1
  refine ⟨πL, he, ?_⟩
  have s0 : (outOfDomainSeedIs r.W r.Sd (bytesToDig table.root) c0.1).det (readBlocks r.m oBits) = true := s0
  have s1 : (outOfDomainSeedIs r.W r.Sd (bytesToDig further.root) c1.1).det (readBlocks r.m oBits) = true :=
    s1
  have vl : (vLA' r.W r.cA (bytesToDig table.root) (bytesToDig further.root) c0 c1 πL).det
    (readBlocks r.m oBits) = true := vl
  rw [armE_det]
  show (VLA' r.W r.Sd r.cA (bytesToDig table.root) (bytesToDig further.root) c0 c1 πL).det
    (readBlocks r.m oBits) = true
  unfold VLA'
  simp only [OComp.det_bind]
  rw [s0, s1, vl]
  rfl

end OnBytes.K
