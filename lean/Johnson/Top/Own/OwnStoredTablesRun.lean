-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Own/OwnStoredTablesRun.lean: tests, run by Lean's evaluator at every build, that compare
the four public tables that the parameter file of `zStoredFull` names by digest, entry by entry,
with the numbers of the theorems' integer model. The build fails where a test says no.

States. No theorem. Four `#guard` commands make five tests: the parameter file is `textOf policyF`;
its four digests are `refTableWords`; the tables SILU, FS (sigmoid, then clamp) and rotary, as the
Lean verifier program makes them, have these digests and are `gate.1`, `gate.2`, `rope` of the file
`OnBytes/Tie/Pv/Lookup/Test/TestTablesOfModel.lean`; the table of exponentials has its digest and is
`expTable 12 8`, which that file types again under no name: that the two are one, a reader compares;
entry t of the upper half of FS is the model's `clamp 127 (t - 49152) + 128`.
Under. No hypothesis. Of the 264,451 entries, 32,768 are compared with the model here; the other
231,683 in that test file, which this file imports.
Does not show.
  1. A theorem: an evaluation is not checked by Lean's kernel, and no statement can use these lines.
  2. That the bytes of `zStoredFull` are a file's on a disk: see OwnStoredFullRun.lean.
  3. Equal tables from equal digests, but for a collision of the hash in OnBytes/Hash/SecondHashFunction.lean.
  4. Anything on the tables that the C++ programs compute in floating point.
  5. "The model's tables are the proofs' tables": only entries under the four digests are compared.
  6. The model's other tables and steps (`FE`, `FC`, `R8`, `tau1`, roundings; the notes list them).
  7. What a lookup in these tables proves.
  8. That the model reads no further line of the parameter file.
  9. Anything on soundness.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Own.OwnStoredFull
import Johnson.Flat.ModelLines
import OnBytes.Model.VerifyPublic
import OnBytes.Model.LayerTables
import OnBytes.Model.AttentionExp
import OnBytes.Tie.Pv.Plan.PlanKits
import OnBytes.Tie.Pv.Lookup.Test.TestTablesOfModel
import Inst.Model.Program

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Arm.Own.StoredTablesRun

open OnBytes.Model OnBytes.Model.Verify

/-- An array with its first entry one higher. -/
def turned (a : Array Nat) : Array Nat := a.modify 0 (· + 1)

/-- Of a table: its length; whether it is the array `want`; what the program's comparison of its
digest with the parameter file's lines says of it, and of it with its first entry one higher. -/
def row (P : PolScan) (t : PublicTable) (a want : Array Nat) : Nat × Bool × Bool × Bool :=
  (a.size, a == want, (tableHeld P t a).isOk, (tableHeld P t (turned a)).isOk)

/-- The number of t below n at which same t is false. -/
def differ (n : Nat) (same : Nat → Bool) : Nat := ((List.range n).filter fun t => !same t).length

-- 1. the parameter file is the written list's bytes
#guard zStoredFull.pol == OnBytes.Tie.Pv.Plan.textOf OnBytes.Tie.Pv.Plan.policyF

-- 2. and 3. the digests' words; SILU, FS, the rotary table
#guard (match polLayout zStoredFull.pol with
  | .error _ => none
  | .ok (P, y) =>
    let g := Fo.TablesOfModel.gate
    some (P.tblPol.size, P.tblPol.toList == OnBytes.Flat.refTableWords, y.h.p3, y.h.p4,
      row P .silu y.silu g.1, row P .sigmoid y.fs g.2,
      (Layer.ropeOf y.h).toOption.map fun r => row P .rope r Fo.TablesOfModel.rope)) ==
  some (32, true, true, true, (65536, true, true, false), (65536, true, true, false),
    some (131072, true, true, false))

-- 4. the whole public part; the table of exponentials
#guard (match publicOf zStoredFull.pol zStoredFull.KL (some zStoredFull.lay) with
  | .error _ => none
  | .ok X =>
    some (X.A.size, X.A[0]?.map fun a =>
      (X.A.all fun b => b.S.Tt == a.S.Tt,
        row X.P .exp a.S.Tt ((OnBytes.Attention.expTable 12 8).getD #[])))) ==
  some (12, some (true, (2307, true, true, false)))

-- 5. the upper half of table FS is the model's clamp
#guard (let f := Fo.TablesOfModel.gate.2
  (differ 32768 fun t =>
      (f.getD (32768 + t) 0 : Int) == Inst.Model.clamp 127 ((32768 + t : Int) - 49152) + 128,
    differ 32768 (fun t =>
      (f.getD (32768 + t) 0 : Int) == Inst.Model.clamp 127 ((32768 + t : Int) - 49151) + 128)
      != 0)) == (0, true)

end OnBytes.K.Arm.Own.StoredTablesRun

/-
Notes in full (other files' comments call these notes "the head of" this file).

Johnson/Top/Own/OwnStoredTablesRun.lean: the four public tables that the parameter file of
`zStoredFull` (Johnson/Top/Own/OwnStoredFull.lean) names by their digests: EVALUATED AT EVERY BUILD;
NO KERNEL PROOF. Each `#guard` command below is checked by Lean's evaluator whenever this file
compiles, and the file stands in the library's default target: so a build fails where one says no.
Four commands hold the five tests listed here: 2 and 3 share one.

Why. The theorems' integer model computes with fixed tables, `tbRef` (Inst/Model/TablesRef.lean),
and with the clamp of its step (U3) (Inst/Model/Program.lean). A proof is about the tables whose
digests stand in the parameter file (the lines tsilu, tsig, trope, texp). If one entry differed, a
statement that reads the sub-proofs as the model's would be false of honest proofs.

What is tested, at `zStoredFull`, the library's written copy of the shipped full-size example's
public files:
  1. the parameter file is, byte for byte, `textOf policyF` (OnBytes/Tie/Pv/Plan/PlanKits.lean): so
     what OnBytes/Tie/Pv/Lookup/Test/TestTablesAtFiles.lean runs at that term is run at these bytes:
     a second road to 3 and 4;
  2. the file has the 32 words of four digests, and they are `refTableWords`
     (Johnson/Flat/ModelLines.lean); the layout's flags p3 and p4 are on, under which the program
     compares the second and the fourth (OnBytes/Model/VerifyPublic.lean, `publicOf`);
  3. for the tables SILU, FS and the rotary table, as the program's own `polLayout` and `ropeOf`
     make them at this file: the length; the array is `gate.1`, `gate.2` or `rope` of
     OnBytes/Tie/Pv/Lookup/Test/TestTablesOfModel.lean, as a whole array; the program's own
     comparison `tableHeld`
     (OnBytes/Model/Config.lean) of the array's digest with the file's lines says yes; with the
     array's first entry one higher it says no;
  4. the program's `publicOf` returns at the three files; it has twelve attention plans, all with
     one table of exponentials; for that table the like of 3, against `expTable 12 8`, the term of
     that file's fourth guard;
  5. the upper half of table FS, which is none of `tbRef`'s five functions: entry t is the model's
     `clamp 127 (t - 49152) + 128`, at all 32,768 entries; moved by one place some entry differs.

What this file's own lines hold, and what the imported file's. HERE: that the four digests in the
file are those of the four arrays that the program makes at these files (264,451 entries); that
these arrays are the arrays of OnBytes/Tie/Pv/Lookup/Test/TestTablesOfModel.lean; and, of the model,
the 32,768 entries of 5. THERE: THE OTHER 231,683 ENTRIES (all of SILU, the lower half of FS, the
rotary table, the exponentials) ARE HELD AGAINST `tbRef`. THIS FILE IMPORTS THAT ONE, so that the
two are built together and this one cannot stand in a tree without it, and it compares with that
file's own terms `gate` and `rope`: if another array stood there, a guard here would say no. (For
the exponentials that file has no name: `expTable 12 8` is typed in both: there the tie is a
reader's eye.) So all entries under the four digests that the parameter file names are held against
the model's own numbers, by Lean's evaluator.

What is not claimed. THESE ARE NO THEOREMS: an evaluation is not checked by Lean's kernel, and no
statement of the library can use a line of this file. That `zStoredFull`'s bytes are a file's on a
disk: on that see the guards on three BLAKE2b sums in Johnson/Top/Own/OwnStoredFullRun.lean and that
file's head. Equal digests show equal tables only up to a collision of the second hash function
(OnBytes/Hash/SecondHashFunction.lean, under the number 72). Nothing on the tables that the C++ programs compute
in floating point (on these see the head of OnBytes/Model/TestLayerTables.lean).
IT IS LESS THAN "THE MODEL's TABLES ARE THE PROOFS' TABLES": it speaks of the entries under the four
digests. Under no digest of the file, and under no guard here or in the two test files named: the
layers without the rotary step (the comparison with `tbRef` stands at layer 0); how an entry becomes
a row of a lookup table (`FL`, `FS`, `tau2` of Inst/Model/Tables.lean: shifts, tags, paddings);
`tau2`'s dead rows and cut, and the model's `expRows` against the table's length; `FE`, with the
exponentials `EX` of the model's last stage, which have no digest among the file's lines; `FC`;
`R8`, `R16`, `R23` (Cm/TargetPHead.lean); `tau1`, `tau3`, `tau4`; every rounding and shift of the
model's arithmetic. Nothing on what a lookup in these tables proves. That the model reads no further
line of the parameter file is not tested here (Johnson/Flat/ModelLines.lean lists what is compared
and what is left out). Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
