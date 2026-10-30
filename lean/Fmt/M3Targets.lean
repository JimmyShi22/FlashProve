-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Targets.lean: the entry file: the 28 intermediate values that the programs print, as a
function of the view.

An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link (Fmt/M3Entry.lean says more).
The decision (Fmt/M3Dec.lean) makes its only checks of equations between field elements in the last
block, so its verdict alone only shows whether all blocks agree. The head of Fmt/M3Dec.lean lists
under 1 what the decision tests before that block. The programs (the C++ implementation that comes
with this Lean code) therefore print 28 field elements that their verifier computes on its way
through an entry file. This file computes the same values from the view (`View`, Fmt/M3Types.lean),
so that each block can be compared with the programs by itself. Core Lean, no Mathlib; every
function is total; generic in the sizes.

Sources. The list of the values, their names and their order: an answer to a question on these
values, at s = 0 (a table whose answers are empty); what the names G_u<0>, G_u<B> and (Col_1)
mean: the programs' description of the entry file. By a later answer, at s > 0 the programs print
the same 28 names, and by that answer two more are to come (the targets of the first rows of the two
tables' records, behind the first six). Nothing of that is rendered here, as the decision refuses
such sizes.

1. What the file contains. A row of the link is one of the verifier's linear claims on the prover's
   two oracle messages (Fmt/M3Link.lean): a form (a vector of coefficients) and a target.
   The values, in this order, which is that of `names`:
    1 to 3:  for the first table, three values of the row of its first draw:
             its target (the opened column folded at gamma);
             its coefficient at entry 0 of the folded row (the generator's first message entry at
             that position);
             its coefficient at the first entry of the folded tail (the generator's first tail
             entry).
    4 to 6:  the same three for the copy.
    7:       the fold of the first table's column at its first draw.
    8:       the same of the copy's.
    9:       the equality row's coefficient at entry 0 of the first table's folded row (the weight
             of phi at 0).
    10:      the target after the batching.
    Then, for each stage of the proximity test but the last:
             the target after FOLD;
             the three folded symbols at the first draw of the code switch (CS);
             the target after CS;
             the first entry of its c;
             the first and the last entry of its d (`c`, `d`: the fields of the new row, `GRow`,
             Fmt/M1Types.lean).
    Last:    the two sides of the last block's linear check.
   Values 1 and 7, and 4 and 8, are the same number under two of the programs' names.
   `firstOf P xs which`: The first draw of a table, in the order drawn.
   `col3 P V gamma which x`: The three values of that draw's row.
   `targetsBy B P V bt : Option (List E)`: The values. How many there are, in the
     order of the list above: 6, 3, 1, 8 for each stage but the last (at the first stage three fewer
     if `yFirstAt`, Fmt/M2LastT.lean, gives nothing), 2; at three stages 28. The five rounds in
     front and BAT are read as the decision reads them: these steps are a copy of the steps of
     `decBy` (Fmt/M3Dec.lean; its head names the rounds). The proximity test's values come from
     `lastTAt` (Fmt/M2LastT.lean).

   `names n`: The programs' names for the values, for use in a report.

2. What is checked when the file compiles (one #guard). At three stages there are 28 names.


3. Theorems. None. In particular no theorem ties the copied steps to the decision's.

4. What is not claimed. That these are the programs' values.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M3Dec
import Fmt.M2LastT

set_option autoImplicit false

namespace Fmt.M3
open Fmt.M1 Fmt.M2

/-- the first draw of the table "which" -/
def firstOf (P : Par) (xs : List Nat) (which : Nat) : Option Nat :=
  ((drawsOf P xs).find? fun d => d.1 == which).map (·.2)

/-- Three values of the row of a draw: its target; its coefficient at entry 0; at the tail's first
entry. -/
def col3 (P : Par) (V : View) (gamma : List E) (which x : Nat) : Option (List E) :=
  (storedAt V which x).map fun col =>
    [foldCol P.fld gamma col, Fld.ofF ((genM P.T x).getD 0 0), Fld.ofF ((genT P.T x).getD 0 0)]

/-- The values, given the blocks `B` and a way `bt` of combining the rows (`Batch`, Fmt/M3Dec.lean).
`B` is used at the first stage. The later stages use the functions of `M1.blocks` (`ioppT`,
Fmt/M1Targets.lean). -/
def targetsBy (B : M1.Blocks) (P : Par) (V : View) (bt : Batch) : Option (List E) :=
  match nextN 0 P.v 0 V.rounds with
  | some (vg, rs1) =>
    match seedOf (seedLen (lg P.C.l) (lg P.Z.l) P.mems) rs1 with
    | some (z, beta, rs2) =>
      match nextN 2 0 0 rs2 with
      | some (⟨[y0, yj], _, _⟩, rs3) =>
        match nextN 0 0 (P.nu0 + P.nuj) rs3 with
        | some (vx, rs4) =>
          match nextN 0 P.aPhi 0 rs4 with
          | some (vp, rs5) =>
            match nextN 0 1 0 rs5 with
            | some (⟨_, [theta], _⟩, rs6) =>
              match (firstOf P vx.poss 0).bind (col3 P V vg.els 0),
                (firstOf P vx.poss 1).bind (col3 P V vg.els 1),
                bt vg.els z beta y0 yj vx.poss vp.els theta with
              | some a, some b, some R =>
                (lastTAt B P.fld P.stages P.mems 1 0 V.own R.toG rs6).map fun r =>
                  a ++ b ++ [a.getD 0 Fld.zeroE, b.getD 0 Fld.zeroE,
                      ent (eqVecG (opsOf P.fld) P.cut P.nTab vp.els) 0] ++
                    [R.t] ++ r
              | _, _, _ => none
            | _ => none
          | none => none
        | none => none
      | _ => none
    | none => none
  | none => none

/-- The programs' names for the values, for use in a report; n stages. -/
def names (n : Nat) : List String :=
  ((List.range 2).flatMap fun _ =>
    ["FOLDEQ: (Col_1)'s target", "FOLDEQ: (Col_1) on G_u<0>", "FOLDEQ: (Col_1) on G_u<B>"]) ++
  ["LINK: the fold of the first table's column at its first draw",
    "LINK: the fold of the further table's column at its first draw",
    "LINK: the equality row's coefficient at entry 0 of the first table's folded row",
    "BAT: target"] ++
  ((List.range (n - 1)).flatMap fun _ =>
    ["FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw",
      "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry"]) ++
  ["BASE: left side of the linear check", "BASE: right side of the linear check"]

#guard (names 3).length == 28

end Fmt.M3
