-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Targets.lean: the second toy (a chain of three links): the 34 intermediate values that the
programs print, as a function of the view.

At the blocks of Fmt/M2All.lean, the decision (Fmt/M2Dec.lean) makes its only checks of equations
between field elements in the last block, so its verdict alone only shows whether all blocks agree.
(The head of Fmt/M2Dec.lean, under 1., tells what the decision tests before the last block.) The
programs (the C++ implementation that comes with this Lean code) therefore print, beside a proof, 34
field elements that their verifier computes on its way. This file computes the same values from the
view, so that each block can be compared with the programs by itself. Core Lean, no Mathlib; every
function is total; generic in the sizes and in the number of links. What the second toy is, and what
a row, a block and the view are: the head of Fmt/M2Dec.lean.

Sources. The list of the values and their order: the programs' description of the toy, section 6.

1. What the file contains. The values, in this order:
    for each link: the target of the group's row after its batching; the target after its fold; the
    three folded symbols (main, old mask, fresh mask) at the first draw of the list that opens its
    tree;
    the target after the last group's batching;
    for each stage of the last test but the last: the target after FOLD; the three folded symbols at
    the first draw of the switch; the target after CS; the first entry of its c; the first and the
    last entry of its d;
    the two sides of the last block's linear check.
   `targets B P V : Option (List E)`: these values: 5 for each link, 1, 8 for each stage but the
     last, 2 (3 fewer wherever `yFirst`, Fmt/M2Dec.lean, gives nothing). The links' values are the
     log of the decision's own pass (`goLinks`, Fmt/M2Dec.lean), but for the last link's three
     folded symbols, which `targetsBy` computes after the links. For the last group's batching
     `targetsBy` copies `decBy`'s steps. For the last test's first stage `lastT` copies
     `lastTest`'s steps. For its later stages `lastT` calls the first toy's function (`ioppT`,
     Fmt/M1Targets.lean), which is itself a copy of that toy's pass, at that toy's own blocks.
   `names L n`: the programs' names for the values, for use in a report.

2. What is checked when the file compiles (#guard). At three links and three stages there are 34
   names.

3. Theorems. None. In particular no theorem ties the copied steps to the decision's.

4. What is not claimed. That these are the programs' values is not shown here. On the programs' own
   proofs all 34 values are compared by tests (#guard) in Fmt/M2EngineLT.lean, Fmt/M2EngineLR.lean
   and Fmt/M2EngineLF.lean. The tests named here stand on the files that come with this code.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Dec
import Fmt.M1Targets

namespace Fmt.M2
open Fmt.M1

/-- the last test's values, from the last group's row on -/
def lastT (B : Blocks) (P : Par) (V : M1.View) (G : GRow) (rs : Rs) : Option (List E) :=
  match P.stages with
  | s :: s' :: more =>
    match nextN 1 1 0 rs with
    | some (⟨[sigma], [eps], _⟩, rs1) =>
      match takeRounds s.k rs1 with
      | some (qs, g, rs2) =>
        match seedOf s'.na rs2 with
        | some (z, beta, rs3) =>
          match nextN 1 1 s.t rs3 with
          | some (⟨[alpha], [theta], xs⟩, rs4) =>
            let S := B.m1.fold P.fld s.k s.h G sigma eps qs g
            match B.m1.cs P.fld s s' S (B.m1.sample P.fld s'.Am s'.Az z beta alpha) xs theta
                (fun x =>
                  ((colAt V P.links x).bind (groupCol (memsOf P.links (P.links + 1)) 1)).map
                      (·.col)) with
            | some G' =>
              (ioppT P.fld V (s' :: more) (P.links + 1) 0 (2 ^ s'.k) G' rs4).map fun r =>
                [S.t] ++ yFirst P V (P.links + 1) ⟨S, #[]⟩ xs ++
                  [G'.t, ent G'.c 0, ent G'.d 0, ent G'.d (G'.d.size - 1)] ++ r
            | none => none
          | _ => none
        | none => none
      | none => none
    | _ => none
  | _ => none

/-- the values, given a way of batching -/
def targetsBy (B : Blocks) (P : Par) (V : M1.View) (bt : Batch) : Option (List E) :=
  match goLinks B P V bt P.links 1 none V.rounds [] with
  | some (some S, rs, log) =>
    match readFirst P (P.links + 1) rs with
    | some (z, beta, ys, xs, rs2) =>
      match nextN 0 1 0 rs2 with
      | some (⟨_, [theta], _⟩, rs3) =>
        match bt (P.links + 1) (some ⟨S.1, xs, S.2⟩)
            (samplesM B P (P.links + 1) z beta ys) theta with
        | some R => (lastT B P V R.toG rs3).map fun r => log ++ yFirst P V P.links S.1 xs ++ [R.t] ++ r
        | none => none
      | _ => none
    | none => none
  | _ => none

/-- The values. -/
def targets (B : Blocks) (P : Par) (V : M1.View) : Option (List E) := targetsBy B P V (batch B P V)

/-- their names; L links, n stages -/
def names (L n : Nat) : List String :=
  ((List.range L).flatMap fun _ =>
    ["REQ: the group row's target", "REQ: FOLD's target", "CS: y_main at the first draw",
      "CS: y_0 at the first draw", "CS: y_1 at the first draw"]) ++
  ["BAT: target"] ++
  ((List.range (n - 1)).flatMap fun _ =>
    ["FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw",
      "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry"]) ++
  ["BASE: left side of the linear check", "BASE: right side of the linear check"]

#guard (names 3 3).length == 34

end Fmt.M2
