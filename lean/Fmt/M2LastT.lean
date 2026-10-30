-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2LastT.lean: the values that the programs (the C++ implementation that comes with this Lean
code) print on the way through the last proximity test on a group. The sizes are arguments, so the
values are given in a form that names no toy's sizes.

Two definitions, two theorems. No Mathlib. The second toy is a test protocol; the head of
Fmt/M2Dec.lean says what it is. A group consists of the oracle messages that are tested together,
its members.
`lastTAt` walks the last test round by round. For each stage but the last it gives eight values (at
the first stage three fewer if `yFirstAt` gives nothing, the empty list):
    `S.t`, the target after the fold;
    the three folded symbols;
    `G'.t`, the target after the code switch;
    the first entry of `G'.c`; the first and the last entry of `G'.d`.
Then it gives the two sides of the last block's linear check.
`lastT` (Fmt/M2Targets.lean; its head lists the values under 1.) is the same walk for the second
toy: it reads members, tree, field and stages off that toy's record of sizes; here these are
arguments. `lastAt` (Fmt/M2Last.lean) is the decision in that form. Fmt/M3Targets.lean (`targetsBy`)
uses this walk for a group of its own.

Main names:
  `yFirstAt f ms fresh tree V g xs`: the three folded symbols (main, old mask, fresh mask) at the
    first draw of xs, the list of positions at which the group's tree is opened. It gives nothing if
    there is no draw or no column. g is the list of the fold's challenges.
  `lastTAt B f stages ms fresh tree V G rs`: the list of the values told above. It gives none at
    fewer than two stages, at a missing round or one with other numbers of elements or positions,
    and where `B.cs` or `ioppT` gives none.
  `yFirst_at`, `lastT_at`: the second toy's functions (`yFirst`, `lastT`) are these at its own data:
    by unfolding.

Notation:
  of `lastTAt`,
  `B`: a record `M1.Blocks`: the six functions of the blocks;
  `f`: the field;
  `stages`: the stages of the last proximity test (`Stage`);
  `ms`: the group's members;
  `fresh`: a natural number; in the head of Fmt/M2Last.lean, the rows of the first fold's fresh
    mask;
  `tree`: the number of the group's tree;
  `V`: the view, that is the rounds and the opened columns (`View`);
  `G` (`GRow`): the group's row;
  `rs` (`Rs`): a list of rounds; in the head of Fmt/M2Last.lean, the rounds from this test's first
    "FOLD epsilon" on (the rounds' names: Fmt/M2Plan.lean);
  `S`: what the fold hands on (`SRow`), with its target t;
  `G'` (`GRow`): c on the main table, d on the mask table, and the target t.
  (`M1.Blocks`: Fmt/M1Dec.lean; `Stage`, `View`, `GRow`, `Rs`, `SRow`: Fmt/M1Types.lean.)

Limits: this file does not say that the walk is the decision's. The walk is a copy of `lastAt`'s
steps; no theorem ties the two. B is read at the first stage alone. For the later stages the walk
calls `ioppT` (Fmt/M1Targets.lean), at the first toy's own blocks (`foldStep`, `csStep`,
`sampleRow`). What the head of Fmt/M2Targets.lean lists under 4. as not claimed is not claimed here
either: that these are the programs' values.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Last
import Fmt.M2Targets

namespace Fmt.M2
open Fmt.M1

/-- the three folded symbols at the first draw -/
def yFirstAt (f : Fld) (ms : List Mem) (fresh tree : Nat) (V : M1.View)
    (g : List E) (xs : List Nat) : List E :=
  match xs.head?.bind fun x => (colAt V tree x).bind (groupCol ms fresh) with
  | some c =>
    let gh := g.take (hOf ms)
    [foldV f g c.col.main, foldV f gh c.col.mask, foldV f gh c.col.fresh]
  | none => []

theorem yFirst_at (P : Par) (V : M1.View) (m : Nat) (S : KSRow) (xs : List Nat) :
    yFirst P V m S xs = yFirstAt P.fld (memsOf P.links m) 1 (m - 1) V S.s.g xs := rfl

/-- The last test's values, from the group's row on. -/
def lastTAt (B : M1.Blocks) (f : Fld) (stages : List Stage) (ms : List Mem) (fresh tree : Nat)
    (V : M1.View) (G : GRow) (rs : Rs) : Option (List E) :=
  match stages with
  | s :: s' :: more =>
    match nextN 1 1 0 rs with
    | some (⟨[sigma], [eps], _⟩, rs1) =>
      match takeRounds s.k rs1 with
      | some (qs, g, rs2) =>
        match seedOf s'.na rs2 with
        | some (z, beta, rs3) =>
          match nextN 1 1 s.t rs3 with
          | some (⟨[alpha], [theta], xs⟩, rs4) =>
            let S := B.fold f s.k s.h G sigma eps qs g
            match B.cs f s s' S (B.sample f s'.Am s'.Az z beta alpha) xs theta
                (fun x => ((colAt V tree x).bind (groupCol ms fresh)).map (·.col)) with
            | some G' =>
              (ioppT f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rs4).map fun r =>
                [S.t] ++ yFirstAt f ms fresh tree V S.g xs ++
                  [G'.t, ent G'.c 0, ent G'.d 0, ent G'.d (G'.d.size - 1)] ++ r
            | none => none
          | _ => none
        | none => none
      | none => none
    | _ => none
  | _ => none

theorem lastT_at (B : Blocks) (P : Par) (V : M1.View) (G : GRow) (rs : Rs) :
    lastT B P V G rs =
      lastTAt B.m1 P.fld P.stages (memsOf P.links (P.links + 1)) 1 P.links V G rs := rfl

end Fmt.M2
