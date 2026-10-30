-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Last.lean: the last proximity test on a group, from the group's row on. The sizes are
arguments, so the test is in a form that names no toy's sizes: for any members, any tree, any
stages.

One definition, one theorem. No Mathlib. A group consists of the oracle messages that are tested
together, its members. The second toy is a test protocol; the heads of Fmt/M2Dec.lean and
Fmt/M2Types.lean say what it is, and what a group's row, a block and the view are.
Fmt/M2Dec.lean's `lastTest` reads the members of the last group, the number of its tree, the field
and the stages off the second toy's record of sizes. A further toy closes a group of its own (other
members, another tree) by the same test (Fmt/M3Dec.lean). This file has that test with these four as
arguments. A fifth argument, fresh, is 1 in `lastTest`.

Main names:
  `lastAt B f stages ms fresh tree V G rs`: the test. Among its arguments:
      B: any record of the type `M1.Blocks` (Fmt/M1Dec.lean), the six functions of the first toy's
        blocks;
      ms: the group's members;
      fresh: a natural number, the rows of the first fold's fresh mask;
      tree: the number of the group's tree (the later stages' trees follow it);
      G: the group's one batched row;
      rs: the rounds from this test's first "FOLD epsilon" on (the rounds' names: Fmt/M2Plan.lean).
    ms and fresh say how a column of the group's tree is cut (`groupCol`, Fmt/M2Types.lean).
    The first stage is written here:
      a fold (`B.fold`);
      the next stage's sending with its sample (`B.sample`);
      the code switch (`B.cs`; the head of Fmt/M1Cs.lean) at the opened columns of the group's tree.
    The later stages are the first toy's (`iopp`, Fmt/M1Dec.lean). The test refuses (false) at fewer
    than two stages, at a missing round or one with other numbers of elements or positions, and
    where `B.cs` gives none.
  `lastTest_at`: the second toy's `lastTest` is `lastAt` at its own data: by unfolding.

Notation:
  `f`: the field;
  `stages`: the stages of the last proximity test (`Stage`);
  `V`: the view, that is the rounds and the opened columns (`View`);
  `sigma`: the element sent before the fold's rounds;
  `eps`: the element drawn after sigma;
  `z`, `beta`: the point and the factor of a seed;
  `alpha`: the answer, sent in the round behind the seed;
  `theta`, `xs`: the element and the positions drawn in that round;
  0 and 2 ^ s'.k, handed to `iopp`: its natural numbers mF, mE, the main rows that were sent at the
    stage s' (over the base field, over the extension field).
  (Fmt/M1Types.lean: `Stage`, `View`, `RV`; Fmt/M1Dec.lean: `seedOf`, `Blocks.sample`; the head of
    Fmt/M1Fold.lean: sigma, eps.)

Limits: this file says nothing on what the test shows. That the stages fit the group (the first
stage's k, h are the group's) is the caller's test on sizes.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Dec

namespace Fmt.M2
open Fmt.M1

/-- The last proximity test on a group. -/
def lastAt (B : M1.Blocks) (f : Fld) (stages : List Stage) (ms : List Mem) (fresh tree : Nat)
    (V : M1.View) (G : GRow) (rs : Rs) : Bool :=
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
            match B.cs f s s' (B.fold f s.k s.h G sigma eps qs g)
                (B.sample f s'.Am s'.Az z beta alpha) xs theta
                (fun x => ((colAt V tree x).bind (groupCol ms fresh)).map (·.col)) with
            | some G' => iopp B f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rs4
            | none => false
          | _ => false
        | none => false
      | none => false
    | _ => false
  | _ => false

theorem lastTest_at (B : Blocks) (P : Par) (V : M1.View) (G : GRow) (rs : Rs) :
    lastTest B P V G rs =
      lastAt B.m1 P.fld P.stages (memsOf P.links (P.links + 1)) 1 P.links V G rs := rfl

end Fmt.M2
