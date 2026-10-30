-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Fold.lean: the second toy (a chain of three links): fold on a group with a kept row, the
verifier's side.

Definitions that compute, with tests (#guard). No theorem. Core Lean; total. What the second toy is:
the head of Fmt/M2Dec.lean.

Main names:
  `foldK f k h R sigma eps qs g`: the fold on a group with a kept member, a message that the next
    link reads again (the head of Fmt/M2Types.lean).
      On the group's main and mask tables and on the target it is the first toy's fold, unchanged
        (`foldStep`, Fmt/M1Fold.lean).
      The form on the kept member's table stays on that table, unfolded, and is multiplied by
        eps (1 - g_1) .. (1 - g_k). This product of the 1 - g_j (`cornerZero`) is the value at g of
        the multilinear Lagrange polynomial of the corner of the cube where all k variables are 0.
      In `foldStep` the mask's form is multiplied by eps and the product of the g_j after the first
        h: the other corner of the cube, where these variables are 1.

Notation:
  k, h: natural numbers; the pass (`goLinks`, Fmt/M2Dec.lean) hands in a group's `kOf`, `hOf`
    (Fmt/M2Types.lean): 2^k rows hold the main blocks of rows, 2^h rows the mask blocks;
  `R` (`KRow`): a row on a group: forms c, kp, d and the target t;
  c, kp, d: forms on the main table, on the kept member's own table, on the mask table;
  `sigma`, `eps`: elements; in `foldStep` (Fmt/M1Fold.lean), sigma: the element sent before the
    rounds; eps: the element drawn after it;
  `qs`: a list of pairs of elements;
  `g`: a list of elements: the drawn elements;
  `KSRow`: what a fold hands on: s, the first toy's `SRow`, and the form kp.
  (`KRow`, `KSRow`: Fmt/M2Types.lean; `SRow`: Fmt/M1Types.lean.)

Limits: what the head of Fmt/M2Send.lean lists as not said is not said here either. That the first
claim of the fold's sum-check is sigma + eps tau with tau the target of the whole row, the kept part
in it, was a reading of the programs' description; in the tests named in the head of
Fmt/M2Send.lean the fold's target agrees with theirs at all three links.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1Fold

namespace Fmt.M2
open Fmt.M1

/-- the product of 1 - g_j over the first k drawn elements (g_j counts as 0 beyond the list's end)
-/
def cornerZero (f : Fld) (k : Nat) (g : List E) : E :=
  (List.range k).foldl (fun s j => f.mulE s (f.subE Fld.oneE (g.getD j Fld.zeroE))) Fld.oneE

/-- FOLD, the verifier's side, with a kept row. -/
def foldK (f : Fld) (k h : Nat) (R : KRow) (sigma eps : E) (qs : List (E × E)) (g : List E) :
    KSRow :=
  ⟨foldStep f k h R.toG sigma eps qs g, scaleV f (f.mulE eps (cornerZero f k g)) R.kp⟩

#guard cornerZero .two 0 [(5, 0, 0)] == Fld.oneE && cornerZero .two 2 [(5, 0, 0), (3, 0, 0), (9, 0, 0)] == (8, 0, 0)
#guard (foldK .two 1 0 ⟨#[(1, 0, 0), (2, 0, 0)], #[(7, 0, 0), (0, 0, 0)], #[(4, 0, 0)], (1, 0, 0)⟩ (0, 0, 0) (2, 0, 0) [((0, 0, 0), (0, 0, 0))] [(0, 0, 0)]).kp == #[(14, 0, 0), (0, 0, 0)]
#guard (foldK .two 1 0 ⟨#[(1, 0, 0), (2, 0, 0)], #[], #[(4, 0, 0)], (1, 0, 0)⟩ (0, 0, 0) (2, 0, 0) [((0, 0, 0), (0, 0, 0))] [(3, 0, 0)]).kp == #[]
-- without a kept row: the first toy's fold
#guard (let R : KRow := ⟨#[(1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)], #[], #[(4, 0, 0), (5, 0, 0)], (1, 0, 0)⟩
  let a := (foldK .two 1 0 R (6, 0, 0) (2, 0, 0) [((1, 0, 0), (2, 0, 0))] [(3, 0, 0)]).s
  let b := foldStep .two 1 0 R.toG (6, 0, 0) (2, 0, 0) [((1, 0, 0), (2, 0, 0))] [(3, 0, 0)]
  (a.c, a.d0, a.d1, a.t, a.g) == (b.c, b.d0, b.d1, b.t, b.g))

end Fmt.M2
