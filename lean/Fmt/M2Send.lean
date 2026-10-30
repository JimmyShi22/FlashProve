-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Send.lean: the sample row of a sent oracle message in the second toy (a chain of three links),
on the message's own tables, for all three kinds of pad.

Definitions that compute, with tests (#guard). No theorem. Core Lean; total.
This is one step of a verifier's decision (Fmt/M2Dec.lean; the field `sample` of its record
`Blocks`). After a prover's message the verifier draws a point z and a factor beta, and the prover
answers with one field element y for each sampled oracle message. The sample row is the linear
equation that such an answer claims: a form (a vector of coefficients) on the message's main table,
a form on its mask table, and the target y. The weights of a point are the values at it of the
multilinear Lagrange polynomials (`pv`, `eqAt`, Fmt/M1Types.lean).
A prover's message holds several oracle messages; those that are sampled share one point, of which
each reads the first coordinates, as many as its own cube has (Fmt/M2Types.lean: `cubeOf`). The pad
is one element of E that stands under the factor beta and under no weight of the point.

Main names:
  `sampleOf f l lz m z beta y`: two forms; l and lz are the lengths of a main row and of a mask row.
    What follows is said for l and lz that are powers of two: the forms' sizes are taken from
    `Nat.log2 l` and `Nat.log2 lz`. The decision calls this block at `P.C.l` and `P.Z.l`, and
    `sizesOK` (Fmt/M2Dec.lean) tests that these are powers of two. The first form is on m's own main
    table, of 2^b rows (b = `clog m.rows`), where the entry of row r at place p has the index r +
    2^b p. The second form is on m's own mask table, and is empty if m has none. The target is y.
    With mask rows, the two forms are the first toy's row unchanged (`sampleRow`, Fmt/M1Send.lean).
    That row reads the point by index, so a longer point does no harm. The pad is the mask table's
    last entry. (So this case is for a number of mask rows that is a power of two; no other occurs.)
    Without mask rows, no coordinate is read on top of the main table's own index bits. The first
    form has the weights of the point's first coordinates, one for each of these bits, and nothing
    of the coordinates beyond enters. The pad stands in the last real main row (row `m.rows` - 1):
      rows over E: at its last place, under beta;
      rows over the base field: at its last three places, under beta, beta X, beta X^2.
    E is the base field's cubic extension (`Ext3`, Fmt/FieldE.lean).

Limits: this file does not say that the programs (the C++ implementation that comes with this Lean
code) compute so: no theorem says it. Written from their description of the toy and from the answers
to questions about it; this file's sources include no file of theirs on this toy. The decision of
which this block is a part is compared with theirs by tests when files compile, on their own files:
Fmt/M2EngineLT.lean, M2EngineLR.lean, M2EngineLF.lean (every round as their tool prints it; the
decision accepts the honest proof; the 34 intermediate values of Fmt/M2Targets.lean);
Fmt/M2EngineLTw.lean, M2EngineLRw.lean, M2EngineLFwa.lean to M2EngineLFwg.lean (each altered copy
and false proof is refused, and by which of the two, the strict reader or the decision);
Run/M2Engine*.lean (the same files before the compiled verifier). Tests, no theorem.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1Send

namespace Fmt.M2
open Fmt.M1

/-- the index, in a member's own main table, of place p of its last real row -/
def padAt (m : Mem) (p : Nat) : Nat := (m.rows - 1) + 2 ^ clog m.rows * p

/-- The sample row of a sent oracle message, on its own tables. -/
def sampleOf (f : Fld) (l lz : Nat) (m : Mem) (z : List E) (beta y : E) : Array E × Array E :=
  let Am := clog m.rows + Nat.log2 l
  if m.masks == 0 then
    let w := pv f Fld.oneE (z.take Am)
    if m.overE then (w.setIfInBounds (padAt m (l - 1)) beta, #[])
    else
      (((w.setIfInBounds (padAt m (l - 3)) beta).setIfInBounds
            (padAt m (l - 2)) (f.mulE beta (0, 1, 0))).setIfInBounds
          (padAt m (l - 1)) (f.mulE beta (0, 0, 1)),
        #[])
  else
    let R := sampleRow f Am (clog m.masks + Nat.log2 lz) z beta y
    (R.c, R.d)

/-! ## Tests -/

namespace SendT
def el (n : Nat) : E :=
  (Fld.two.red (1000003 * n + 17), Fld.two.red (n * n + 5 * n + 3), Fld.two.red (7919 * n + 1))
def pt (a : Nat) : List E := (List.range a).map fun t => el (t + 1)
end SendT
open SendT

-- sizes, at rows of 8 and mask rows of 4 entries
#guard ((sampleOf .two 8 4 memG (pt 9) (el 50) (el 51)).1.size, (sampleOf .two 8 4 memG (pt 9) (el 50) (el 51)).2.size) == (16, 0)
#guard ((sampleOf .two 8 4 (memP true) (pt 9) (el 50) (el 51)).1.size, (sampleOf .two 8 4 (memB 1) (pt 9) (el 50) (el 51)).1.size, (sampleOf .two 8 4 (memB 1) (pt 9) (el 50) (el 51)).2.size, (sampleOf .two 8 4 (memB 2) (pt 9) (el 50) (el 51)).1.size) == (8, 16, 4, 8)
-- the pads' places: the carrying message: the table's last entry; a row over the base field: its
-- last three
#guard padAt memG 7 == 15 && ent (sampleOf .two 8 4 memG (pt 9) (el 50) (el 51)).1 15 == el 50
#guard (let w := (sampleOf .two 8 4 (memP false) (pt 9) (el 50) (el 51)).1; (ent w 5, ent w 6, ent w 7)) == (el 50, Fld.two.mulE (el 50) (0, 1, 0), Fld.two.mulE (el 50) (0, 0, 1))
-- beside the pad: the weights of the first coordinates
#guard (List.range 15).all fun i => ent (sampleOf .two 8 4 memG (pt 9) (el 50) (el 51)).1 i == eqAt .two (pt 4) i
#guard (List.range 5).all fun i => ent (sampleOf .two 8 4 (memP false) (pt 9) (el 50) (el 51)).1 i == eqAt .two (pt 3) i
-- only the first coordinates are read: a longer point, other coordinates beyond the cube: the same
-- forms, in all three cases
#guard [memG, memP false, memB 1, memB 2].all fun m => sampleOf .two 8 4 m (pt 9) (el 50) (el 51) == sampleOf .two 8 4 m ((pt 9).take (cubeOf 3 2 m) ++ [el 77, el 78]) (el 50) (el 51)
-- with mask rows: the first toy's row
#guard (sampleOf .two 8 4 (memB 1) (pt 9) (el 50) (el 51)) == ((sampleRow .two 4 2 (pt 9) (el 50) (el 51)).c, (sampleRow .two 4 2 (pt 9) (el 50) (el 51)).d)
-- three entries of the base field under beta, beta X, beta X^2 make beta times one element of E
#guard Fld.two.addE (Fld.two.mulE (el 50) (Fld.ofF 5)) (Fld.two.addE (Fld.two.mulE (Fld.two.mulE (el 50) (0, 1, 0)) (Fld.ofF 6)) (Fld.two.mulE (Fld.two.mulE (el 50) (0, 0, 1)) (Fld.ofF 7))) == Fld.two.mulE (el 50) (5, 6, 7)

end Fmt.M2
