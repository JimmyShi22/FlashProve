-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/Target.lean: the kind «the code switch»: THE PUBLIC TEST IN FRONT OF THE
SENDING [G0], IN THE KIND's OWN TEXT: do the sizes of the carried rows (old), of the plan's target
(T) and of the statement, which are all public, fit a switch?
A list of clauses, each under a name in plain words; the test is that all hold; a refusal names the
first that fails («it is not so that …»).
WHAT IS ASKED, AND WHY. The switch encodes anew, into ONE new message g, the message of the folded
main row (into g's «main block») and «the rest» (the two masks' messages and the tails of all rows:
into g's «rest block»), and sends a fresh copy of each kept member. So:
  the old rows   have both masks; their two codes are in the statement's lists; the old message
  length is a power of two
  g              has a main code in the list, at least one main row, rows over the extension field,
  at least one answer, and a row long enough for its pad
  the two blocks begin at multiples of their sizes and are together ALL the rows of g: either the
  rest lies in g's mask rows, or behind the main block among the main rows (then g has no mask row)
  the sizes      a main block has at most as many rows as the old message has entries, and the old
  message fits into the block; the rest fits into the places that g's rest block has outside the pad
  the kept       one target for each kept member; old and new have no mask rows; the new code is in
  the list; the old row is long enough for its pad; rows, degree, answers and message length are the
  old ones
WHAT IS CALLED BY NAME OF THE PROGRAM's FILES: LAYOUTS ALONE, which cannot fail: switchKept (which
members are kept) · switchParts (how long the rest is) · SwitchPlaces.make (how many places the rest
block has) · ceilLog2.
That each test here says what the program's own says (switchTargetCheck · (Send.pad …).isSome ·
powerOfTwo) is proved BESIDE, in K2C/Yard.lean, which no block imports.
No soundness: definitions with code.
-/
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

/-- The row that bears a sampled message's pad is long enough for it: the pad lies in the mask rows
if there are any, else in the main rows; it takes one entry an answer over the extension field,
three over the base field. -/
def padFits (codes : Codes) (s : OracleShape) : Bool :=
  let onMask := decide (0 < s.maskRows)
  let len := if onMask then (codes.mask.getD s.maskCode default).ell else
      (codes.base.getD s.code default).ell
  let each := if onMask || s.mainDeg == 3 then 1 else 3
  decide (each * s.answers ≤ len)

/-- n is a power of two. -/
def isPow2 (n : Nat) : Bool := n != 0 && 2 ^ ceilLog2 n == n

/-- A kept member's old shape o and the shape n of its fresh copy. -/
def keptFits (codes : Codes) (o n : OracleShape) : Bool :=
  o.maskRows == 0 && n.maskRows == 0 && decide (n.code < codes.base.size) && padFits codes o &&
    n.mainRows == o.mainRows && n.mainDeg == o.mainDeg && n.answers == o.answers &&
    (codes.base.getD n.code default).ell == (codes.base.getD o.code default).ell

/-- The two blocks are all the rows of g. -/
def blocksFill (codes : Codes) (T : SwitchTarget) : Bool :=
  match T.rest.part with
  | .mask =>
    decide (T.shape.maskCode < codes.mask.size) && T.main.firstRow == 0 && 2 ^ T.main.bits ==
        T.shape.mainRows &&
      T.rest.firstRow == 0 && 2 ^ T.rest.bits == T.shape.maskRows
  | .main =>
    T.shape.maskRows == 0 && T.main.firstRow == 0 && T.rest.firstRow == 2 ^ T.main.bits &&
      2 ^ T.main.bits + 2 ^ T.rest.bits == T.shape.mainRows

/-- [G0], clause by clause. -/
def targetL (S : Statement) (old : SingleRows) (T : SwitchTarget) : List (String × Bool) :=
  let codes := S.codes
  let g := T.shape
  let ell := (codes.base.getD old.code default).ell
  [("the old rows have both masks", old.masks == 2),
   ("the old main code is in the list", decide (old.code < codes.base.size)),
   ("the old mask code is in the list", decide (old.maskCode < codes.mask.size)),
   ("g's main code is in the list", decide (g.code < codes.base.size)),
   ("g has a main row", decide (0 < g.mainRows)),
   ("g's main rows are over the extension field", g.mainDeg == 3),
   ("g is sampled", decide (1 ≤ g.answers)),
   ("g's row is long enough for its pad", padFits codes g),
   ("the main row's message goes to g's main rows", T.main.part == .main),
   ("the old message length is a power of two", isPow2 ell),
   ("the main block begins at a multiple of its size", T.main.firstRow % 2 ^ T.main.bits == 0),
   ("the rest block begins at a multiple of its size", T.rest.firstRow % 2 ^ T.rest.bits == 0),
   ("the two blocks are all the rows of g", blocksFill codes T),
   ("the main block has at most as many rows as the old message has entries",
       decide (2 ^ T.main.bits ≤ ell)),
   ("the old message fits into the main block",
       decide (ell ≤ (codes.base.getD g.code default).ell * 2 ^ T.main.bits)),
   ("the rest fits into the rest block's places",
       decide ((switchParts S old).length ≤ (SwitchPlaces.make codes T).size)),
   ("there is a target for each kept member", T.kept.size == (switchKept old).size),
   ("each kept member's copy has its shape",
     ((switchKept old).zip T.kept).all fun p =>
         keptFits codes (S.oracles.getD p.1 default).shape p.2.shape)]

/-- [G0] All clauses hold. -/
def targetOk (S : Statement) (old : SingleRows) (T : SwitchTarget) : Bool :=
    (targetL S old T).all (·.2)

/-- The first clause that fails. -/
def targetWhy (S : Statement) (old : SingleRows) (T : SwitchTarget) : String :=
  (((targetL S old T).find? fun c => !c.2).map (·.1)).getD "no clause fails"

end Tw.K2
