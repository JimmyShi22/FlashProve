-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Psc.lean: the three linear claims that a link's sum-check leaves in the second toy (a chain of
three links). Each claim is on one row of l entries and on the link's mask row.

Definitions that compute, with tests (#guard). No theorem. Core Lean; total. What the second toy is:
the head of Fmt/M2Dec.lean. That head also tells what a linear claim is, and calls it a row; in this
file a row is a row of a table.

A link shows x[i] b[i] = c[i] for i below l / 2. A vector fills the lower half of a row. The
sum-check is the first toy's (`pscStep`, Fmt/M1Psc.lean) on V = log2 l - 1 variables X (`Par.V`,
Fmt/M2Types.lean) and one further variable Y. The head of Fmt/M1Psc.lean writes that toy's three
claims out as (U), (E_1), (E_2); x is called a there. Here the mask entries, their coefficients and
the targets are the same: these parts are those of the first toy's `rowU`, `rowE1`, `rowE2`,
unchanged. New is the main part alone, the form on the row of l entries. It has the weights of the
point gamma at the places below l / 2, and 0 above: `pv` at (gamma, then one coordinate 0).
Where a row is placed in its member's table and its group is settled in Fmt/M2Dec.lean (`pscM`).

Main names:
  `halfRow f s gamma`: for gamma of V coordinates: s eq(gamma, i) at place i below 2^V, 0 at the 2^V
    places above.
  `pscForms f V lz o`: the three claims, each as (the form on the row, the form on the mask row, the
    target):
      (U) on c's row, its weights multiplied by - eps;
      (E_1) on x's row;
      (E_2) on b's row.
  `pscOf`: the same on plain arguments, as the field `psc` of the record `Blocks` (Fmt/M2Dec.lean)
    asks it.

Notation (the head of Fmt/M1Psc.lean, which writes K for V):
  `zeta`: a list of elements: those drawn in the zero-check;
  what the prover sends: mu' (in code `mu`); the V pairs (in code `qs`); (p_1, p_2); (v_1, v_2);
  what is drawn: `eps`; `gamma`, a list of elements; `beta`;
  `lz`: the mask row's length.

Limits: what the head of Fmt/M2Send.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1Psc

namespace Fmt.M2
open Fmt.M1

/-- s eq(gamma, i) at place i of the lower half; 0 in the upper half -/
def halfRow (f : Fld) (s : E) (gamma : List E) : Array E := pv f s (gamma ++ [Fld.zeroE])

/-- The three claims. -/
def pscForms (f : Fld) (V lz : Nat) (o : PscOut) :
    (Array E × Array E × E) × (Array E × Array E × E) × (Array E × Array E × E) :=
  ((halfRow f (f.negE o.eps) o.gamma, (rowU f V lz o).d, (rowU f V lz o).t),
   (halfRow f Fld.oneE o.gamma, (rowE1 f V lz o).d, (rowE1 f V lz o).t),
   (halfRow f Fld.oneE o.gamma, (rowE2 f V lz o).d, (rowE2 f V lz o).t))

/-- The block, on plain arguments: V, l, the mask row's length; zeta; mu'; the V pairs; (p_1, p_2);
(v_1, v_2); eps; gamma; beta. -/
def pscOf (f : Fld) (V _l lz : Nat) (zeta : List E) (mu : E) (qs : List (E × E)) (p v : E × E)
    (eps : E) (gamma : List E) (beta : E) :
    (Array E × Array E × E) × (Array E × Array E × E) × (Array E × Array E × E) :=
  pscForms f V lz (pscStep f zeta ⟨mu, qs, p, v⟩ ⟨eps, gamma, beta⟩)

/-! ## Tests: an honest prover of the first toy's own test (`PscHon.wit`, `PscHon.msg`,
Fmt/M1Psc.lean), its three vectors laid in the lower halves of three rows -/

namespace PscT
/-- a vector in the lower half of a row whose upper half holds other things (a pad stands there):
the claims must not read them -/
def lower (v : Array E) : Array E :=
  v ++ Array.ofFn (n := v.size) fun i => PscHon.el .two (900 + i.val)
/-- which of the three claims hold: (U) of c's row, (E_1) of x's row, (E_2) of b's row, each with
the mask row -/
def holds (f : Fld) (K lz s : Nat) (spoil : Bool) : Bool × Bool × Bool :=
  let w0 := PscHon.wit f K lz s
  let w := if spoil then PscHon.bad f w0 1 else w0
  let zeta := PscHon.zetas f K s
  let d := PscHon.draws f K s
  let F := pscForms f K lz (pscStep f zeta (PscHon.msg f w K zeta d) d)
  let ok (x : Array E × Array E × E) (row : Array E) : Bool :=
    f.addE (dot f x.1 (lower row)) (dot f x.2.1 w.m) == x.2.2
  (ok F.1 w.c, ok F.2.1 w.a, ok F.2.2 w.b)
end PscT

#guard (halfRow .two (3, 0, 0) [(2, 0, 0), (5, 0, 0)]).size == 8 && (List.range 4).all fun i => ent (halfRow .two (3, 0, 0) [(2, 0, 0), (5, 0, 0)]) (4 + i) == Fld.zeroE
#guard (List.range 4).all fun i => ent (halfRow .two Fld.oneE [(2, 0, 0), (5, 0, 0)]) i == eqAt .two [(2, 0, 0), (5, 0, 0)] i
#guard PscT.holds .two 2 16 7 false == (true, true, true) && PscT.holds .two 3 16 9 false == (true, true, true) && PscT.holds .one 2 16 7 false == (true, true, true)
-- a product that is wrong at one place: the claim on c fails
#guard (PscT.holds .two 2 16 7 true).1 == false

end Fmt.M2
