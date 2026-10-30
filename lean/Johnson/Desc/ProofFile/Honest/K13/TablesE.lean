-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/TablesE.lean: kind K13, the members' batching: THE TWO TABLES OF
EACH ROW OF THE PILE, THEIR HALVING AT A CHALLENGE AND A ROUND's THREE COEFFICIENTS, IN THE
PROGRAM's FIELD (`OnBytes.E`: three machine words). Definitions with code; no theorem. GENERAL IN
THE SIZE. It imports OnBytes/Iop/Batt.lean alone, so that it can be compiled without the library's
mathematics; that the reading of each is the like text of Johnson/Desc/K13/Honest/ is not shown
here.

Why. The kind's job (`k13Job`, Part.lean of this folder) reckons in the library's field: numbers
near 2 ^ 64, which a compiled program holds as big numbers. These texts reckon in machine words,
make a row's weights once, and are cut so that the tables can be made once and halved from round to
round.
Main names:
  `K13Kept`: **the type of what a job that keeps its tables hands on**: the two tables of each row
    of the pile. It stands here so that a file that lays room for it need import little.
  `loopBy` · `sumLoopE f n a`: a + f (n - 1) + ... + f 0: a loop.
  `rowWeightE g i`: the row's weight at matrix row i: the sum of its tensors' entries.
  `rowTabE nR k mat g`: **the table of a row**: for each of the 2 ^ k columns the sum over the nR
    rows of the matrix of weight times entry; the weights once, in an array. mat: the matrix, by row
    and by the column's number.
  `eqTE` · `scaleTE`: the table of the equality vector at a point; every entry times c.
  `tabsE nR k mat pile a`: **both tables of each row of the pile.**
  `foldTE` · `foldAllE`: **the halving**: the first variable set to a challenge.
  `quadTE` · `quadAllE`: **a round's three coefficients**, off the tables as they stand.

THE LIBRARY's PROGRAM HAS TEXTS THAT DO WHAT TWO OF THESE DO: `halve` (OnBytes/Iop/Lkp.lean) and
`foldStepE` (OnBytes/Field/Mle.lean; it keeps an odd last entry, which is dropped here) beside
`foldTE`; `eqTable` (Mle.lean; an array) beside `eqTE`. THEY ARE TYPED ANEW because each text here
follows, sign for sign, the text of Johnson/Desc/K13/Honest/Moves.lean that it is to be read as
(`foldT`, `eqT`). No theorem ties them to the program's.
`foldTE`, `quadTE` and `quadAllE` are not loops: they call themselves to a depth of half a table's
length, or of the pile's. "General in the size" is said of the types; nothing is said on the stack
at a large k.

What is not claimed. Anything on time. The definitions are none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import OnBytes.Iop.Batt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E TensorRow Tensor zeroE oneE addE subE mulE powE)

/-- What is kept: the two tables of each row of the pile, in the program's field. -/
abbrev K13Kept : Type := List (List E × List E)

/-- a, then f (n - 1), ..., f 0 laid to it by `add`, as a loop. -/
@[specialize] def loopBy {α : Type} (add : α → α → α) (f : Nat → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => loopBy add f n (add a (f n))

/-- a + f (n - 1) + ... + f 0 in the program's field. -/
def sumLoopE (f : Nat → E) (n : Nat) (a : E) : E := loopBy addE f n a

/-- The row's weight at matrix row i. -/
def rowWeightE (g : List Tensor) (i : Nat) : E := g.foldl (fun a t => addE a (t.entry i)) zeroE

/-- **The table of a row of the pile**: the weights once, then each column's sum. -/
def rowTabE (nR k : Nat) (mat : Nat → Nat → E) (g : List Tensor) : List E :=
  let A : Array E := Array.ofFn (n := nR) fun i => rowWeightE g i
  (List.range (2 ^ k)).map fun j => sumLoopE (fun i => mulE (A.getD i zeroE) (mat i j)) nR zeroE

/-- The table of the equality vector at a point: the first coordinate is the lowest bit. -/
def eqTE : List E → List E
  | [] => [oneE]
  | z :: zs => (eqTE zs).flatMap fun v => [mulE v (subE oneE z), mulE v z]

/-- Every entry times c. -/
def scaleTE (c : E) (T : List E) : List E := T.map fun v => mulE c v

/-- **The two tables of each row of the pile**, once a is sampled. -/
def tabsE (nR k : Nat) (mat : Nat → Nat → E) (pile : List TensorRow) (a : E) :
    List (List E × List E) :=
  List.ofFn fun q : Fin pile.length =>
    (scaleTE (powE a q) (eqTE (pile.get q).psi), rowTabE nR k mat (pile.get q).g)

/-- A table with its first variable set to g: entries 2 e and 2 e + 1 become one. -/
def foldTE (g : E) : List E → List E
  | a :: b :: l => addE a (mulE g (subE b a)) :: foldTE g l
  | _ => []

/-- **The rows' tables with the first variable set.** -/
def foldAllE (g : E) (S : List (List E × List E)) : List (List E × List E) :=
  S.map fun p => (foldTE g p.1, foldTE g p.2)

/-- The coefficients of 1, X, X^2 of the sum of the products, entry by entry, of two tables whose
first variable is set to X. -/
def quadTE : List E → List E → E × E × E
  | a0 :: a1 :: A, b0 :: b1 :: B =>
    let r := quadTE A B
    (addE (mulE a0 b0) r.1,
      addE (addE (mulE a0 (subE b1 b0)) (mulE (subE a1 a0) b0)) r.2.1,
      addE (mulE (subE a1 a0) (subE b1 b0)) r.2.2)
  | _, _ => (zeroE, zeroE, zeroE)

/-- **The three coefficients of a round, over the rows.** -/
def quadAllE : List (List E × List E) → E × E × E
  | [] => (zeroE, zeroE, zeroE)
  | p :: S =>
    let a := quadTE p.1 p.2
    let r := quadAllE S
    (addE a.1 r.1, addE a.2.1 r.2.1, addE a.2.2 r.2.2)

end ProofFile.Honest.K13
