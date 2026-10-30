-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Measure.lean
(kind K9's soundness lemma): DEFINITIONS ONLY: the measures in which the lemma is
stated. No theorem. The program does not import this file.

The setting is that of OnBytes/Model/HideLaws.lean: a reading (Reading K) takes the program's
elements of E, three machine words each, to a commutative ring K and keeps 0, 1, sum, difference and
product; a world (World K) gives a value to every unknown of a claim: to each slot, and to each
entry of each virtual row. Fork.total is the value of what the ledger has gathered.

New here:
  claimValue    the value of a claim (Johnson/Desc/Claim.lean): its form and its runs.
  expo          the exponent of chi under which a claim is added.
  claimsSum     the sum over a list of claims of chi ^ exponent * value.
  Bound         THE DATA TO WHICH THE PROVER IS BOUND when chi is drawn: every element of every
                committed array, and the entries of the segment's mask row.
  worldAt       the world that such data give at a ledger: the unknown under slot j is
                shown_j - factor_j * mask_j; entry i of a virtual row is the row's public weights
                coef applied to column i of its array.
  weightAt, termValue, eqValue   the value of the one equation (K9.Equation) on such data.
  sums          what of a ledger its value reads.
  termsSum, TermsOk   a polynomial in chi as a list of (exponent, coefficient).
The test "no weight, no coefficient and no constant in the ledger" is K9.ledgerEmpty
(Batch/Kind.lean), which the draw's block asks.
A theorem in these measures says no more than they do.

-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import OnBytes.Model.TreesLaws
import Johnson.Desc.Claim
import Johnson.Desc.First.Batch.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Equation)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## Claims -/

/-- The value of a claim in a world: the form's value and the runs' values. -/
def claimValue (W : World K) (cl : Claim) : K :=
  cl.form.value ρ W + (cl.runs.toList.map (Run2.value ρ W)).sum

/-- The exponent of chi under which a claim is added. n: the number of claims in the plan. c: the
claim's own number. -/
def expo (n c : Nat) (cl : Claim) : Nat :=
  match cl.eqFirst with
  | none => c
  | some first => n + first

/-- The sum over a list of claims of x ^ exponent * value; c: the first claim's number. -/
def claimsSum (W : World K) (x : K) (n c : Nat) (l : List Claim) : K :=
  sumFrom (fun i cl => x ^ expo n i cl * claimValue ρ W cl) c l

/-! ## The data to which the prover is bound -/

/-- The data behind the commitments that the chain has received before chi is drawn. A LETTER HERE:
that these are what the commitments bind the prover to is another law's. -/
structure Bound (K : Type) where
  /-- element (i, c) of the array of a name that a link has committed to: link, name, i, c -/
  cell : Nat → String → Nat → Nat → K
  /-- entry j of the segment's mask row -/
  mask : Nat → K

/-- Entry i of virtual row r of array number t: the row's weights coef on the array's R rows,
applied to column i. fr: what the arrays hold beside the weights L (treesFrame). -/
def entryAt (arrayOf : Array (Nat × String)) (fr : Array (HTree × Array (HRow × Nat)))
    (D : Bound K) (t r i : Nat) : K :=
  ∑ j ∈ Finset.range (fr.getD t default).1.R,
    ρ.val (((fr.getD t default).2.getD r default).1.coef.getD j zeroE) *
      D.cell (arrayOf.getD t (0, "")).1 (arrayOf.getD t (0, "")).2 j i

/-- The world of the data D at the ledger F of the segment L. Every slot's scalar is read with an
entry of the segment's mask row (D.mask). A slot whose scalar is masked elsewhere (a merge's end
value: by an entry of the request's index-mask message) is meant to have the coefficient 0 in the
ledger (the test "K9.free-slot"); the ledger's value then reads nothing under it. Not shown here. -/
def worldAt (L : LinkCtx) (F : Fork) (D : Bound K) : World K :=
  F.worldOf ρ D.mask (entryAt ρ L.arrayOf (treesFrame F.trees) D)

/-! ## The one equation -/

/-- The weight that IndexWeights (OnBytes/Iop/ReqRows.lean) puts on index i: the written-out
vector's entry, or the product over the bits t of hi[t] or lo[t], as bit t of i is 1 or 0. At an
index from 2^bits on a product form's weight repeats (the low bits alone are seen); the theorems use
it below 2^bits alone. -/
def weightAt (w : IndexWeights) (i : Nat) : K :=
  match w.values with
  | some v => ρ.val (v.getD i zeroE)
  | none =>
    ∏ t ∈ Finset.range w.lo.size,
      if i.testBit t then ρ.val (w.hi.getD t zeroE) else ρ.val (w.lo.getD t zeroE)

/-- The rows and columns of an array in the layout; (0, 0) if the layout has no such array. -/
def dimsOf (c : ChainCheck) (born : Nat) (name : String) : Nat × Nat :=
  match (c.rows.layout.link.getD born []).find? fun A => A.name == name with
  | some A => (A.sizeI, A.sizeC)
  | none => (0, 0)

/-- The value of a term: the sum over the array's elements (i, c) of
scale * onRows[i] * onColumns[c] * element. -/
def termValue (dims : Nat → String → Nat × Nat) (D : Bound K) (t : ReqTerm) : K :=
  ∑ i ∈ Finset.range (dims t.born t.array).1, ∑ c ∈ Finset.range (dims t.born t.array).2,
    ρ.val t.scale * weightAt ρ t.onRows i * weightAt ρ t.onColumns c * D.cell t.born t.array i c

/-- The left side of the one equation "... = 0" on the data D. -/
def eqValue (dims : Nat → String → Nat × Nat) (D : Bound K) (q : Equation) : K :=
  (q.terms.toList.map (termValue ρ dims D)).sum + maskValue ρ D.mask q.onMasks + ρ.val q.constant

/-! ## What of a ledger its value reads -/

/-- The weights L of every virtual row with their first column, the coefficients LS, the constant,
and the number of slots. A step that leaves these alone leaves the ledger's value alone in every
world (Law/Ledger.lean: total_of_sums). -/
def sums (F : Fork) : Array (Array (Array E × Nat)) × Array E × E × Nat :=
  (F.trees.map fun X => X.rows.map fun r => (r.L, r.L0), F.LS, F.c0, F.ns)

/-! ## A polynomial in chi -/

/-- A list of terms (exponent, coefficient), at x. -/
def termsSum (t : List (ℕ × K)) (x : K) : K := (t.map fun y => x ^ y.1 * y.2).sum

/-- The exponents differ from each other and are at most d. -/
def TermsOk (t : List (ℕ × K)) (d : ℕ) : Prop := (t.map (·.1)).Nodup ∧ ∀ y ∈ t, y.1 ≤ d

end VerifiableInference.Desc.K9L
