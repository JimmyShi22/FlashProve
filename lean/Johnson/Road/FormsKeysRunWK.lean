-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRunWK.lean: the hypotheses of the theorems on the layout of the committed
weights (Johnson/Road/FormsKeysWLay.lean) at the made-up shape hR and at the numbers of the two
examples that ship with the prover; and the two layouts side by side at these examples' numbers.

The theorems layout_eq and unitOf_eq begin "if the shape of the weights and the library's parameters
agree in nine numbers (SizedW), and wsLayOf returns a layout". This file shows the first half at
three pairs of a shape and parameters, as theorems, and runs the second half.

Two kinds of evidence. sizedW_R, sizedW_KS and sizedW_KF are theorems. A line "#guard" is evaluated
when this file is compiled, by Lean's interpreter, and the compilation fails if the value is not
true. It is a run and no theorem: nothing that only a guard shows can be used in a proof.

What is run, at each of the two examples, on the lines of its parameter file as
Johnson/Road/FormsKeysRunK.lean writes them out (linesKS, linesKF):
 1. the verifier's own scan and layout (polLayout) return, and wsLayOf returns on the shape of the
    weights, the switch and the number of column bits that the verifier's public part hands it
    (weightShape P y, y.h.p3, P.lkW: the call in publicOf, OnBytes/Model/VerifyPublic.lean),
 2. that shape of the weights is the shape written here by hand from hKS or hKF and the size of the
    vocabulary, for which SizedW is proved; the model has mixtures of experts,
 3. the verifier's list of units is the library's, field by field (unitsP against unitsL of
    Johnson/Road/FormsKeysRunW.lean), and unitOf finds every kind of every layer at the library's
    number (w1Lay),
 4. the numbers of units, of column bits and of rows; at the full-size example the last two are the
    library's kRef and hRef,
 5. at the small example, on a sample of the index tuples of four units: the cell of a weight's
    digit through the verifier's own settling, against the library's place (w2Unit of
    Johnson/Road/FormsKeysRunW.lean).
Points 3 and 4 repeat at these numbers what layout_eq and unitOf_eq prove for all numbers; they are
a test of the statements' reading, not a part of a proof.

What is not claimed. No Lean code compares the lines with the files on the disk. The files hold
public parameters, no weights. Nothing is said on any claim, on how W is committed, or on other
numbers. The program does not import this file.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.FormsKeysRunW
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (WsShape WsLay wsLayOf)
open OnBytes.Model.Verify (polLayout weightShape)
open OnBytes.Model.Layer (Shape)
open Inst.Model (Params ppref)
open Inst.Model.Layout (units first off kRef hRef)

/-- The numbers on which the layout of the committed weights depends, from a shape and the size of
the vocabulary. -/
def shapeV (h : Shape) (V : ℕ) : WsShape := { shapeW h with V := V }

/-- The library's parameters for a shape and the size of the vocabulary. -/
def parV (h : Shape) (V : ℕ) : Params := { (dimOf h).P with V := V }

/-- At the made-up shape hR the shape of the weights and the library's parameters agree. -/
theorem sizedW_R : SizedW (shapeW hR) (parW hR) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the small example's numbers. -/
theorem sizedW_KS : SizedW (shapeV hKS 512) (parV hKS 512) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the full-size example's numbers, with the library's reference parameters themselves. -/
theorem sizedW_KF : SizedW (shapeV hKF 202048) ppref :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two lists of units are one; the verifier finds the unit of each kind of each of L layers at
the number that the library's order gives it; the units' rows end at or before the verifier's number
of rows. -/
def w1Lay (L : ℕ) (lay : WsLay) (P : Params) : Bool :=
  unitsP lay == unitsL P lay.lk &&
  ((List.range L).all fun l =>
    (kindsOf l).zipIdx.all fun x => lay.unitOf x.1 l == some (first P l + x.2)) &&
  lay.unitOf 12 L == some (first P L) && lay.unitOf 13 L == some (first P L + 1) &&
  decide (off lay.lk (units P) (units P).length ≤ lay.m0)

/-- From the lines of a parameter file: whether the shape of the weights that the verifier's public
part hands to wsLayOf is s; whether the model has mixtures of experts; w1Lay; w2Unit on every
step-th index tuple of the units with the numbers ns; the numbers of units, of column bits and of
rows. Refuses where the verifier refuses. -/
def runWK (pol : ByteArray) (s : WsShape) (P : Params) (step : ℕ) (ns : List ℕ) :
    Except String (Bool × Bool × Bool × Bool × ℕ × ℕ × ℕ) := do
  let (Q, y) ← polLayout pol
  let lay ← wsLayOf (weightShape Q y) y.h.p3 Q.lkW
  pure (sameW (weightShape Q y) s, y.h.p3, w1Lay s.L lay P,
    ns.all fun n => w2Unit placeL step lay P n, lay.U.size, lay.lk, lay.m0)

/-! ## The run -/

/- the small example: points 1 to 5 -/
#guard (match runWK (textK linesKS) (shapeV hKS 512) (parV hKS 512) 997 [1, 2, 13, 15] with
  | .ok r => r == (true, true, true, true, 66, 11, 59392)
  | .error _ => false)

/- the full-size example: points 1 to 4 (no unit is sampled: the fourth mark is true of the empty
list) -/
#guard (match runWK (textK linesKF) (shapeV hKF 202048) ppref 1 [] with
  | .ok r => r == (true, true, true, true, 386, kRef, hRef)
  | .error _ => false)
#guard (kRef, hRef) == (18, 3076096)

/- at the made-up shape hR wsLayOf returns (also run in Johnson/Road/FormsKeysRunW.lean) -/
#guard (wsLayOf (shapeW hR) true 6).isOk

#print axioms sizedW_R
#print axioms sizedW_KS
#print axioms sizedW_KF

end OnBytes.Road
