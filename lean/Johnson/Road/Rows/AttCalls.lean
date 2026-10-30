-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttCalls.lean: the numbers of the lookup of an attention sub-proof, in the
library's record, from the verifier's shape.

The library's points and weights of an attention segment (Inst/Model/Att/Points.lean) are cut from
the lookup's point by a record of numbers (Calls in Inst/Model/Att/Trace.lean): call c has 2^(a c)
keys, a tree has 2^Dk keys, a tree's number has sg bits. The verifier derives the same numbers for
its group of calls (Forest.Shape in OnBytes/Model/Forest.lean). This file takes the library's record
from the verifier's, and gathers what the library's theorems on the key forms ask of these numbers.

Main definitions.
 - callsOf fs: a c is the n of call number c of the verifier's list, Dk is dT, sg is rK.
 - CallsFit S fs: the library's condition Calls.OK at the sizes of the shape S; a piece of every
   family fits into a tree; the first two calls have the same size.
 - callsFitB S fs: the same as a test that can be run.
Main theorems: callsFit_of: if the test says yes, CallsFit holds.

What this file does not claim. That CallsFit holds of every shape that the verifier accepts: it is
tested at two configurations in Johnson/Road/Rows/TestAttCalls.lean. The
library numbers the trees of the calls in the order of the list; the verifier lays them by falling
size, ties in the order of the list. The two agree if the sizes do not rise along the list
(SameOrder), which is tested there too. That the programs lay their keys as the library's vector of
looked-up values does is not said here.


-/
import Johnson.Road.Lane5AttDef
import OnBytes.Model.AttentionShape
import Inst.Model.Att.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open OnBytes.Attention (Shape)
open Inst.Model.AttSeg (Calls Fam)

/-- The library's numbers of the lookup, from the verifier's. -/
def callsOf (fs : Model.Forest.Shape) : Calls :=
  ⟨fun c => (fs.calls.getD c.val default).n, fs.dT, fs.rK⟩

/-- What the library's theorems on the key forms ask of the numbers. -/
structure CallsFit (S : Shape) (fs : Model.Forest.Shape) : Prop where
  /-- the library's condition on the numbers -/
  ok : (callsOf fs).OK (scl := L5.sclOf S) (L5.dimOf S)
  /-- a piece of every family fits into a tree -/
  deep : ∀ u : Fam, u.l (L5.dimOf S) ≤ (callsOf fs).Dk
  /-- the first two calls have the same size -/
  same : (callsOf fs).a 0 = (callsOf fs).a 1

/-- The first tree of every call is the library's. -/
def SameOrder (fs : Model.Forest.Shape) : Prop :=
  ∀ c : Fin 4, fs.first.getD c.val 0 = (callsOf fs).first c

instance (fs : Model.Forest.Shape) : Decidable (SameOrder fs) :=
  inferInstanceAs (Decidable (∀ c : Fin 4, fs.first.getD c.val 0 = (callsOf fs).first c))

/-- CallsFit as a test. -/
def callsFitB (S : Shape) (fs : Model.Forest.Shape) : Bool :=
  decide ((∀ c, (L5.dimOf S).used c ≤ 2 ^ (callsOf fs).a c) ∧
    (∀ c, (callsOf fs).Dk ≤ (callsOf fs).a c) ∧
    (callsOf fs).NT ≤ 2 ^ (callsOf fs).sg ∧
    (∀ c, (callsOf fs).first c % (callsOf fs).trees c = 0) ∧
    10 ≤ (callsOf fs).Dk ∧
    Inst.Model.ExpOK ((L5.sclOf S).κ 0).sh (L5.dimOf S).u0 ∧
    (∀ u ∈ [Fam.m1, .d1, .m2, .d2, .w3, .x3, .f4], u.l (L5.dimOf S) ≤ (callsOf fs).Dk) ∧
    (callsOf fs).a 0 = (callsOf fs).a 1)

/-- **If the test says yes, CallsFit holds.** -/
theorem callsFit_of {S : Shape} {fs : Model.Forest.Shape} (h : callsFitB S fs = true) :
    CallsFit S fs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := of_decide_eq_true h
  refine ⟨Calls.OK.mk (scl := L5.sclOf S) h1 h2 h3 (fun c => Nat.dvd_of_mod_eq_zero (h4 c)) h5 h6,
    fun u => ?_, h8⟩
  cases u <;> exact h7 _ (by simp)

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.callsFit_of
