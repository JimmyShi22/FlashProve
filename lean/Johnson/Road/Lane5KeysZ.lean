-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5KeysZ.lean

At integer matrices the lookup clause of "the attention link is in order" is one statement in two
fields. "AttKeys S Z" (Lane5SplitA.lean) forms the looked-up values in the prime field; "KeysC S
(cellZ Z)" (Lane5KeysIff.lean) forms them in the protocol's field. They say the same. So the whole
meaning of the link is: its part without the lookup clause, and "every call's keys lie in its
table".

Main theorems:
* "keysC_cellZ_iff": KeysC S (cellZ Z) ↔ AttKeys S Z. For every shape: no premise.
* "inTables_iff_attKeys": under NumsA, LaidA, TabsEq, InsideA: (callsA S fs Z).InTables ↔ AttKeys
  S Z.
* **"attOrd_iff_calls"**: under the same: AttOrd S Z ↔ AttR0 S Z ∧ (callsA S fs Z).InTables.

How: the library's key_cast (the looked-up values over a ring are the images of those over the
integers); the map from the prime field into the protocol's field is one-to-one.
Use: from right to left it is the bridge (Lane5BridgeA.lean). From left to right it carries a
witness: a list Z that meets AttOrd meets both premises of the seam together.

What the clause weighs. kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean) is a term written for this library
over the verifier's records; the verifier holds no key vector. The keys of calls 1 and 2 are
formed from products of cells: the scores (query times key) and the accumulators (softmax weight
times value; denominator times output). So "every call's keys lie in its table", at kvA, holds all
of attention's products, and the part without the lookup clause is thin: small cells, index bits,
the row maximum, the denominator. The equivalence moves that weight; it does not carry it.

Not claimed: that some Z meets AttOrd at a shape; all that Lane5KeysIff.lean does not claim.

-/
import Johnson.Road.Lane5KeysIff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (Shape ACall)
open Inst.Model.AttSeg

/-- **The lookup clause at integer matrices, in the two fields.** -/
theorem keysC_cellZ_iff (S : Shape) (Z : Zs) : KeysC S (cellZ Z) ↔ AttKeys S Z := by
  constructor
  · intro H c X hX
    obtain ⟨ι, hι, e⟩ := H c X hX
    refine ⟨ι, hι, ?_⟩
    apply (algebraMap Cb.Gl.F Cb.Gl.E).injective
    rw [tC_cellZ, key_cast] at e
    rw [key_cast, map_intCast, map_intCast]
    exact e
  · intro H c X hX
    obtain ⟨ι, hι, e⟩ := H c X hX
    refine ⟨ι, hι, ?_⟩
    have e2 := congrArg (algebraMap Cb.Gl.F Cb.Gl.E) e
    rw [key_cast, map_intCast, map_intCast] at e2
    rw [tC_cellZ, key_cast]
    exact e2

variable {S : Shape} {cs : Fin 4 → ACall} {fs : Model.Forest.Shape}

/-- **"Every call's keys lie in its table" is the lookup clause.** -/
theorem inTables_iff_attKeys (N : NumsA S) (L : LaidA S cs) (T : TabsEq S fs)
    (hin : InsideA S cs) (Z : Zs) : (callsA S fs Z).InTables ↔ AttKeys S Z := by
  rw [callsA_eq]
  exact (keys_iff N L T hin (cellZ Z)).trans (keysC_cellZ_iff S Z)

/-- **The attention link is in order if and only if its part without the lookup clause holds and
every call's keys lie in its table.** -/
theorem attOrd_iff_calls (N : NumsA S) (L : LaidA S cs) (T : TabsEq S fs) (hin : InsideA S cs)
    (Z : Zs) : AttOrd S Z ↔ AttR0 S Z ∧ (callsA S fs Z).InTables := by
  rw [attOrd_iff_split, inTables_iff_attKeys N L T hin Z]

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.keysC_cellZ_iff
#print axioms OnBytes.Road.L5.inTables_iff_attKeys
#print axioms OnBytes.Road.L5.attOrd_iff_calls
