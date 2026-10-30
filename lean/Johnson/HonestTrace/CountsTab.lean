-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsTab.lean

The tables of a lookup's calls as functions into a type K with a cast of the natural numbers, and
the two readings of a call's numbers.

The library reads a call's table, its padding row and the logarithm of its number of rows off
h : Forest.Shape in two files:
FoNums (OnBytes/Tie/Pv/Lookup/Port/FoNums.lean) and Ends (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean).
The files of this folder state their laws with FoNums; the key vectors and joint vectors of the
three kinds of sub-proof are written with Ends. This file sets the two side by side.

Main definition: "tabOf": row t of call c's table, FoNums.tauN h c t, cast into K.
Main theorems:
* "tabOf_eq": for c below h.calls.size, tabOf K h c t is Ends.tauN h c t cast into K. It rests on
  Fo.tauN_eq (OnBytes/Tie/Pv/Lookup/Forest/FoJoinAt.lean).
* "t0N_eq", "kN_eq": Ends.t0N is FoNums.t0Of and Ends.kN is FoNums.kOf, for every c, by rfl.
* "calls_size": under FoNums.ok h the shape has h.NC calls, and h.NC is at least 1.

Limits. From h.calls.size on the two readings of a table's row are written with different defaults,
and nothing is said there. A row's number is cast into K as it is: in a ring of small
characteristic two rows can get one value.

Not claimed: anything on keys, counts, a prover or a verifier.

-/
import Johnson.HonestTrace.Counts
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinAt

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model

/-- Row t of call c's table, FoNums.tauN h c t, cast into K. -/
def tabOf (K : Type) [NatCast K] (h : Forest.Shape) : ℕ → ℕ → K :=
  fun c t => (FoNums.tauN h c t : K)

/-- For c below h.calls.size, tabOf K h c t is Ends.tauN h c t cast into K. -/
theorem tabOf_eq (K : Type) [NatCast K] (h : Forest.Shape) {c : ℕ} (hc : c < h.calls.size)
    (t : ℕ) : tabOf K h c t = (Ends.tauN h c t : K) := by
  unfold tabOf
  rw [Fo.tauN_eq h c t hc]

/-- The two readings of a call's padding row are one term. -/
theorem t0N_eq (h : Forest.Shape) (c : ℕ) : Ends.t0N h c = FoNums.t0Of h c := rfl

/-- The two readings of the logarithm of a call's number of rows are one term. -/
theorem kN_eq (h : Forest.Shape) (c : ℕ) : Ends.kN h c = FoNums.kOf h c := rfl

/-- Under FoNums.ok h the shape has h.NC calls, and at least one. -/
theorem calls_size {h : Forest.Shape} (hok : FoNums.ok h = true) :
    h.calls.size = h.NC ∧ 1 ≤ h.NC :=
  ⟨(Cb.Fo.ok_parts hok).1.2.2.2.2.2.2, (Cb.Fo.ok_parts hok).1.2.1⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.tabOf_eq
#print axioms OnBytes.HonestTrace.t0N_eq
#print axioms OnBytes.HonestTrace.kN_eq
#print axioms OnBytes.HonestTrace.calls_size
