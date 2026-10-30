-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidBaseTie.lean: from the smallness test's relation to BaseSegF, under one
named equation.

The library's base_of_relIn (Cb/Pv/Tail/Base.lean) gives Base at the symbols of the smallness test's
own letters, Λ.sym m, from the test's relation in front of its draw (relIn) and the three
inequalities Size.Uniq. BaseSegF (Johnson/Goal/Meaning/HidFamily.lean) is Base at the symbols that
sub-proof k reads in its messages at its seats. This file carries the one to the other under the
equation of the two families of symbols.

Main names:
  baseSegF_of_relIn   relIn Λ x m, Size.Uniq and Λ.sym m = symAt (s k) (seat k) (msgF k) give
    BaseSegF s seat msgF k.
  baseSeg_of_relIn   the same at one family of messages.
  ownAtF_of_relIn   then the list of sub-proof k is the total form of the test's own cells (cellsOf
    Λ m).

What is not claimed. THE EQUATION: that the symbols of the test's letters are what the witness's
messages hold at the layout's seats is a premise here. relIn of any run. The program does not import
this file.
-/
import Johnson.Goal.Meaning.HidFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.Rows.Norms
open Cb.Pv.Tail (Size Letters relIn)

variable {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {k : ℕ}

/-- **The smallness test's relation gives BaseSegF**, where its letters' symbols are the symbols
that the sub-proof reads in its messages. -/
theorem baseSegF_of_relIn {msgF : ℕ → Msgs} (Λ : Letters Cb.Gl.E (s k)) (p : ℕ) [CharP Cb.Gl.E p]
    (U : (s k).Uniq p) {x : Λ.X} {m : Λ.M} (R : relIn Λ x m)
    (e : Λ.sym m = symAt (s k) (seat k) (msgF k)) : BaseSegF s seat msgF k := by
  rw [baseSegF_def, ← e]
  exact Cb.Pv.Tail.base_of_relIn Λ p U R

/-- At one family of messages. -/
theorem baseSeg_of_relIn {msg : Msgs} (Λ : Letters Cb.Gl.E (s k)) (p : ℕ) [CharP Cb.Gl.E p]
    (U : (s k).Uniq p) {x : Λ.X} {m : Λ.M} (R : relIn Λ x m)
    (e : Λ.sym m = symAt (s k) (seat k) msg) : BaseSeg s seat msg k :=
  baseSegF_of_relIn (msgF := fun _ => msg) Λ p U R e

/-- Then the list of sub-proof k is the total form of the test's own cells. -/
theorem ownAtF_of_relIn {msgF : ℕ → Msgs} (Λ : Letters Cb.Gl.E (s k)) (p : ℕ) [CharP Cb.Gl.E p]
    (U : (s k).Uniq p) {x : Λ.X} {m : Λ.M} (R : relIn Λ x m)
    (e : Λ.sym m = symAt (s k) (seat k) (msgF k)) :
    ownAtF s seat msgF k = mzTot (Cb.Pv.Tail.cellsOf Λ m) :=
  ownAt_unique p U (e ▸ Cb.Pv.Tail.baseAt_of_relIn Λ p U R)

end Meaning

#print axioms Meaning.baseSegF_of_relIn
#print axioms Meaning.baseSeg_of_relIn
#print axioms Meaning.ownAtF_of_relIn
