-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Model/TwoLines.lean: the two clauses of the acceptance policy on a position's cost, (B4)
and (Z) of the head's field relation, as a family of two arrays on a cube.

Definitions, statements and proofs. No protocol occurs here. The rule for a second zero test on a
block's challenges (Cb/G6/Rider/Carrier.lean) has a source `OnCubes` and a target `AtCoords`, both
over free arrays. This file fills the arrays with `linesFam` (Cb/Pv/Head/TwoLines.lean): member 0 is
`dB4`, member 1 is `dZ` (Inst/Model/Head/Trace.lean); both hold the public indicator of the counted
positions as a factor. The cube has lt variables, lt a free letter.
Main names:
  `twoFam cells req`: the family. `cells` and `req` are free letters: how the cells are read off a
    state and a tuple of messages, and what the head reads of the request and the policy, off the
    state alone.
  `two_source`: `OnCubes` of the family is `LinesAll`. `two_target`: `AtCoords` of the family, both
    members at one choice sel of coordinates, is `LinesAtPt` at the point t ↦ pt (sel t). Both hold
    by definition.
  `linesAll_jc`: at lt = 10, `LinesAll` is the clause jc of the head's field relation `RF`: at every
    i < nT both `dB4` and `dZ` are 0.
  `linesAll_none`: if the request has no counted position, `LinesAll` and `LinesAtPt` hold of all
    cells, at every lt and every point.
  `two_not_back`: the target does not give the source. For lt ≥ 1 there are a request, cells and a
    point with `LinesAtPt` and without `LinesAll`.
Limits: nothing on which block draws the point, on its counts, or on who tests the target. `dB4` and
`dZ` are at the reference sizes of Inst/Model/Head/Index.lean whatever lt is: the sum in `dZ` runs
over the reference vocabulary, and the indicator counts positions below 1,023.
-/
import Cb.Pv.Head.TwoLines
import Blocks.LookupRel
import Cb.G6.Rider.Carrier

set_option autoImplicit false

namespace Cb.Rider
open Blocks Finset Inst.Model Inst.Model.Head Cb.Pv.Head

section TwoLines
variable {K : Type} [Field K] {St M : Type} (cells : St → M → Cells K) (req : St → Req)

/-- The family of two members. -/
def twoFam : Fin 2 → St → M → ℕ → K := fun i st m => linesFam (cells st m) (req st) i

/-- The source. -/
theorem two_source (lt : ℕ) (st : St) (m : M) :
    OnCubes (fun _ : Fin 2 => lt) (twoFam cells req) st m ↔ LinesAll (cells st m) (req st) lt :=
  Iff.rfl

/-- The target. -/
theorem two_target (lt : ℕ) (sel : ℕ → ℕ) (st : St) (pt : ℕ → K) (m : M) :
    AtCoords (fun _ : Fin 2 => lt) (fun _ => sel) (twoFam cells req) st pt m ↔
      LinesAtPt (cells st m) (req st) lt fun t => pt (sel t) :=
  Iff.rfl

/-- At the reference number of positions the source is the clause jc of the head's field
relation. -/
theorem linesAll_jc (t : Cells K) (y : Req) :
    LinesAll t y 10 ↔ ∀ i < nT, dB4 t y i = 0 ∧ dZ t y i = 0 :=
  ⟨fun h i hi => ⟨h 0 i hi, h 1 i hi⟩, fun h c i hi => by
    unfold linesFam
    split
    · exact (h i hi).1
    · exact (h i hi).2⟩

/-- If no position is counted, source and target hold whatever the cells. -/
theorem linesAll_none (t : Cells K) (y : Req) (h : ∀ i, y.rhoC i = 0) (lt : ℕ) (u : ℕ → K) :
    LinesAll t y lt ∧ LinesAtPt t y lt u := by
  have z : ∀ c a, linesFam t y c a = 0 := by
    intro c a
    unfold linesFam dB4 dZ
    rw [h a, Int.cast_zero, zero_mul, zero_mul, ite_self]
  exact ⟨fun c a _ => z c a, fun c => ext_zero_of_forall (fun a _ => z c a) u⟩

/-- The target does not give the source: a request whose one counted position is 0, cells with
`dB4` = 1 there, and the vertex 1 as the point. -/
theorem two_not_back {lt : ℕ} (h : 1 ≤ lt) :
    ∃ (t : Cells K) (y : Req) (u : ℕ → K), LinesAtPt t y lt u ∧ ¬ LinesAll t y lt := by
  have h1 : 1 < 2 ^ lt := Nat.one_lt_two_pow (by omega)
  let y : Req := ⟨0, 1, fun _ => 0, ⟨0, 0, 0⟩⟩
  let t : Cells K :=
    ⟨fun _ _ => 0, fun _ _ => 0, fun n _ => if n = 99 then -127 else -128, fun _ _ => 0⟩
  have r1 : y.rhoC 1 = 0 := by decide
  have r0 : y.rhoC 0 = 1 := by decide
  refine ⟨t, y, cubePt lt 1, fun c => ?_, fun g => ?_⟩
  · rw [ext_cubePt lt _ h1]
    unfold linesFam dB4 dZ
    rw [r1, Int.cast_zero, zero_mul, zero_mul, ite_self]
  · have g0 := g 0 0 (Nat.two_pow_pos _)
    have e : linesFam t y 0 0 = 1 := by
      unfold linesFam dB4
      rw [if_pos rfl, r0]
      simp [hidC, hidK, Ledger.b256, sum_range_succ, Dv, t, y]
      norm_num
    rw [e] at g0
    exact one_ne_zero g0

end TwoLines

end Cb.Rider

#print axioms Cb.Rider.two_source
#print axioms Cb.Rider.two_target
#print axioms Cb.Rider.linesAll_jc
#print axioms Cb.Rider.linesAll_none
#print axioms Cb.Rider.two_not_back
