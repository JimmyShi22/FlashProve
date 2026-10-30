-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanTestsFirst.lean: WHAT THE LINES OF K4's ROW AT THE TABLE OF JOINTS THAT GO
THROUGH THE PINS ASK OF THE PUBLIC PARAMETERS IN THE FIRST GROUP (the Lean structure `K4PlanFitF`,
Johnson/Road/K4/K4PinsEndFirst.lean), FROM TWO TESTS WITH CODE THAT WALK NO SYMBOL. The first group
has no seam in front of it: so nine of the eleven tests of Johnson/Road/K4/K4PlanTests.lean are not
asked. `K4PlanFitF` is one premise of `k4_own_endF` among many: the row is not paid by it. One Lean
structure and one theorem. Glue: calls; no draw, no count.

  `K4PlanTestsF`: `sitsInB`, and `symTieB` at every matrix.
  `k4PlanFitF_of_tests`: `K4PlanFitF` at q := the lookup's authors' public letters of the segment,
    ms any list, s := Meaning.sizesOf X, seat := seatBy (fLay D.layout num) X (Meaning.sizesOf X),
    the least bounds, first := 0.

CALLED, ours: `sitsIn_of_B` (K4PinsBools.lean) · `symsOne_of_layout` (SymsOfLayout.lean) ·
`covers_top`, `size_sizesOf` (K4PinsSizes.lean) · `keysFit_at_pub` (K4PinsKeysAt.lean). BESIDE THE
TESTS: `PublicSteps`, `RefPub`, the two lines on p, p.g < 12, `PlaceIs x p 0` (a theorem at the
place that is made: `ties_of_plan`, K4PinsScope.lean: not called here), three lines on numbers.

Limits. K04_law IS NOT PROVED BY THIS. NO RUN IS A PART OF THIS FILE. That p.g = 0 is asked nowhere
here: `K4PlanFitF` does not ask it. The letters num, arr, N, ms, seatT, D and the number hd are
free: their makers off the public parameters stand in no library file yet.
-/
import Johnson.Road.K4.K4PinsEndFirst
import Johnson.Road.K4.K4PinsKeysAt
import Johnson.Road.K4.K4PinsSizes
import Johnson.Road.K4.K4PinsBools
import Johnson.Road.K4.SymsOfLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (Mem)
open Meaning (seatBy fLay)
open Inst.Model.Layout (kRef hRef)

variable {X : Public} {p : Par} (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
  (enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
  (num arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **The tests.** Either field: a test with code says true. Neither walks a symbol. -/
structure K4PlanTestsF : Prop where
  sits : sitsInB (sigListCalls D rad x.link) seatT ms N m = true
  syms : ((List.range (Meaning.sizesOf X (2 * p.g)).NM).all fun μ =>
    symTieB (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) num arr N (2 * p.g) p.hp.tl
      X (Meaning.sizesOf X) μ) = true

variable {x D rad seatT posI oW enc wOf num arr ms N m}

/-- **`K4PlanFitF` from the two tests**, `PublicSteps`, `RefPub`, the two lines on p, p.g < 12,
`PlaceIs x p 0` and three lines on numbers. -/
theorem k4PlanFitF_of_tests {pol KL : ByteArray} {tk : Array Nat} (hd : ℕ)
    (T : K4PlanTestsF (X := X) (p := p) x D rad seatT posI oW enc wOf num arr ms N m)
    (St : PublicSteps pol KL X) (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg : p.g < 12) (P0 : PlaceIs x p 0)
    (hgr : m / stepOf X = p.g) (hm : m = 2 * p.g) (hhd : m ≠ hd) :
    K4PlanFitF (X := X) (p := p) x (pubAt X (m / stepOf X)) D rad seatT posI oW enc wOf arr ms N m
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf X)
      (seatBy (fLay D.layout num) X (Meaning.sizesOf X)) hd where
  sits := sitsIn_of_B T.sits
  covers := covers_top p.hp.tl
  place := P0
  keys := keysFit_at_pub St B hP hG hgr
  size := size_sizesOf hG hg
  syms := symsOne_of_layout _ num arr N (2 * p.g) p.hp.tl rfl fun μ hμ =>
    List.all_eq_true.1 T.syms μ (List.mem_range.2 hμ)
  segment := hm
  notHead := hhd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4PlanFitF_of_tests
