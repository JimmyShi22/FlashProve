-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsPlanOf.lean: OF THE NINE FIELDS OF `K4PlanFit`
(Johnson/Road/K4/K4PinsEnd.lean) THREE ARE LEFT AS TESTS: `SitsIn`, `SymsOne`, `SeamFit`. The other
six are theorems or lines on two numbers, at these letters: q := the lookup's authors' public
letters of the segment · s := the meaning's authors' sizes off the public parameters · nM, nR, nC :=
the least bounds · first := 0. One theorem: a gathering of calls (K4PinsKeysAt.lean,
K4PinsSizes.lean). No draw, no count.

  **`planFit_of_tests`**: `K4PlanFit x (pubAt X (m / stepOf X)) … 0 (Meaning.sizesOf X) seat hd`,
    from:
    `PublicSteps` · `RefPub` · the two lines on p · p.g < 12 · `PlaceIs x p 0` (a theorem at the
    place that `layAt X m` finds: `ties_of_plan`, Johnson/Road/K4/K4PinsScope.lean) · three lines on
    numbers (m / stepOf X = p.g · m = 2 p.g · m is not the head's segment) · AND THE THREE TESTS.

OBJECT: none of its own. USER: none yet; meant: the assembly of K4's law. LETTERS: those of
K4PinsEnd.lean but q, s, nM, nR, nC, first.

Limits. K04_law IS NOT PROVED BY THIS. THE THREE TESTS STAY PREMISES: they are conditions on public
letters that must be evaluated, or drawn from what the verifier itself tests. `SymsOne` and
`SeamFit` are asked at s := `Meaning.sizesOf X`.
-/
import Johnson.Road.K4.K4PinsEnd
import Johnson.Road.K4.K4PinsKeysAt
import Johnson.Road.K4.K4PinsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (Mem)
open Inst.Model.Layout (kRef hRef)

/-- **`K4PlanFit`, from the three tests.** -/
theorem planFit_of_tests {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}
    {rows cols : ℕ} (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (seat : ∀ k, Fin (_root_.Meaning.sizesOf X k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hd : ℕ)
    (St : PublicSteps pol KL X) (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg : p.g < 12) (P0 : PlaceIs x p 0)
    (hgr : m / stepOf X = p.g) (hm : m = 2 * p.g) (hhd : m ≠ hd)
    (sits : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (syms : SymsOne (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) p.hp.tl arr N
      (2 * p.g) (_root_.Meaning.sizesOf X (2 * p.g)) (seat (2 * p.g)))
    (seam : SeamFit arr ms N (_root_.Meaning.sizesOf X) seat D.codes (pubAt X (m / stepOf X)).y
      p.g) :
    K4PlanFit (X := X) (p := p) x (pubAt X (m / stepOf X)) D rad seatT posI oW enc wOf arr ms N m
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (_root_.Meaning.sizesOf X) seat
      hd where
  sits := sits
  covers := covers_top p.hp.tl
  place := P0
  keys := keysFit_at_pub St B hP hG hgr
  size := size_sizesOf hG hg
  syms := syms
  seam := seam
  segment := hm
  notHead := hhd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planFit_of_tests
