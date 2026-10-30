-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsBool.lean.
The tests on public numbers of the lookup on the digits, as one test that can be run.

Main names:
  `sameCallB`, `sameCallsB`, `sameShapeB`: two calls, two lists of calls, two shapes are the same,
    field by field; `sameShapeB_eq`.
  `shapeTestZ tl`: the shape that `Forest.shape` makes of the record's two calls, with the record's
    numbers of padding keys filled in, is the record's shape; false where `Forest.shape` refuses.
  `rowsTestZ tl Fp`: each piece's rows lie inside its array.
  `zTestsB tl Fp`: the ten tests of `ZTests tl tl Fp` (FoLookDigitsRun) as one Bool.
  `zTests_of_test`: if it is true, `ZTests tl tl Fp` holds.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that the test is true at any record.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigitsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP

/-- Two calls are the same, field by field. -/
def sameCallB (a b : Call) : Bool :=
  decide (a.name = b.name) && decide (a.n = b.n) && decide (a.iota = b.iota) &&
    decide (a.k = b.k) && decide (a.kappa = b.kappa) && decide (a.fn = b.fn) &&
    decide (a.t0 = b.t0) && decide (a.tau = b.tau) && decide (a.pub = b.pub) &&
    decide (a.heavy = b.heavy)

theorem sameCallB_eq {a b : Call} (h : sameCallB a b = true) : a = b := by
  simp only [sameCallB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  cases a
  cases b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

/-- Two lists of calls are the same. -/
def sameCallsB : List Call → List Call → Bool
  | [], [] => true
  | a :: l, b :: l' => sameCallB a b && sameCallsB l l'
  | _, _ => false

theorem sameCallsB_eq : ∀ {l l' : List Call}, sameCallsB l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [sameCallsB, Bool.and_eq_true] at h
    rw [sameCallB_eq h.1, sameCallsB_eq h.2]
  | [], _ :: _, h => by simp [sameCallsB] at h
  | _ :: _, [], h => by simp [sameCallsB] at h

/-- Two shapes are the same, field by field. -/
def sameShapeB (a b : Forest.Shape) : Bool :=
  sameCallsB a.calls.toList b.calls.toList && decide (a.dT = b.dT) && decide (a.kT = b.kT) &&
    decide (a.NT = b.NT) && decide (a.rK = b.rK) && decide (a.NC = b.NC) &&
    decide (a.cK = b.cK) && decide (a.iota = b.iota) && decide (a.first = b.first) &&
    decide (a.callOf = b.callOf) && decide (a.pub = b.pub)

theorem sameShapeB_eq {a b : Forest.Shape} (h : sameShapeB a b = true) : a = b := by
  simp only [sameShapeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have h0' : a.calls = b.calls := Array.toList_inj.mp (sameCallsB_eq h0)
  cases a
  cases b
  simp only at h0' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst h0' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

/-- The record's shape is the one made of its two calls. -/
def shapeTestZ (tl : HTailF2) : Bool :=
  match Forest.shape #[tl.z1.call, tl.z2.call] tl.lidb with
  | .ok h0 => sameShapeB { h0 with pub := tl.f9.pub } tl.f9
  | .error _ => false

/-- Each piece's rows lie inside its array. -/
def rowsTestZ (tl : HTailF2) (Fp : Fork) : Bool :=
  (allPieces tl).all fun a => decide (a.2.r0 + a.2.Rp ≤ (Fp.trees.getD a.2.tree {}).R)

/-- The ten tests as one. -/
def zTestsB (tl : HTailF2) (Fp : Fork) : Bool :=
  tailTest tl && (pieceTest tl 0 && pieceTest tl 1) && (apartTest tl 0 && apartTest tl 1) &&
    callsTest tl && shapeTestZ tl && decide (2 ^ tl.f9.cK = tl.f9.NC) &&
    decide (5 ≤ tl.f9.kT + tl.f9.cK) &&
    (decide ((tl.zOf 0).call.n ≤ 63) && decide ((tl.zOf 1).call.n ≤ 63)) && coefTest tl Fp &&
    rowsTestZ tl Fp

theorem two_cases {p : ℕ → Prop} (h0 : p 0) (h1 : p 1) : ∀ q < 2, p q := by
  intro q hq
  rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
  · obtain rfl : q = 0 := by omega
    exact h0
  · rw [h]
    exact h1

theorem zTests_of_test {tl : HTailF2} {Fp : Fork} (h : zTestsB tl Fp = true) :
    ZTests tl tl Fp := by
  simp only [zTestsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2, a2'⟩, a3, a3'⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8, a8'⟩, a9⟩, a10⟩ := h
  refine ⟨a1, two_cases a2 a2', two_cases a3 a3', a4, fun h0 e => ?_, a6, a7, two_cases a8 a8', a9,
    fun a ha => ?_⟩
  · unfold shapeTestZ at a5
    rw [e] at a5
    exact sameShapeB_eq a5
  · exact of_decide_eq_true (List.all_eq_true.1 a10 a ha)

end Fo
