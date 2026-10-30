-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerLayTests.lean: THE TESTS ON PUBLIC DATA UNDER THE CALLER OF THE
LOOKUP ON A LAYERS' LINK's CALLS (LayOK, K3CallerLay.lean) AS ONE BOOL WITH CODE, and the theorem
that its yes gives LayOK. Definitions with code, statements and proofs. NO SOUNDNESS IS CLAIMED.

Main names:
  `tabDiff h c row`: in how many rows u < 2^k_c the verifier's row of call c, as a number, is not
    the integer row u.
  `tabsB h`: at each of the eight calls: k_c is 8 at call 3 and 16 else, and tabDiff against the
    library's reference table of that call is 0.
  `layB h`: eight calls · DF.lT ≤ dT · each call has room for the library's key vector · tabsB.
  `layAt X i`: the place of the lookup on the calls of the layers' link i, with the record that the
    kind's own parameters make in the place of the plan's.
  `layOK_of`, `layOK_at`: a yes of layB gives LayOK.
Limits. A yes of layB at a public record is an evaluation's matter. The tables are compared as
numbers, row by row in the same order: more than LayOK.tabs asks.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open Inst.Model.All (DF)
open Inst.Model.FFSeg (lut aC)

/-- In how many rows the verifier's row of call c, as a number, is not the integer `row u`. -/
def tabDiff (h : Forest.Shape) (c : Nat) (row : Nat → Int) : Nat :=
  ((List.range (2 ^ FoNums.kOf h c)).filter
    fun u => ((FoNums.tauN h c u : Nat) : Int) != row u).length

/-- The bits of a row's number in the library's table of call c. -/
def tabBits (c : Fin 8) : Nat := if c = 3 then 8 else 16

def tabsB (h : Forest.Shape) : Bool :=
  (List.finRange 8).all fun c =>
    FoNums.kOf h c.val == tabBits c && tabDiff h c.val (lut Inst.Model.tbRef c).row == 0

def roomB (h : Forest.Shape) : Bool :=
  (List.finRange 8).all fun c => decide (aC DF c ≤ FoNums.nOf h c.val)

def layB (h : Forest.Shape) : Bool :=
  h.NC == 8 && decide (DF.lT ≤ h.dT) && roomB h && tabsB h

/-- A group has two links where attention has a link of its own. -/
def stepOf (X : Verify.Public) : Nat := if X.p4 then 2 else 1

/-- The place, with the record that the kind's own parameters make. -/
def layAt (X : Verify.Public) (i : Nat) : Option Place :=
  if i % stepOf X == 0 && i != stepOf X * X.NGr then
    (lookAt X i false).bind fun x =>
      (P.ofPlace (Params.settingOf X.P.frame) false x).shape.map fun h => { x with fs := h }
  else none

theorem tabDiff_zero {h : Forest.Shape} {c : Nat} {row : Nat → Int} (e : tabDiff h c row = 0)
    {u : Nat} (hu : u < 2 ^ FoNums.kOf h c) : ((FoNums.tauN h c u : Nat) : Int) = row u := by
  unfold tabDiff at e
  have h0 := List.eq_nil_of_length_eq_zero e
  by_contra hne
  have hm : u ∈ (List.range (2 ^ FoNums.kOf h c)).filter
      fun u => ((FoNums.tauN h c u : Nat) : Int) != row u :=
    List.mem_filter.2 ⟨List.mem_range.2 hu, by simpa using hne⟩
  rw [h0] at hm
  exact List.not_mem_nil hm

/-- **A yes of the test on the tables gives LayOK's clause.** -/
theorem tabs_of {h : Forest.Shape} (e : tabsB h = true) (c : Fin 8) (u : ℕ)
    (hu : u < 2 ^ Cb.LdLkp.Port.kOf h c) :
    ∃ v ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
      ((FoNums.tauN h c u : ℕ) : Cb.Gl.E) = algebraMap Cb.Gl.F Cb.Gl.E v := by
  have hc := List.all_eq_true.1 e c (List.mem_finRange c)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hc
  have hu' : u < 2 ^ FoNums.kOf h c.val := hu
  have er := tabDiff_zero hc.2 hu'
  refine ⟨(((lut Inst.Model.tbRef c).row u : ℤ) : Cb.Gl.F), ⟨u, ?_, rfl⟩, ?_⟩
  · show u < 2 ^ (if c = 3 then 8 else 16)
    rw [hc.1] at hu'
    exact hu'
  · rw [← er, map_intCast, Int.cast_natCast]

/-- **A yes of the one Bool gives LayOK.** -/
theorem layOK_of {set : Params.Setting} {x : Place}
    (hs : (P.ofPlace set false x).shape = some x.fs) (e : layB x.fs = true) : LayOK set x := by
  unfold layB at e
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at e
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := e
  exact ⟨hs, h1, h2,
    fun c => of_decide_eq_true (List.all_eq_true.1 h3 c (List.mem_finRange c)), tabs_of h4⟩

/-- **At a link of the public record the one Bool is all that is asked.** -/
theorem layOK_at {X : Verify.Public} {i : ℕ} {x : Place} (hx : layAt X i = some x)
    (e : layB x.fs = true) : LayOK (Params.settingOf X.P.frame) x := by
  refine layOK_of ?_ e
  unfold layAt at hx
  split at hx
  · obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
    subst hx
    exact hh
  · cases hx

#print axioms tabs_of
#print axioms layOK_of
#print axioms layOK_at

end VerifiableInference.Desc.First.Look
