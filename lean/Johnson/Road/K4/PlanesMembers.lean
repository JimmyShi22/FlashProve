-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PlanesMembers.lean: THE LOOKUP's THREE CLAIMS THAT READ THE PLANES ARE MEMBERS OF
THE LIST OF K4's RUN "front". At a layers' link the driver's order (`orderCuts`,
Johnson/Desc/First/Driver/Chain.lean) has no run "planes": there the three claims are K4's own text
(`planesParts`, OnBytes/Desc/First/K4/Claims.lean: group 11 of "front"). Statements and proofs: read
off two laws (`formsFrontWith_some`, `front_some`, OnBytes/Desc/First/K4/ClaimsLaws.lean);
kin of `mem_front` there, which has the leaves' own claim as a letter and does not give pp. The
statements stand at the plain function `formsFrontWith`; that the block's run hands on just its list
is proved (`block_front`, `front_ok`, Johnson/Desc/First/K4/BlockLaws.lean).

`planesParts v fo` returns a pair pp. pp.1 IS NO CLAIM OF ITS OWN: it is what is kept in the own
claim of the lookup's leaves' sumcheck: the member of the list is
`fo.leaves.rowForm oneE pp.1`. pp.2 holds the second and the third claim.

  `planes_members`: where `formsFrontWith rows P g o F` returns (fs, G), with or without the
    lookup's own claims (rows): `planesParts o.v o.H.fo` returns some pp; the leaves' own claim at
    pp.1 is in fs; every form of pp.2 is in fs.
  `planesParts_some`: `planesParts` UNFOLDED: where it returns pp: the three tables "b-bits-0",
    "b-bits-1", "b-pin" have their numbers; the public test `Forest.planeCols` on the heard shape at
    lmb holds; the planes' forms at 0 and at 1 (`planesAt`: the form at 0 reads "b-bits-0" alone,
    the form at 1 "b-bits-1" alone) and the pins' form return, each column read by `U3at` and only
    below kbm; and pp is: what is kept := the form at 0, scaled by `fo.leavesA`; the second claim :=
    the slot `fo.sBit` less the form at 1; the third := the pins' form: the sum of the pins' columns
    less (2 ^ v - padding), that difference taken in the natural numbers and through `toUInt64`.
  `planes_zero`: so, where every form of fs has a property Z (meant: is worth 0 in a world; nothing
    in the statement is 0), these three have it.

Limits. NOTHING ON WHAT THE THREE FORMS MEAN: that they are worth 0 in a world with true reads of
the three tables gives what the lookup's law asks at the layers is a theorem in other files. THE
FIRST MEMBER HOLDS MORE THAN pp.1 (`Psc.rowForm`: the window's hiding coefficients, eps times the
target less the start form, eps times what is kept, the claim): that it is worth 0 says nothing of
pp.1 without eps ≠ 0 and the leaves' sumcheck. Nothing on the ledger G. "Have their numbers" is
`tabAt`'s first hit by name; `U3at`'s own docstring says which wrong indices it does not refuse.
Nothing here shows that the run returns. Nothing on soundness.
-/
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Pub Own)
open OnBytes.Desc.First.K4 (formsFrontWith planesParts planesAt need formsFrontWith_some
  front_some)

/-- **The planes' three claims are members of the list of "front".** -/
theorem planes_members {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsFrontWith rows P g o F = some (fs, G)) :
    ∃ pp, planesParts o.v o.H.fo = some pp ∧ o.H.fo.leaves.rowForm oneE pp.1 ∈ fs.toList ∧
      ∀ f ∈ pp.2, f ∈ fs.toList := by
  obtain ⟨sh, pp, l, _, _, _, a2, a3, a4, _, _, _⟩ := formsFrontWith_some h
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, _, _, _, _, _, b6, _, e⟩ := front_some a3
  rw [a2] at b6
  cases b6
  refine ⟨pp, a2, ?_, fun f hf => ?_⟩
  · rw [a4, e]
    simp
  · rw [a4, e]
    simp [hf]

/-- **`planesParts`, unfolded.** -/
theorem planesParts_some {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : planesParts v fo = some pp) :
    ∃ tB0 tB1 tP at0 at1 count,
      v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧ v.tabAt "b-pin" = some tP ∧
      (Forest.planeCols fo.shape v.y.h.lmb).toBool = true ∧
      planesAt fo v.y.h.lmb 0 (fun e x =>
        if x < v.y.kbm then v.U3at (if e == 0 then tB0 else tB1) x else none) = some at0 ∧
      planesAt fo v.y.h.lmb 1 (fun e x =>
        if x < v.y.kbm then v.U3at (if e == 0 then tB0 else tB1) x else none) = some at1 ∧
      (List.range (fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb))).foldlM
        (fun (f : Aff) c => (if c < v.y.kbm then v.U3at tP c else none).map fun x => f + x)
        (Aff.ofConst (negE (ofF (2 ^ fo.shape.v - fo.shape.padding).toUInt64))) = some count ∧
      pp = (Aff.scale at0 fo.leavesA, [Aff.slot fo.sBit - at1, count]) := by
  unfold planesParts at h
  obtain ⟨tB0, e0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB1, e1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tP, eP, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨count, hc, h⟩ := Option.bind_eq_some_iff.mp h
  have hb : (Forest.planeCols fo.shape v.y.h.lmb).toBool = true := by
    unfold need at hn
    split at hn
    · assumption
    · cases hn
  exact ⟨tB0, tB1, tP, at0, at1, count, e0, e1, eP, hb, h0, h1, hc, (Option.some.inj h).symm⟩

/-- Where every form of the list has a property, the planes' three have it. -/
theorem planes_zero {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsFrontWith rows P g o F = some (fs, G)) (Z : Aff → Prop)
    (hz : ∀ f ∈ fs.toList, Z f) :
    ∃ pp, planesParts o.v o.H.fo = some pp ∧ Z (o.H.fo.leaves.rowForm oneE pp.1) ∧
      ∀ f ∈ pp.2, Z f := by
  obtain ⟨pp, h1, h2, h3⟩ := planes_members h
  exact ⟨pp, h1, hz _ h2, fun f hf => hz f (h3 f hf)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planes_members
#print axioms OnBytes.Road.K4.planesParts_some
#print axioms OnBytes.Road.K4.planes_zero
