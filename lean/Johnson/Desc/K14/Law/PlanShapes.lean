-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PlanShapes.lean: THEOREMS: THE SEVEN STATEMENTS OF PlanShapesOwed.lean: the
sizes, the shapes and the samples of the shared chain's two sendings ("o_u and the first mask";
"o_omega and o_sp") in the plan's own letters.
  shapes_parK1   K1's list of shapes at one of the two sendings is the sending's own shapes.
  withU_cut      what goes out with o_u begins with G_u's notice.
  withOmega_split, withOmega_plain   what goes out with o_omega, by whether the split is needed.
  u0, o0, o1     the shape at place 0 of "send o_u"; at places 0 and 1 of "send o_omega" (a place 1
                 is there only where the split is needed).
  sizeU, sizeOmega, lengths, places, shapeAtU, sampledIff, sampled   THE SEVEN.
What is not claimed. Nothing of a run. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.PlanShapesOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt msgAt)

theorem shapes_parK1 (Q : P14) (piece : Nat) (part : String) (sent : Array OracleNotice) :
    shapesOf (parK1 Q piece part sent) = sent.toList.map (·.shape) := by
  simp [shapesOf, VerifiableInference.Desc.K1.Par.sent, parK1]

theorem withU_cut {S : LinShape} {sentU : Array OracleNotice} (h : withU S = some sentU) :
    ∃ rest, linWithU S = some rest ∧
      sentU = #[(⟨S.fold.u, S.fold.leafClass⟩ : OracleNotice)] ++ rest := by
  unfold withU at h
  obtain ⟨rest, hr, e⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rest, hr, e.symm⟩

theorem withOmega_split {S : LinShape} (h : S.sharedSplitNeeded = true) :
    withOmega S = #[⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] := by
  simp [withOmega, linMessageOmega, h]

theorem withOmega_plain {S : LinShape} (h : S.sharedSplitNeeded = false) :
    withOmega S = #[⟨S.omega, S.omegaLeafClass⟩] := by
  simp [withOmega, linMessageOmega, h]

/-- From a shape read with "?" to shapeAt and sampledAt. -/
theorem shapeAt_of {P : VerifiableInference.Desc.K1.Par} {k : Fin (shapesOf P).length}
    {s : OracleShape} (h : (shapesOf P)[k.val]? = some s) : shapeAt P k = s := by
  obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 h
  exact e

theorem sampled_of {P : VerifiableInference.Desc.K1.Par} {k : Fin (shapesOf P).length}
    {s : OracleShape} (h : (shapesOf P)[k.val]? = some s) : sampledAt P k ↔ s.answers ≠ 0 := by
  obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 h
  unfold sampledAt msgAt
  rw [e]
  exact Iff.rfl

theorem u0 (Q : P14) (part : String) {sentU : Array OracleNotice} (h : withU Q.S = some sentU) :
    (shapesOf (parK1 Q 2 part sentU))[0]? = some Q.S.fold.u := by
  obtain ⟨rest, _, rfl⟩ := withU_cut h
  rw [shapes_parK1]
  simp

theorem o0 (Q : P14) (part : String) :
    (shapesOf (parK1 Q 5 part (withOmega Q.S)))[0]? = some Q.S.omega := by
  rw [shapes_parK1]
  cases hs : Q.S.sharedSplitNeeded with
  | true => simp [withOmega_split hs]
  | false => simp [withOmega_plain hs]

/-- A place 1 at "send o_omega" is there only where the split is needed. -/
theorem split_of_one (Q : P14) (part : String)
    (h : 1 < (shapesOf (parK1 Q 5 part (withOmega Q.S))).length) :
    Q.S.sharedSplitNeeded = true := by
  cases hs : Q.S.sharedSplitNeeded with
  | true => rfl
  | false =>
    rw [shapes_parK1, withOmega_plain hs] at h
    simp at h

theorem o1 (Q : P14) (part : String)
    (h : 1 < (shapesOf (parK1 Q 5 part (withOmega Q.S))).length) :
    (shapesOf (parK1 Q 5 part (withOmega Q.S)))[1]? = some Q.S.sharedSplit := by
  rw [shapes_parK1, withOmega_split (split_of_one Q part h)]
  simp

/-! ## The seven -/

theorem sizeU : SizeUOwed := by
  intro S sentU h hm
  obtain ⟨rest, hr, rfl⟩ := withU_cut h
  have h1 : rest.size = 1 := by
    unfold linWithU at hr
    cases hx : linMaskNotice S.testU S.fold.leafClass with
    | none => simp [hm, hx] at hr
    | some a =>
      simp [hm, hx] at hr
      simp [← hr]
  simp [h1]

theorem sizeOmega : SizeOmegaOwed := by
  intro S h
  rw [withOmega_split h]
  rfl

theorem lengths : LengthsOwed := by
  intro Q sentU
  constructor
  · rw [shapes_parK1]
    simp
  · rw [shapes_parK1]
    simp

theorem places : PlacesOwed := by
  intro Q sentU
  refine ⟨fun h => ?_, ?_, fun h => ?_⟩
  · obtain ⟨x, _⟩ := List.getElem?_eq_some_iff.1 (u0 Q "o_u and the first mask" h)
    exact x
  · obtain ⟨x, _⟩ := List.getElem?_eq_some_iff.1 (o0 Q "o_omega and o_sp")
    exact x
  · rw [shapes_parK1, withOmega_split h]
    simp

theorem shapeAtU : ShapeUOwed := by
  intro Q sentU h h0
  exact shapeAt_of (k := ⟨0, h0⟩) (u0 Q "o_u and the first mask" h)

theorem sampledIff : SampledIffOwed := by
  intro Q sentU
  refine ⟨fun h h0 => ?_, fun h0 => ?_, fun h1 => ?_⟩
  · exact sampled_of (k := ⟨0, h0⟩) (u0 Q "o_u and the first mask" h)
  · exact sampled_of (k := ⟨0, h0⟩) (o0 Q "o_omega and o_sp")
  · exact sampled_of (k := ⟨1, h1⟩) (o1 Q "o_omega and o_sp" h1)

theorem sampled : SampledOwed := by
  intro Q sentU hok
  simp only [LinShape.ok, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, _⟩, _⟩, _⟩, _⟩, _⟩, c7⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, c14⟩, _⟩ := hok
  simp only [FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at c1
  simp only [LinShape.vectorMessageOk, Bool.and_eq_true, decide_eq_true_eq] at c7
  obtain ⟨iU, iO, iS⟩ := sampledIff Q sentU
  refine ⟨fun h h0 => (iU h h0).2 ?_, fun h0 => (iO h0).2 ?_, fun h1 => (iS h1).2 ?_⟩
  · have := c1.1.2
    omega
  · have := c7.2
    omega
  · have hs := split_of_one Q "o_omega and o_sp" h1
    simp only [hs, Bool.not_true, Bool.false_or, LinShape.splitMessageOk, Bool.and_eq_true,
      decide_eq_true_eq] at c14
    have := c14.1.2
    omega

end Desc.K14.Law
