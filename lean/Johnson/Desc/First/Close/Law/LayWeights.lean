-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayWeights.lean: which oracle messages count as kept, as folded and as
masked at the layout that the verifier's own function returns (`Statement.layout`,
OnBytes/Iop/Ground.lean). Statements and proofs.

BatApply.lean, beside this file, adds a row's coefficients up under three weights: `keptWeight`
(OnBytes/Iop/RowLaws.lean), `foldedWeight` and `maskedWeight`, each 1 or 0, read off a layout. Here
they are read off the statement.
  `idxOf_lt`, `laySizes_at`: the place that is found for a member; the size at a place.
  `first_isSome`: a place of the members holds a block just if the member has a size.
  `weights_member`: at a member: it counts as kept just if its mark says so; as folded just if it is
    not kept and has main rows; as masked just if it has mask rows.
  `weights_none`: at an oracle message that is no member all three weights are 0.

Limits. Nothing on place bits: that a member's table has as many as the group's is a fact on the
members' codes, which is not treated. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayAll
import Johnson.Desc.First.Close.Law.BatApply

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw

variable {K : Type} [CommRing K]

/-- The place that is found for a number in an array is a place of the array. -/
theorem idxOf_lt (a : Array Nat) (o i : Nat) (h : a.idxOf? o = some i) : i < a.size := by
  obtain ⟨l⟩ := a
  rw [List.idxOf?_toArray] at h
  exact (List.idxOf?_eq_some_iff.1 h).1

/-- The size at a place of the members. -/
theorem laySizes_at (S : Statement) (G : Group) (part : Part) (i : Nat) (hi : i < G.members.size) :
    (laySizes S G part)[i]? = some
      (if S.has (G.members.getD i noId) part && !(part == .main && G.kept.getD i false) then
        some (S.rowBits (G.members.getD i noId) part) else none) := by
  unfold laySizes
  rw [Array.getElem?_map, Array.getElem?_range, if_pos hi]
  rfl

/-- A place of the members holds a block just if the member has a size. -/
theorem first_isSome (S : Statement) (G : Group) (part : Part) (i : Nat)
    (hi : i < G.members.size) :
    ((layBlocks (laySizes S G part)).1.getD i none).isSome =
      (S.has (G.members.getD i noId) part && !(part == .main && G.kept.getD i false)) := by
  have hs := laySizes_at S G part i hi
  cases hc : (S.has (G.members.getD i noId) part && !(part == .main && G.kept.getD i false)) with
  | true =>
    rw [hc, if_pos rfl] at hs
    obtain ⟨f, hf⟩ := layBlocks_all _ i _ hs
    rw [(getD_some _ _ _).2 hf]
    rfl
  | false =>
    rw [hc] at hs
    simp only [Bool.false_eq_true, if_false] at hs
    cases hb : (layBlocks (laySizes S G part)).1.getD i none with
    | none => rfl
    | some f =>
      obtain ⟨s, a1, -, -⟩ :=
        (layBlocks_laid (laySizes S G part)).block i f ((getD_some _ _ _).1 hb)
      rw [hs] at a1
      cases a1

/-- **THE WEIGHTS AT THE LAYOUT THAT THE VERIFIER's OWN FUNCTION RETURNS**, at an oracle message
that is a member: it counts as kept just if its mark says so; as folded just if it is not kept and
has main rows; as masked just if it has mask rows. -/
theorem weights_member (S : Statement) (g : Nat) (L : GroupLayout) (h : S.layout g = some L)
    (o i : Nat) (hf : L.find o = some i) :
    keptWeight (K := K) L o = (if L.kept.getD i false then 1 else 0) ∧
    foldedWeight (K := K) L o = (if S.has o .main && !L.kept.getD i false then 1 else 0) ∧
    maskedWeight (K := K) L o = (if S.has o .mask then 1 else 0) := by
  cases hG : S.groups[g]? with
  | none =>
    unfold Statement.layout at h
    rw [hG] at h
    cases h
  | some G =>
    rw [layout_eq S g G hG] at h
    obtain rfl := Option.some.inj h
    have hi : i < G.members.size := idxOf_lt G.members o i hf
    have ho : G.members.getD i noId = o := find_getD _ o i hf
    have hM := first_isSome S G .main i hi
    have hZ := first_isSome S G .mask i hi
    rw [ho] at hM hZ
    refine ⟨?_, ?_, ?_⟩
    · unfold keptWeight
      rw [hf]
    · unfold foldedWeight
      rw [hf]
      dsimp only at hM ⊢
      cases hk : G.kept.getD i false with
      | true => simp
      | false =>
        rw [hk] at hM
        simp only [Bool.false_eq_true, if_false]
        cases hb : (layBlocks (laySizes S G .main)).1.getD i none with
        | none =>
          rw [hb] at hM
          have : S.has o .main = false := by simpa using hM.symm
          simp [this]
        | some f =>
          rw [hb] at hM
          have : S.has o .main = true := by simpa using hM.symm
          simp [this]
    · unfold maskedWeight
      rw [hf]
      dsimp only at hZ ⊢
      cases hb : (layBlocks (laySizes S G .mask)).1.getD i none with
      | none =>
        rw [hb] at hZ
        have : S.has o .mask = false := by simpa using hZ.symm
        simp [this]
      | some f =>
        rw [hb] at hZ
        have : S.has o .mask = true := by simpa using hZ.symm
        simp [this]

/-- At an oracle message that is no member all three weights are 0. -/
theorem weights_none (L : GroupLayout) (o : Nat) (hf : L.find o = none) :
    keptWeight (K := K) L o = 0 ∧ foldedWeight (K := K) L o = 0 ∧
      maskedWeight (K := K) L o = 0 := by
  unfold keptWeight foldedWeight maskedWeight
  rw [hf]
  exact ⟨rfl, rfl, rfl⟩

end OnBytes.LayLaw

#print axioms OnBytes.LayLaw.weights_member
#print axioms OnBytes.LayLaw.weights_none
