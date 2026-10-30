-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormRoomsAt.lean: THE FORM's HALF: THE ROOMS AND THE FRESH TABLE's ROWS AT THE
STATEMENT BEHIND THE FOLD, at the fold's own layout, the members as a list: the letters in which the
payer of a switch's reading asks them.

Main names.
  behind_front    a message behind the fold has the shape of the one in front.
  roomZ_at_foldT, roomM_at_foldT, fresh_at_foldT   THE THREE.

How. As in Johnson/Prover/Link/FormRooms.lean, off the fold's own test on the shape; the bounds
stand at the fold's layout's own two numbers, so nothing is asked of the carried layout's.

Limits. FoldFront is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormRooms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

variable {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
  {c : IoppStage} {n : Nat × Nat} {id : Nat}

/-- A message behind the fold has the shape of the one in front. -/
theorem behind_front (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat)
    (id : Nat) (rs : List Fmt.RoundView) (o : Nat) (x : OnBytes.Oracle)
    (h : (foldT t row L c n id rs).st.oracles[o]? = some x) :
    ∃ y, t.st.oracles[o]? = some y ∧ y.shape = x.shape := by
  have e := foldT_shape t row L c n id rs o
  rw [h] at e
  cases hy : t.st.oracles[o]? with
  | none =>
    rw [hy] at e
    cases e
  | some y =>
    rw [hy] at e
    exact ⟨y, rfl, (Option.some.inj e).symm⟩

/-- A member's number, off the list or off the array. -/
theorem toList_getD (A : Array Nat) (w a : Nat) : A.toList.getD w a = A.getD w a := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

/-- **The mask rows' room, behind the fold.** -/
theorem roomZ_at_foldT (H : FoldFront p j cur t row L c n id) (rs : List Fmt.RoundView) (w : Nat)
    (x : OnBytes.Oracle) (hw : w < L.members.toList.length)
    (hx : (foldT t row L c n id rs).st.oracles[L.members.toList.getD w 0]? = some x)
    (h0 : 0 < x.shape.maskRows) :
    ∃ f, (ioppFoldShape c L).layout.maskFirst.getD w none = some f ∧
      f + x.shape.maskRows ≤ 2 ^ (ioppFoldShape c L).layout.h := by
  have hw' : w < L.members.size := by simpa using hw
  obtain ⟨y, hy, ey⟩ := behind_front t row L c n id rs _ x hx
  rw [toList_getD, getD_any L.members w 0 noId hw'] at hy
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hM, _⟩ := front_fit H
  obtain ⟨y', hy', _, _, _, m2⟩ := hM w hw'
  have hy2 : t.st.oracles[L.members.getD w noId]? = some y' := hy'
  rw [hy] at hy2
  obtain rfl := Option.some.inj hy2
  rw [ey] at m2
  cases hf : (ioppFoldShape c L).layout.maskFirst.getD w none with
  | none =>
    rw [hf] at m2
    have m2' : x.shape.maskRows = 0 := m2
    omega
  | some f =>
    rw [hf] at m2
    exact ⟨f, rfl, m2.2⟩

/-- **The main rows' room, behind the fold.** -/
theorem roomM_at_foldT (H : FoldFront p j cur t row L c n id)
    (hk : ∀ i, i < L.members.size → L.kept.getD i false = false) (rs : List Fmt.RoundView) (w : Nat)
    (x : OnBytes.Oracle) (hw : w < L.members.toList.length)
    (hx : (foldT t row L c n id rs).st.oracles[L.members.toList.getD w 0]? = some x)
    (h0 : 0 < x.shape.mainRows) :
    ∃ f, (ioppFoldShape c L).layout.mainFirst.getD w none = some f ∧
      f + x.shape.mainRows ≤ 2 ^ (ioppFoldShape c L).layout.k := by
  have hw' : w < L.members.size := by simpa using hw
  obtain ⟨y, hy, ey⟩ := behind_front t row L c n id rs _ x hx
  rw [toList_getD, getD_any L.members w 0 noId hw'] at hy
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hM, _⟩ := front_fit H
  obtain ⟨y', hy', _, _, m1, _⟩ := hM w hw'
  have hy2 : t.st.oracles[L.members.getD w noId]? = some y' := hy'
  rw [hy] at hy2
  obtain rfl := Option.some.inj hy2
  rw [ey] at m1
  cases hf : (ioppFoldShape c L).layout.mainFirst.getD w none with
  | none =>
    rw [hf] at m1
    exact absurd ⟨h0, hk w hw'⟩ m1
  | some f =>
    rw [hf] at m1
    exact ⟨f, rfl, m1.2⟩

/-- **The fresh table's rows, behind the fold.** -/
theorem fresh_at_foldT (H : FoldFront p j cur t row L c n id) (rs : List Fmt.RoundView)
    (x : OnBytes.Oracle) (hx : (foldT t row L c n id rs).st.oracles[id]? = some x) :
    x.shape.maskRows = 2 ^ (ioppFoldShape c L).layout.h := by
  obtain ⟨y, hy, ey⟩ := behind_front t row L c n id rs _ x hx
  obtain ⟨o, ho, _, h2, _⟩ := (Own.foldMaskFits_iff _ _ _).1 H.maskFits
  rw [hy] at ho
  obtain rfl := Option.some.inj ho
  rw [← ey]
  exact h2

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.behind_front
#print axioms Johnson.Prover.Link.toList_getD
#print axioms Johnson.Prover.Link.roomZ_at_foldT
#print axioms Johnson.Prover.Link.roomM_at_foldT
#print axioms Johnson.Prover.Link.fresh_at_foldT
