-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormRooms.lean: THE FORM's HALF: FROM THE FOLD's FRONT (FoldFront,
Johnson/Prover/Link/FormFold.lean): each member's rows have room in the layout's two tables; the
fresh table has 2 ^ h rows; the fold's output passes the tests on its own numbers.

Why. The reading of the old rows at a code switch asks these of the fold's output and of the
statement (Tw.L9.readOld's last tests). They are no new facts on the carried record: the fold's own
test on the shape has asked them.

Main names.
  stageAt_says    the stage that the front names has the stage's two numbers.
  front_fit       the front's test on the shape, in sentences (Own.FoldShapeFit).
  noKept_all      no member is kept, at every number.
  roomM_of_front, roomZ_of_front, fresh_of_front   THE THREE.
  foldT_shape     the fold turns no message's shape.
  shapeFits_foldOut   the tests on the output's own numbers.
  foldOut_says    what the output says of itself.

Limits. FoldFront is a premise. Nothing on the book, the tree or the columns that the reading asks
for.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFold
import Johnson.Desc.Own.FoldMean
import Johnson.Desc.Own.Symbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem stageAt_says {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {c : IoppStage}
    (h : stageAt p j cur = some c) : c.k = cur.k ∧ c.h = cur.h := by
  unfold stageAt at h
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl⟩

variable {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
  {c : IoppStage} {n : Nat × Nat} {id : Nat}

/-- The front's test on the shape, in sentences. -/
theorem front_fit (H : FoldFront p j cur t row L c n id) :
    Own.FoldShapeFit t.st (ioppFoldShape c L) := (Own.foldShapeFits_iff _ _).1 H.shape

/-- A member's number, whichever number stands for «none». -/
theorem getD_any (A : Array Nat) (w a b : Nat) (h : w < A.size) : A.getD w a = A.getD w b := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- **No member is kept, at every number.** -/
theorem noKept_all (H : FoldFront p j cur t row L c n id)
    (hk : ∀ i, i < L.members.size → L.kept.getD i false = false) (w : Nat) :
    L.kept.getD w false = false := by
  obtain ⟨_, _, _, _, _, _, _, _, h5, _⟩ := front_fit H
  have h5' : L.kept.size = L.members.size := h5
  by_cases hw : w < L.members.size
  · exact hk w hw
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

/-- **Each member's main rows have room.** -/
theorem roomM_of_front (H : FoldFront p j cur t row L c n id) (ek : L.k = c.k)
    (hk : ∀ i, i < L.members.size → L.kept.getD i false = false) (w : Nat) (x : OnBytes.Oracle)
    (hw : w < L.members.size) (hx : t.st.oracles[L.members.getD w 0]? = some x)
    (h0 : 0 < x.shape.mainRows) :
    ∃ f, L.mainFirst.getD w none = some f ∧ f + x.shape.mainRows ≤ 2 ^ L.k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hM, _⟩ := front_fit H
  obtain ⟨y, hy, _, _, m1, _⟩ := hM w hw
  have hy' : t.st.oracles[L.members.getD w noId]? = some y := hy
  rw [getD_any L.members w noId 0 hw, hx] at hy'
  obtain rfl := Option.some.inj hy'
  have m1' : (match L.mainFirst.getD w none with
      | some f => (0 < x.shape.mainRows ∧ L.kept.getD w false = false) ∧
          f + x.shape.mainRows ≤ 2 ^ c.k
      | none => ¬ (0 < x.shape.mainRows ∧ L.kept.getD w false = false)) := m1
  cases hf : L.mainFirst.getD w none with
  | none =>
    rw [hf] at m1'
    exact absurd ⟨h0, hk w hw⟩ m1'
  | some f =>
    rw [hf] at m1'
    exact ⟨f, rfl, by rw [ek]; exact m1'.2⟩

/-- **Each member's mask rows have room.** -/
theorem roomZ_of_front (H : FoldFront p j cur t row L c n id) (eh : L.h = c.h) (w : Nat)
    (x : OnBytes.Oracle) (hw : w < L.members.size)
    (hx : t.st.oracles[L.members.getD w 0]? = some x) (h0 : 0 < x.shape.maskRows) :
    ∃ f, L.maskFirst.getD w none = some f ∧ f + x.shape.maskRows ≤ 2 ^ L.h := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hM, _⟩ := front_fit H
  obtain ⟨y, hy, _, _, _, m2⟩ := hM w hw
  have hy' : t.st.oracles[L.members.getD w noId]? = some y := hy
  rw [getD_any L.members w noId 0 hw, hx] at hy'
  obtain rfl := Option.some.inj hy'
  have m2' : (match L.maskFirst.getD w none with
      | some f => 0 < x.shape.maskRows ∧ f + x.shape.maskRows ≤ 2 ^ c.h
      | none => x.shape.maskRows = 0) := m2
  cases hf : L.maskFirst.getD w none with
  | none =>
    rw [hf] at m2'
    omega
  | some f =>
    rw [hf] at m2'
    exact ⟨f, rfl, by rw [eh]; exact m2'.2⟩

/-- **The fresh table has 2 ^ h rows.** -/
theorem fresh_of_front (H : FoldFront p j cur t row L c n id) (eh : L.h = c.h)
    (x : OnBytes.Oracle) (hx : t.st.oracles[id]? = some x) : x.shape.maskRows = 2 ^ L.h := by
  obtain ⟨o, ho, _, h2, _⟩ := (Own.foldMaskFits_iff _ _ _).1 H.maskFits
  rw [hx] at ho
  obtain rfl := Option.some.inj ho
  rw [eh]
  exact h2

/-- The fold turns no message's shape. -/
theorem foldT_shape (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat)
    (id : Nat) (rs : List Fmt.RoundView) (o : Nat) :
    ((foldT t row L c n id rs).st.oracles[o]?).map (·.shape) =
      (t.st.oracles[o]?).map (·.shape) := by
  show ((t.st.oracles.modify id fun x => { x with spentAsMask := true })[o]?).map (·.shape) = _
  rw [Array.getElem?_modify]
  by_cases e : id = o
  · rw [if_pos e, Option.map_map]
    rfl
  · rw [if_neg e]

/-- **The tests on the fold's output's own numbers.** -/
theorem shapeFits_foldOut (H : FoldFront p j cur t row L c n id) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hr : rR.length = c.k) :
    Own.shapeFits (foldOut t row L c id (rE :: rR)) = true := by
  obtain ⟨_, _, _, _, _, h2, _, _, h5, h6, h7, _⟩ := front_fit H
  have a2 : c.h ≤ c.k := h2
  have a5 : L.kept.size = L.members.size := h5
  have a6 : L.mainFirst.size = L.members.size := h6
  have a7 : L.maskFirst.size = L.members.size := h7
  show ((rR.map drawnOf).length == c.k && decide (c.h ≤ c.k) &&
    L.kept.size == L.members.size && L.mainFirst.size == L.members.size &&
    L.maskFirst.size == L.members.size) = true
  simp [hr, a2, a5, a6, a7]

/-- What the fold's output says of itself. -/
theorem foldOut_says (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (id : Nat)
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) :
    (foldOut t row L c id (rE :: rR)).masks = 2 ∧ (foldOut t row L c id (rE :: rR)).fresh = id ∧
      (foldOut t row L c id (rE :: rR)).layout = { L with k := c.k, h := c.h } ∧
      ((∀ w, L.kept.getD w false = false) →
        (foldOut t row L c id (rE :: rR)).keptRows = 0) := by
  refine ⟨rfl, rfl, rfl, fun hk => ?_⟩
  show (List.range L.members.size).foldl (fun m i =>
    if L.kept.getD i false then
      m + (((spent t.st id).oracles[L.members.getD i noId]?).map (·.shape.mainRows)).getD 0
    else m) 0 = 0
  have : ∀ (l : List Nat) (m : Nat), l.foldl (fun m i =>
      if L.kept.getD i false then
        m + (((spent t.st id).oracles[L.members.getD i noId]?).map (·.shape.mainRows)).getD 0
      else m) m = m := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons a l ih =>
      intro m
      rw [List.foldl_cons, hk a]
      exact ih m
  exact this _ 0

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.stageAt_says
#print axioms Johnson.Prover.Link.front_fit
#print axioms Johnson.Prover.Link.getD_any
#print axioms Johnson.Prover.Link.noKept_all
#print axioms Johnson.Prover.Link.roomM_of_front
#print axioms Johnson.Prover.Link.roomZ_of_front
#print axioms Johnson.Prover.Link.fresh_of_front
#print axioms Johnson.Prover.Link.foldT_shape
#print axioms Johnson.Prover.Link.shapeFits_foldOut
#print axioms Johnson.Prover.Link.foldOut_says
