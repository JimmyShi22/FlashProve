-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Plan/ShapeRows.lean: WHERE addTreesF (OnBytes/Model/Tail.lean), the routine that, by
its own docstring, the sub-proofs call to lay their arrays, RETURNS, EACH MATRIX's SHAPE HAS A THIRD
OF ITS ROWS OF CELLS, ROUNDED UP, AS ITS ROWS OF SYMBOLS. General: no planner, no scope, no premise
but the return.

  `GoodN x`, `Good T`: an entry of a sub-proof's list of arrays bears a shape with that equation, or
    none (the default shape has it too: 0 = (0 + 2) / 3); every entry of the list does.
  `goodN_none`: an entry without a shape has it.
  `good_addN`, `good_addP`: the two routines that add an array keep it: t2AddN lays no shape; t2AddP
    lays ShP.of m k a, whose text has mS := (m + 2) / 3 (OnBytes/Model/FormF.lean).
  `goodN_getD`: so has whatever getD reads off such a list.
  **`addTreesF_mS`** : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T') → ∀ mu, mu < tl'.NM →
    (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3.
  `addTrees_mS`: the same under the name by which the sub-proofs' plans call the routine.
How. addTreesF refuses unless the list that it is handed is empty; each of its four loops and two
single calls adds by t2AddN or t2AddP; shp[mu] is read off the list that is left. Which array bears
which matrix is not needed. The routine's own last test (`addTreesF_fits`,
OnBytes/Tie/Pv/Tail/EndSame.lean) turns the shape's rows of cells into the matrix's. The walk is
that of `addTreesF_u3` (Johnson/Goal/Meaning/PlanPort.lean).
Limits. That the routine returns anywhere is not said. Where gtTree[mu] names an entry without a
shape the equation holds idly: the routine's last test has then forced a matrix without rows (0 = 2
/ 3). Nothing on soundness.

-/
import Johnson.Goal.Meaning.PlanPort
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Plan

open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- The entry's shape, or the default shape where it bears none, has the equation. -/
def GoodN (x : N2) : Prop := (x.p.getD {}).mS = ((x.p.getD {}).m + 2) / 3

/-- Every entry of the list has it. -/
def Good (T : Tail2) : Prop := ∀ x ∈ T.nt, GoodN x

/-- An entry without a shape has it. -/
theorem goodN_none (ec a : Nat) (foreign : Bool) :
    GoodN { ec := ec, a := a, foreign := foreign } := by
  simp [GoodN]

/-- t2AddN lays no shape. -/
theorem good_addN {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) (g : Good T) : Good T' := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨_, e3⟩ := Prod.mk.inj e2
    subst e3
    intro x hx
    rcases Array.mem_push.1 hx with h1 | rfl
    · exact g x h1
    · exact goodN_none ec a foreign

/-- t2AddP lays ShP.of. -/
theorem good_addP {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : Good T) : Good T' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨_, e3⟩ := Prod.mk.inj e2
      subst e3
      intro x hx
      rcases Array.mem_push.1 hx with h1 | rfl
      · exact g x h1
      · exact (rfl : (m + 2) / 3 = (m + 2) / 3)

/-- What getD reads off such a list has it. -/
theorem goodN_getD {T : Tail2} (g : Good T) (j : Nat) : GoodN (T.nt.getD j {}) := by
  rw [Array.getD_eq_getD_getElem?]
  cases hj : T.nt[j]? with
  | none => exact (rfl : (0 : Nat) = (0 + 2) / 3)
  | some x => exact g x (Array.mem_of_getElem? hj)

/-- **Behind addTreesF each matrix's shape has a third of its rows of cells, rounded up, as its rows
of symbols.** -/
theorem addTreesF_mS {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3 := by
  have hfit : OnBytes.Tie.Pv.Tail.Port.Fits tl' :=
    (OnBytes.Tie.Pv.Tail.Port.addTreesF_fits tl tl' F G T T' nU aTX hb hbLine h).1
  unfold addTreesF at h
  obtain ⟨h0, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  -- the list that is handed in is empty
  have G0 : Good { T with link := true } := by
    intro x hx
    have hE : T.nt.isEmpty = true := by simpa using h0
    have hz : T.nt.size = 0 := Array.isEmpty_iff_size_eq_zero.1 hE
    obtain ⟨i, hi, _⟩ := Array.mem_iff_getElem.1 hx
    have hi' : i < T.nt.size := hi
    omega
  have K1 : Good T1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => Good s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨_, hs⟩ := ok_of_jp hs
        exact ⟨_, (Except.ok.inj hs).symm, good_addN hP hI⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl G0 h1
  have K2 : Good T2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun _ (s : MProd Fork Tail2) => Good s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, good_addP hP hI⟩)
    (List.range tl.pkMat.size) [] _ _ rfl K1 h2
  have K3 : Good T3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun _ (s : MProd Fork Tail2) => Good s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, good_addP hP hI⟩)
    (List.range tl.pxMat.size) [] _ _ rfl K2 h3
  have KB : Good TB := good_addN hB (good_addN hZ K3)
  have K4 : Good T4 := forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => Good s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, good_addP hP hI⟩)
    (List.range tl.ft.size) [] _ _ rfl KB h4
  intro mu hmu
  have hNM : tl'.NM = tl.NM := by rw [← e1]
  have hm : mu < tl.NM := by rw [← hNM]; exact hmu
  have hs : tl'.shp.getD mu {} = (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {} := by
    rw [← e1]
    show ((Array.range tl.NM).map fun mu =>
      (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {}).getD mu {} = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hm]
    rfl
  have hg : GoodN (T4.nt.getD (tl.gtTree.getD mu 0) {}) := goodN_getD K4 _
  unfold GoodN at hg
  rw [← hs] at hg
  rw [hg, (hfit mu hmu).1]

/-- The same under the name by which the sub-proofs' plans call the routine. -/
theorem addTrees_mS {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTrees F T nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3 :=
  addTreesF_mS h

end OnBytes.Road.K4.Plan

#print axioms OnBytes.Road.K4.Plan.goodN_none
#print axioms OnBytes.Road.K4.Plan.good_addN
#print axioms OnBytes.Road.K4.Plan.good_addP
#print axioms OnBytes.Road.K4.Plan.goodN_getD
#print axioms OnBytes.Road.K4.Plan.addTreesF_mS
#print axioms OnBytes.Road.K4.Plan.addTrees_mS
