-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FunsRel.lean: THE LAYERS' OWN ROUNDS (K4): THE LIST OF TABLES THAT
THE HEARING LAYS HAS ONE SHAPE AT TWO RECORDS OF ONE SHAPE. Congruences: each statement compares two
calls. Nothing is evaluated.

  PtsAlike, last_rel, **pointsOf_rel**   the points at which the tables are read: the same names,
                  points of one size each.
  find_rel, phiOf_rel, FunsAlike, **funsOf_rel**   the tables with their weights: one shape (funSh,
                  Johnson/Desc/First/Shape/Tail.lean: matrix, rows to an entry, the NUMBER of
                  weights, vector, first entry).

Limits. NO FUNCTION IS SHOWN TO RETURN ANYWHERE. pointsOf_rel stands at "some hd2" on both sides
alone: the case without a second level is not treated. Nothing on what a weight is worth. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelHear
import Johnson.Desc.Reads.FoldAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same mapM_opt_rel)
open OnBytes.Desc.First.K4.RtPub (optRel_ite optRel_pure)
open OnBytes.Road (eqTab_size)
open VerifiableInference.Reads (blockRows_size)
open VerifiableInference.Desc.First.Shape

/-! ## The points at which the tables are read -/

/-- Two lists of named points: the same names, points of one size each. -/
def PtsAlike (l l' : List (String × Array E)) : Prop :=
  l.map (fun p => (p.1, p.2.size)) = l'.map fun p => (p.1, p.2.size)

theorem last_rel {z z' : Array E} (h : z.size = z'.size) (k : Nat) :
    OptRel SameSize (lastOf z k).toOption (lastOf z' k).toOption := by
  cases h1 : (lastOf z k).toOption with
  | none =>
    cases h2 : (lastOf z' k).toOption with
    | none => trivial
    | some b =>
      exfalso
      have hk : k ≤ z.size := by
        by_contra hc
        unfold lastOf cutLast at h2
        rw [if_pos (by omega)] at h2
        cases h2
      obtain ⟨a, ha, -⟩ := lastOf_some z k hk
      rw [ha] at h1
      cases h1
  | some a =>
    cases h2 : (lastOf z' k).toOption with
    | none =>
      exfalso
      have hk : k ≤ z'.size := by
        by_contra hc
        unfold lastOf cutLast at h1
        rw [if_pos (by omega)] at h1
        cases h1
      obtain ⟨b, hb, -⟩ := lastOf_some z' k hk
      rw [hb] at h2
      cases h2
    | some b =>
      show a.size = b.size
      rw [lastOf_size h1, lastOf_size h2]

theorem pointsOf_rel (y : Lay) {H H' : Heard} (h : NormsAlike H H') {hd hd' hd2 hd2' : Level}
    (h1 : LevelAlike hd hd') (h2 : LevelAlike hd2 hd2') :
    OptRel PtsAlike (pointsOf y H hd (some hd2)) (pointsOf y H' hd' (some hd2')) := by
  unfold pointsOf
  dsimp only
  have hfo : heardAll H.fo = heardAll H'.fo := congrArg NormsSh.fo h
  have hw : LevelAlike H.wpl H'.wpl := congrArg NormsSh.wpl h
  refine optRel_bind (last_rel (congrArg HeardAll.zx hfo) _) fun Z Z' hZ => ?_
  refine optRel_bind (S := PtsAlike) ?_ fun routed routed' hr => ?_
  · have e := last_rel h2.r y.h.la
    cases a1 : (lastOf hd2.r y.h.la).toOption <;> cases a2 : (lastOf hd2'.r y.h.la).toOption <;>
      rw [a1, a2] at e
    · trivial
    · exact e.elim
    · exact e.elim
    · show [("Z_b", _)] = [("Z_b", _)]
      rw [show _ = _ from e]
  refine optRel_bind (last_rel hw.r _) fun zv zv' hzv => ?_
  refine optRel_bind (last_rel h1.r _) fun za za' hza => ?_
  refine optRel_pure ?_
  have b1 : H.ztF.size = H'.ztF.size := congrArg NormsSh.ztF h
  have b2 : H.PV.size = H'.PV.size := congrArg NormsSh.PV h
  have b3 : H.ZE.size = H'.ZE.size := congrArg NormsSh.ZE h
  have b4 : H.tV.r.size = H'.tV.r.size :=
    congrArg TscSh.r (congrArg NormsSh.tV h : tscSh H.tV = tscSh H'.tV)
  have z1 : Z.size = Z'.size := hZ
  have z2 : zv.size = zv'.size := hzv
  have z3 : za.size = za'.size := hza
  unfold PtsAlike at hr ⊢
  have e := h.tT
  cases a1 : H.tT <;> cases a2 : H'.tT <;> rw [a1, a2] at e
  · simp only [List.map_append, List.map_cons, List.map_nil, hr, z1, z2, z3, b1, b2, b3, b4]
  · exact e.elim
  · exact e.elim
  · rename_i t t'
    have c : t.r.size = t'.r.size := congrArg TscSh.r e
    simp only [List.map_append, List.map_cons, List.map_nil, hr, z1, z2, z3, b1, b2, b3, b4, c,
      longPoint, Array.size_append, Array.size_extract]

/-! ## The tables with their weights -/

theorem find_rel (name : String) : ∀ {l l' : List (String × Array E)}, PtsAlike l l' →
    OptRel (fun p p' : String × Array E => p.2.size = p'.2.size)
      (l.find? fun p => p.1 == name) (l'.find? fun p => p.1 == name)
  | [], [], _ => trivial
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | p :: l, p' :: l', h => by
    have h' : (p.1, p.2.size) :: l.map (fun p => (p.1, p.2.size)) =
        (p'.1, p'.2.size) :: l'.map fun p => (p.1, p.2.size) := h
    obtain ⟨e1, e2⟩ := List.cons.inj h'
    obtain ⟨n1, n2⟩ := Prod.mk.inj e1
    rw [List.find?_cons, List.find?_cons, n1]
    cases p'.1 == name
    · exact find_rel name e2
    · exact n2

theorem phiOf_rel (y : Lay) {fo fo' : Forest.Heard} (hfo : heardAll fo = heardAll fo')
    {pt pt' : List (String × Array E)} (hp : PtsAlike pt pt') (a : TableAsk) :
    OptRel SameSize (phiOf y fo pt a) (phiOf y fo' pt' a) := by
  have hs : fo.shape = fo'.shape := congrArg HeardAll.shape hfo
  have hB : ∀ e, OptRel SameSize (Forest.phiB fo y.h.lmb e) (Forest.phiB fo' y.h.lmb e) := by
    intro e
    unfold Forest.phiB
    dsimp only
    rw [hs]
    refine optRel_ite ?_ trivial
    have hz : (fo.zb e).size = (fo'.zb e).size := by
      unfold Forest.Heard.zb
      split
      · exact congrArg HeardAll.zb0 hfo
      · exact congrArg HeardAll.zb1 hfo
    show (eqTab _).size = (eqTab _).size
    rw [eqTab_size, eqTab_size, Array.size_append, Array.size_append, Array.size_extract,
      Array.size_extract, Array.size_extract, Array.size_extract, hz]
  unfold phiOf
  refine optRel_ite (hB 0) (optRel_ite (hB 1) (optRel_ite (rfl : SameSize _ _) ?_))
  have e := find_rel a.point hp
  cases a1 : pt.find? (fun p => p.1 == a.point) <;>
    cases a2 : pt'.find? (fun p => p.1 == a.point) <;> rw [a1, a2] at e
  · trivial
  · exact e.elim
  · exact e.elim
  · rename_i p p'
    have e' : p.2.size = p'.2.size := e
    show OptRel SameSize (if _ then none else some _) (if _ then none else some _)
    rw [e']
    refine optRel_ite trivial ?_
    show (if a.lng = true then longPhi p.2 y.ls y.h.lt else eqTab p.2).size =
      (if a.lng = true then longPhi p'.2 y.ls y.h.lt else eqTab p'.2).size
    split
    · unfold longPhi
      rw [blockRows_size, blockRows_size, eqTab_size, eqTab_size, eqTab_size, eqTab_size,
        Array.size_extract, Array.size_extract, Array.size_extract, Array.size_extract, e']
    · rw [eqTab_size, eqTab_size, e']

/-- Two lists of tables of one shape. -/
def FunsAlike (f f' : Array HFun) : Prop := f.toList.map funSh = f'.toList.map funSh

theorem funsOf_rel (y : Lay) {fo fo' : Forest.Heard} (hfo : heardAll fo = heardAll fo')
    {pt pt' : List (String × Array E)} (hp : PtsAlike pt pt')
    (laid : List (TableAsk × List (Nat × Nat))) :
    OptRel FunsAlike (funsOf y fo pt laid) (funsOf y fo' pt' laid) := by
  unfold funsOf
  refine optRel_bind (mapM_opt_rel (R := fun l l' : List HFun => l.map funSh = l'.map funSh)
    (f := fun x : TableAsk × List (Nat × Nat) => do
      let phi ← phiOf y fo pt x.1
      pure (x.2.map fun m =>
        ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun)))
    (f' := fun x : TableAsk × List (Nat × Nat) => do
      let phi ← phiOf y fo' pt' x.1
      pure (x.2.map fun m =>
        ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun)))
    (fun x => optRel_bind (phiOf_rel y hfo hp x.1) fun phi phi' hphi => optRel_pure (by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun m _ => ?_
      show FunSh.mk m.1 x.1.L phi.size 2 m.2 = FunSh.mk m.1 x.1.L phi'.size 2 m.2
      rw [show phi.size = phi'.size from hphi])) laid) fun l l' hl => optRel_pure ?_
  show l.flatten.toArray.toList.map funSh = l'.flatten.toArray.toList.map funSh
  show l.flatten.map funSh = l'.flatten.map funSh
  induction hl with
  | nil => rfl
  | cons h0 _ ih => rw [List.flatten_cons, List.flatten_cons, List.map_append, List.map_append, h0,
                  ih]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.last_rel
#print axioms OnBytes.Desc.First.K4.Rt.pointsOf_rel
#print axioms OnBytes.Desc.First.K4.Rt.find_rel
#print axioms OnBytes.Desc.First.K4.Rt.phiOf_rel
#print axioms OnBytes.Desc.First.K4.Rt.funsOf_rel
#print axioms OnBytes.Desc.First.K4.Rt.PtsAlike
#print axioms OnBytes.Desc.First.K4.Rt.FunsAlike
