-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PlanPort.lean: two public facts on the record of a smallness test in a layers'
plan, wherever publicOf returns.

  shapeF_gt: what HTailF2.shapeF (OnBytes/Model/Tail.lean) returns lists one array for each matrix:
    gtTree.size = NM. In the library this stands inside the proof of shapeF_ix
    (OnBytes/Tie/Pv/Lookup/Ends/FoShapeF.lean:191) under no name; the walk through the routine's
    third loop is that proof's, with the size alone as what is kept.
  planG_gt, public_G_gt: so hp.tl.gtTree.size = hp.tl.NM at every plan hp that Layer.planG returns,
    and at every member of X.G: the field gt of the library's PortOK
    (OnBytes/Tie/Pv/Tail/EndsAtPort.lean:45).
  addTreesF_u3: behind HTailF2.addTreesF the array of the vector U3 has nU[2] columns: its first
    loop lays the array with that number, and every later step lengthens the list of arrays and
    leaves the earlier ones (the library's Ext, OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean:69).
  planG_K3, public_G_K3: so the number K3 that the sub-proof's own hearing takes off the plan
    (Layer.hearOwn, OnBytes/Model/Layer.lean:551: the number of columns K of the array
    hp.Fp.trees[t], t the plan's number of U3) IS hp.nU[2].
Not claimed: that a run's environment has this K3: that is hearOwn's own line.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHasU
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeF
import Johnson.Road.FormsKeysForest

set_option autoImplicit false

namespace Meaning.Plan

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open Fo.BatRows (bindE_ok)

/-- shapeF lists one array for each matrix. -/
theorem shapeF_gt {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') : tl'.gtTree.size = tl'.NM := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r1, h1, h⟩ := ok_of_bind h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r2, h2, h⟩ := ok_of_bind h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := ok_of_bind h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨-, e2, e3, -⟩ := Fo.piecesF_keys h
  rw [e2, e3]
  clear h e2 e3 h2 h1
  have K3 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) => s.1.size = pre.length)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      have push : ∀ y, (gt.push y).size = (pre ++ [a]).length := by
        intro y
        have hI' : gt.size = pre.length := hI
        simp [hI']
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      split at hs
      · split at hs
        · exact ⟨_, (Except.ok.inj hs).symm, push _⟩
        · exact ⟨_, (Except.ok.inj hs).symm, push _⟩
      · split at hs
        · split at hs
          · simp only [pure_bind] at hs
            split at hs
            · split at hs
              · cases hs
              · split at hs
                · cases hs
                · exact ⟨_, (Except.ok.inj hs).symm, push _⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl rfl h3
  show gtTree.size = m.size
  rw [K3, List.length_range]

/-- The fact passes along records with the same ten fields. -/
theorem gt_same {a b : HTailF2} (h : a.gtTree.size = a.NM) (k : SameP a b) :
    b.gtTree.size = b.NM := by
  rw [k.same.gtTree, k.same.NM]
  exact h

theorem gt_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork}
    {T T' : Tail2} {nU aTX : Array Nat} {hb hbLine : Nat}
    (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {tlc : HTailF2}
    (hr : SameP tl' tlc) : tlc.gtTree.size = tlc.NM :=
  gt_same (shapeF_gt hs) ((addTreesF_sameP ha).trans hr)

theorem planG_gt (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.tl.gtTree.size = hp.tl.NM := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact gt_made hS hA (ownerIs_sameP tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact gt_made hS hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- AT EVERY LAYERS' PLAN OF WHAT publicOf RETURNS. -/
theorem public_G_gt {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : hp.tl.gtTree.size = hp.tl.NM :=
  planG_gt X.layers g _ hp (public_G h g hp hg)

/-! ## The array of the reads has as many columns as the plan's nU says -/

theorem t2AddN_K {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    (F'.trees.getD got {}).K = K := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e1 e2
    show ((F.trees.push _).getD F.trees.size {}).K = K
    rw [getD_push_last]

/-- A loop of t2AddP lengthens the list of arrays. -/
theorem Ext.keep {F G : Fork} (h : Ext F G) {t K : Nat}
    (k : t < F.trees.size ∧ (F.trees.getD t {}).K = K) :
    t < G.trees.size ∧ (G.trees.getD t {}).K = K :=
  ⟨Nat.lt_of_lt_of_le k.1 h.1, by rw [h.2 t k.1]; exact k.2⟩

/-- Behind addTreesF the array U3 has nU[2] columns. -/
theorem addTreesF_u3 {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {t : Nat}
    (hu : tl.ix.U.getD 2 none = some t) :
    t < G.trees.size ∧ (G.trees.getD t {}).K = nU.getD 2 0 := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_of_jp h
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
  obtain ⟨-, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, -⟩ := Prod.mk.inj e2
  subst e2
  have K1 := forIn_keeps _ (List.range 3)
    (fun pre (s : MProd Fork Tail2) => 2 ∈ pre →
      t < s.1.trees.size ∧ (s.1.trees.getD t {}).K = nU.getD 2 0)
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · rename_i want hw
        obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨hgw, hs⟩ := ok_of_jp hs
        refine ⟨_, (Except.ok.inj hs).symm, fun hm => ?_⟩
        obtain ⟨g1, g2, g3, -, -⟩ := t2AddN_ok hP
        rcases List.mem_append.1 hm with hm | hm
        · exact Ext.keep g2 (hI hm)
        · have ea : a = 2 := (List.mem_singleton.1 hm).symm
          subst ea
          have ew : want = t := Option.some.inj (hw.symm.trans hu)
          have eg : got = t := by
            have : got = want := by simpa using hgw
            rw [this, ew]
          subst eg
          exact ⟨by show got < F'.trees.size; omega, t2AddN_K hP⟩
      · rename_i hw
        refine ⟨_, (Except.ok.inj hs).symm, fun hm => ?_⟩
        rcases List.mem_append.1 hm with hm | hm
        · exact hI hm
        · have ea : a = 2 := (List.mem_singleton.1 hm).symm
          subst ea
          exact absurd hu (hw t))
    (List.range 3) [] _ _ rfl (fun hm => by cases hm) h1
  have k1 := K1 (by decide)
  have addP : ∀ (Fa : Fork) (l : List Nat) (body : Nat → MProd Fork Tail2 →
      Except String (ForInStep (MProd Fork Tail2))) (s r : MProd Fork Tail2),
      (∀ a s s', Ext Fa s.1 → body a s = .ok s' → ∃ u, s' = .yield u ∧ Ext Fa u.1) →
      Ext Fa s.1 → forIn l s body = .ok r → Ext Fa r.1 := by
    intro Fa l body s r hstep hs hr
    exact forIn_keeps body l (fun _ s => Ext Fa s.1)
      (fun _ a _ _ s s' hI hb => hstep a s s' hI hb) l [] s r rfl hs hr
  have E2 : Ext F1 F2 := addP F1 _ _ _ _ (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩) (Ext.refl F1) h2
  have E3 : Ext F2 F3 := addP F2 _ _ _ _ (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩) (Ext.refl F2) h3
  have E4 : Ext FB F4 := addP FB _ _ _ _ (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩) (Ext.refl FB) h4
  exact Ext.keep ((((E2.trans E3).trans (t2AddN_ok hZ).2.1).trans (t2AddN_ok hB).2.1).trans E4) k1

/-- trimL keeps each array's number of columns. -/
theorem trimL_K (F : Fork) (t : Nat) :
    ((F.trimL.trees[t]?).map (·.K)).getD 0 = ((F.trees[t]?).map (·.K)).getD 0 := by
  unfold Fork.trimL
  simp only [Array.getElem?_map, Option.map_map]
  rfl

theorem k3_made {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    {tlc : HTailF2} (hr : SameP tl' tlc) {t : Nat} (hu : tlc.ix.U.getD 2 none = some t) :
    ((G.trimL.trees[t]?).map (·.K)).getD 0 = nU.getD 2 0 := by
  rw [((addTreesF_sameP ha).trans hr).same.ix] at hu
  obtain ⟨k1, k2⟩ := addTreesF_u3 ha hu
  rw [trimL_K, Array.getElem?_eq_getElem k1]
  have e : G.trees.getD t {} = G.trees[t] := by simp [Array.getD, k1]
  rw [e] at k2
  exact k2

/-- The number K3 that hearOwn takes off the plan (OnBytes/Model/Layer.lean:551) is the plan's
nU[2]. -/
theorem planG_K3 (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) {t : Nat} (hu : hp.tl.ix.U.getD 2 none = some t) :
    ((hp.Fp.trees[t]?).map (·.K)).getD 0 = hp.nU.getD 2 0 := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k3_made hA (ownerIs_sameP tl1 g) hu
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only at hu ⊢
      rw [hy] at hu
      exact k3_made hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) hu
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem public_G_K3 {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) {t : Nat} (hu : hp.tl.ix.U.getD 2 none = some t) :
    ((hp.Fp.trees[t]?).map (·.K)).getD 0 = hp.nU.getD 2 0 :=
  planG_K3 X.layers g _ hp (public_G h g hp hg) hu

#print axioms shapeF_gt
#print axioms public_G_gt
#print axioms addTreesF_u3
#print axioms public_G_K3

end Meaning.Plan
