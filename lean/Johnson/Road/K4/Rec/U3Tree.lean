-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/U3Tree.lean: THE ARRAY OF THE READS (U3) IN A LAYERS' PLAN, BY THE MAKE OF
planG: it is array number 0 of the plan's list; it has one row, hp.nU[2] columns and one virtual
row, which begins at column 0. WHY: the named test readsP of K4's row (readsArrayP,
Johnson/Road/K4/Rec/ReadsArray.lean) reads just these numbers off the plan. Two definitions, seven
statements with their proofs.

  `u3Tree K`: the array as addTreesF lays it. `trimT`: what Fork.trimL does to an array.
  `shapeF_U`: a smallness test's structure that is shaped with the third vector alone has
    ix.U = #[none, none, some 0, none]. Premise: shapeF returns.
  `t2AddN_tree`: the array that t2AddN adds, whole.
  `ext_keep`: a longer list of arrays keeps an earlier array whole.
  `addTreesF_u3Tree`: behind addTreesF array ix.U[2] is u3Tree nU[2]. The walk is that of
    Meaning.Plan.addTreesF_u3 (Johnson/Goal/Meaning/PlanPort.lean), with the whole array in the
    place of its number of columns.
  `u3_made`, **`planG_u3`**: where planG returns hp: hp.tl.ix.U is that list and
    hp.Fp.trees[0]? = some (trimT (u3Tree (hp.nU.getD 2 0))).
  `look_u3`: so the look of array 0 (looksOf, Johnson/Desc/First/SentTerms.lean) is
    (1, K, [(0, K)]).
Limits. The plan's side alone: nothing on what the segments declare or on the layout. K04_law, the
law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Goal.Meaning.PlanPort
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open Fo.BatRows (bindE_ok)
open VerifiableInference.Desc.First.FillSent (looksOf)

/-- The array of the reads, as addTreesF lays it. -/
def u3Tree (K : Nat) : HTree :=
  { name := "U" ++ toString (2 + 1), kind := .table, R := 1, K := K, owner := !false,
    rows := Array.replicate 1 ({} : HRow) }

/-- What Fork.trimL does to an array. -/
def trimT (X : HTree) : HTree := { X with rows := X.rows.map fun r => { r with L := #[] } }

/-- Shaped with the third vector alone: the list of the vectors' arrays. -/
theorem shapeF_U {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (h : tl.shapeF m txOf f #[false, false, true, false] tau = .ok tl') :
    tl'.ix.U = #[none, none, some 0, none] := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r1, h1, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r2, h2, h⟩ := ok_of_bind h
  obtain rfl := Except.ok.inj h2
  obtain ⟨r3, h3, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨e1, -⟩ := Fo.piecesF_keys h
  rw [e1]
  rfl

/-- The array that t2AddN adds, whole. -/
theorem t2AddN_tree {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    F'.trees.getD got {} =
      { name := name, kind := .table, R := R, K := K, owner := !foreign,
        rows := Array.replicate nv ({} : HRow) } := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e1 e2
    show (F.trees.push _).getD F.trees.size {} = _
    rw [getD_push_last]

/-- A longer list of arrays keeps an earlier array whole. -/
theorem ext_keep {F G : Fork} (h : Ext F G) {t : Nat} {X : HTree}
    (k : t < F.trees.size ∧ F.trees.getD t {} = X) :
    t < G.trees.size ∧ G.trees.getD t {} = X :=
  ⟨Nat.lt_of_lt_of_le k.1 h.1, by rw [h.2 t k.1]; exact k.2⟩

/-- **Behind addTreesF the array U3 is u3Tree nU[2].** -/
theorem addTreesF_u3Tree {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {t : Nat}
    (hu : tl.ix.U.getD 2 none = some t) :
    t < G.trees.size ∧ G.trees.getD t {} = u3Tree (nU.getD 2 0) := by
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
      t < s.1.trees.size ∧ s.1.trees.getD t {} = u3Tree (nU.getD 2 0))
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
        · exact ext_keep g2 (hI hm)
        · have ea : a = 2 := (List.mem_singleton.1 hm).symm
          subst ea
          have ew : want = t := Option.some.inj (hw.symm.trans hu)
          have eg : got = t := by
            have : got = want := by simpa using hgw
            rw [this, ew]
          subst eg
          exact ⟨by show got < F'.trees.size; omega, t2AddN_tree hP⟩
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
  exact ext_keep ((((E2.trans E3).trans (t2AddN_ok hZ).2.1).trans (t2AddN_ok hB).2.1).trans E4) k1

/-- The two facts, at a structure that keeps what addTreesF returns. -/
theorem u3_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (hs : tl₀.shapeF m txOf f #[false, false, true, false] tau = .ok tl) {F G : Fork}
    {T T' : Tail2} {nU aTX : Array Nat} {hb hbLine : Nat}
    (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {tlc : HTailF2}
    (hr : SameP tl' tlc) :
    tlc.ix.U = #[none, none, some 0, none] ∧
      G.trimL.trees[0]? = some (trimT (u3Tree (nU.getD 2 0))) := by
  have eU := shapeF_U hs
  have ei : tlc.ix = tl.ix := ((addTreesF_sameP ha).trans hr).same.ix
  have hu : tl.ix.U.getD 2 none = some 0 := by
    rw [eU]
    rfl
  obtain ⟨k1, k2⟩ := addTreesF_u3Tree ha hu
  refine ⟨by rw [ei, eU], ?_⟩
  have e : G.trees.getD 0 {} = G.trees[0] := by simp [Array.getD, k1]
  unfold Fork.trimL
  show (G.trees.map trimT)[0]? = _
  rw [Array.getElem?_map, Array.getElem?_eq_getElem k1, ← e, k2]
  rfl

/-- **The array of the reads in a layers' plan.** -/
theorem planG_u3 (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    hp.tl.ix.U = #[none, none, some 0, none] ∧
      hp.Fp.trees[0]? = some (trimT (u3Tree (hp.nU.getD 2 0))) := by
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
    exact u3_made hS hA (ownerIs_sameP tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact u3_made hS hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- The look of array 0. -/
theorem look_u3 {Fp : Fork} {K : Nat} (h : Fp.trees[0]? = some (trimT (u3Tree K))) :
    (looksOf Fp)[0]? = some (1, K, [(0, K)]) := by
  unfold looksOf
  rw [List.getElem?_map, Array.getElem?_toList, h]
  simp [trimT, u3Tree]

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.shapeF_U
#print axioms OnBytes.Road.K4.Rec.addTreesF_u3Tree
#print axioms OnBytes.Road.K4.Rec.planG_u3
#print axioms OnBytes.Road.K4.Rec.look_u3
