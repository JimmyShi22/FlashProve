-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean.
The test on the planes' matrix at a group of layers (Fo.planeMatB,
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerReads.lean) says yes at every record that Verify.publicOf
returns.

The twin of OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPub.lean. The test asks that the lookup's shape is
made of the calls (Fo.madeB), that the matrix b has as many rows as a block of its tables, and that
it has at least as many columns as the planes have. The first is Fo.Pub.public_made_G
(OnBytes/Tie/Pv/Lookup/Ends/FoMadePublic.lean) with Fo.test_of_made
(OnBytes/Tie/Pv/Lookup/Ends/FoMadeTestB.lean). The other two hold by how the plan is made:
Layer.tailsOf lays the matrix b with 2 ^ lmb rows and y.kbm columns; Layer.bordersOf keeps every
matrix's rows and columns; Layer.layoutLook sets y.kbm to what Forest.planeCols returns.

States:
  planG_mats: the list of matrices in a group's plan is the first part of what Layer.bordersOf
    returns.
  bordersOf_keeps: that list has, place by place, the rows and columns of the list that went in.
  tailsOf_b: in the list that Layer.tailsOf lays for a group below NGr, the matrix number iB has 2 ^
    lmb rows and y.kbm columns.
  layoutLook_kbm, layout_kbm, public_kbm: y.kbm is the number of columns of the planes.
  pubOf_tails, public_tails: the record's lists of matrices are Layer.tailsOf of its layout.
  plansFrom_len, public_G_lt: a group that has a plan is below NGr.
  public_planeMatB: the test says yes at every group's plan of a record that Verify.publicOf
    returns.
Under: in each the one equation of the routine that returns (in public_G_lt and public_planeMatB
also that the plan is a member of X.G; in tailsOf_b that the group is below NGr). Limits: the groups
of layers alone. One direction: from a routine that returns.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLayerReads
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanH
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeTestB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PlaneMatG
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo

/-! ### the plan keeps the list -/

/-- The list of matrices in a group's plan. -/
theorem planG_mats (P : Layer.Pub) (g : ℕ) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    ∃ r, Layer.bordersOf P.y (P.tails.getD g {}).mats = .ok r ∧ hp.tl.mats = r.1 := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, hb, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k1 : tl1.mats = mats :=
    (addTrees_keeps _ _ _ _ _ _ _ _ hA).1.trans (shape_mats _ _ _ _ _ _ _ hS).1
  have k2 : (tl1.ownerIs g).mats = mats := k1
  refine ⟨(mats, txOf, ft), hb, ?_⟩
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k2
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact (borderMeans_mats hB).1.trans k2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-! ### the borders keep rows and columns -/

/-- Two lists of matrices have the same rows and columns, place by place. -/
def SameMK (a b : List TMat) : Prop := a.map (fun M => (M.m, M.k)) = b.map fun M => (M.m, M.k)

theorem borders_fold (y : Layer.Lay) : ∀ (l : List (TMat × ℕ))
    (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ),
    ((l.foldl (fun (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ) x =>
      let (M, mu) := x
      let (ms, tx, ft, nTX) := s
      if M.kind == 0 && (mu == (Layer.matIx y).iXO || (y.h.p4 && mu == (Layer.matIx y).iQA)) then
        (ms.push M, tx.push (some nTX), ft, nTX + 1)
      else if M.kind == 1 then
        (ms.push { M with foreign := some ft.size, ttOff := 0 }, tx.push none,
         ft.push { name := "PXf" ++ toString ft.size, K := M.k, a := 2, m := M.m, wp := M.wp }, nTX)
      else (ms.push M, tx.push none, ft, nTX)) s).1.toList.map fun M => (M.m, M.k)) =
      (s.1.toList.map fun M => (M.m, M.k)) ++ l.map fun x => (x.1.m, x.1.k)
  | [], s => by simp
  | (M, mu) :: l, (ms, tx, ft, nTX) => by
    rw [List.foldl_cons, borders_fold y l]
    dsimp only
    split
    · simp
    · split <;> simp

theorem zipIdx_map_fst {α β : Type} (f : α → β) : ∀ (l : List α) (n : ℕ),
    (l.zipIdx n).map (fun x => f x.1) = l.map f
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_map_fst f l (n + 1)]

theorem bordersOf_keeps {y : Layer.Lay} {mats : Array TMat}
    {r : Array TMat × Array (Option ℕ) × Array T2Foreign}
    (e : Layer.bordersOf y mats = .ok r) : SameMK r.1.toList mats.toList := by
  unfold Layer.bordersOf at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj e
  unfold SameMK
  dsimp only
  rw [borders_fold y, zipIdx_map_fst (fun M : TMat => (M.m, M.k))]
  simp

theorem sameMK_getD {a b : Array TMat} (h : SameMK a.toList b.toList) (i : ℕ) :
    (a.getD i {}).m = (b.getD i {}).m ∧ (a.getD i {}).k = (b.getD i {}).k := by
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, Array.getElem?_toList] at e
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases ha : a[i]? <;> cases hb : b[i]? <;> rw [ha, hb] at e <;> simp at e
  · exact ⟨rfl, rfl⟩
  · exact e

/-! ### the matrix b in the list -/

theorem nth_second {α : Type} (A B : List α) (a b c d e : α) :
    (A ++ B ++ [a, b, c, d, e])[A.length + B.length + 1]? = some b := by
  rw [List.getElem?_append_right (by simp)]
  have h2 : A.length + B.length + 1 - (A ++ B).length = 1 := by
    rw [List.length_append]
    omega
  rw [h2]
  rfl

theorem zipIdx_map_at {α β : Type} (F : α × ℕ → β) (l : List α) (i : ℕ) :
    (l.zipIdx.map F)[i]? = (l[i]?).map fun a => F (a, i) := by
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases l[i]? <;> simp

/-- The matrix b in the list that Layer.tailsOf lays for a group. -/
theorem tailsOf_b (y : Layer.Lay) (g : ℕ) (hg : g < y.NGr) :
    ((((Layer.tailsOf y).getD g {}).mats).getD (Layer.matIx y).iB {}).m = 2 ^ y.h.lmb ∧
      ((((Layer.tailsOf y).getD g {}).mats).getD (Layer.matIx y).iB {}).k = y.kbm := by
  unfold Layer.tailsOf
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hg, if_true,
    Option.map_some, Option.getD_some, List.getElem?_toArray, zipIdx_map_at]
  have e := nth_second
    (List.map (fun p : ℕ => ("af" ++ toString p, y.mrow[0]?.getD 0, y.kcol[0]?.getD 0))
      (List.range (y.parts[0]?.getD 0)))
    (List.map (fun p : ℕ => ("ad" ++ toString p, y.mrow[1]?.getD 0, y.kcol[1]?.getD 0))
      (List.range (y.parts[1]?.getD 0)))
    ("ar", y.mrow[2]?.getD 0, y.kcol[2]?.getD 0) ("b", 2 ^ y.h.lmb, y.kbm)
    ("qa", y.mrow[3]?.getD 0, y.kcol[3]?.getD 0) ("xbO", y.mxb, y.kxb) ("xbI", y.mxb, y.kxb)
  have hi : (List.map (fun p : ℕ => ("af" ++ toString p, y.mrow[0]?.getD 0, y.kcol[0]?.getD 0))
        (List.range (y.parts[0]?.getD 0))).length +
      (List.map (fun p : ℕ => ("ad" ++ toString p, y.mrow[1]?.getD 0, y.kcol[1]?.getD 0))
        (List.range (y.parts[1]?.getD 0))).length + 1 = (Layer.matIx y).iB := by
    simp [Layer.matIx, Array.getD_eq_getD_getElem?]
  rw [hi] at e
  rw [e]
  simp only [Option.map_some, Option.getD_some]
  constructor <;> (split <;> rfl)

/-! ### the number of columns -/

theorem layoutLook_kbm {y y' : Layer.Lay} (e : Layer.layoutLook y = .ok y') :
    y'.kbm = planeCols y'.fo y'.h.lmb := by
  unfold Layer.layoutLook at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨fo, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨kbm, hk, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨pub, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  unfold Forest.planeCols at hk
  split at hk
  · cases hk
  · exact (Except.ok.inj hk).symm

theorem layout_kbm {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : y.kbm = planeCols y.fo y.h.lmb := by
  unfold Layer.layout at e
  obtain ⟨y0, _, e⟩ := bindE_ok e
  exact layoutLook_kbm e

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_kbm (h : Verify.publicOf pol KL layout = .ok X) :
    X.layers.y.kbm = planeCols X.layers.y.fo X.layers.y.h.lmb := by
  have e := (Pub.publicOf_cut pol KL layout X h).1
  unfold Verify.polLayout at e
  obtain ⟨P, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨y, hy, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, e2⟩ := Prod.mk.inj (Except.ok.inj e)
  rw [← e2]
  exact layout_kbm hy

/-! ### the public end -/

/-- Layer.Pub.of lays the lists of matrices of its layout. -/
theorem pubOf_tails {y : Layer.Lay} {sc : Layer.Scales} {rope : Array ℕ} {wsLay : WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.tails = Layer.tailsOf L.y := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

theorem public_tails (h : Verify.publicOf pol KL layout = .ok X) :
    X.layers.tails = Layer.tailsOf X.layers.y := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := Pub.ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  exact pubOf_tails k4

theorem plansFrom_len (P : Layer.Pub) : ∀ (n g : ℕ) (O : Option Layer.HPlan2)
    (l : List Layer.HPlan2), Layer.plansFrom P n g O = .ok l → l.length = n
  | 0, _, _, l, h => by
    obtain rfl := Except.ok.inj h
    rfl
  | n + 1, g, O, l, h => by
    unfold Layer.plansFrom at h
    obtain ⟨p, _, h⟩ := bindE_ok h
    obtain ⟨l', h1, h⟩ := bindE_ok h
    obtain rfl := Except.ok.inj h
    rw [List.length_cons, plansFrom_len P n (g + 1) (some p) l' h1]

/-- A group that has a plan is below the number of groups. -/
theorem public_G_lt (h : Verify.publicOf pol KL layout = .ok X) {g : ℕ} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) : g < X.layers.y.NGr := by
  have e := (Pub.publicOf_cut pol KL layout X h).2.2.1
  unfold Layer.plansG at e
  obtain ⟨l, h1, e⟩ := bindE_ok e
  have hl := plansFrom_len X.layers _ _ _ l h1
  have hs : X.G.size = X.layers.y.NGr := by
    rw [← Except.ok.inj e]
    simpa using hl
  rw [← hs]
  exact (Array.getElem?_eq_some_iff.mp hg).1

/-- **The test says yes at every group's plan of a record that publicOf returns.** -/
theorem public_planeMatB (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) :
    planeMatB X.layers.y hp.tl.mats = true := by
  obtain ⟨r, hb, hm⟩ := planG_mats X.layers g _ hp (Pub.public_G h g hp hg)
  obtain ⟨k1, k2⟩ := sameMK_getD (bordersOf_keeps hb) (Layer.matIx X.layers.y).iB
  rw [public_tails h] at k1 k2
  obtain ⟨b1, b2⟩ := tailsOf_b X.layers.y g (public_G_lt h hg)
  simp only [planeMatB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨test_of_made (Pub.public_made_G h), ?_⟩, ?_⟩
  · rw [hm, k1, b1]
    exact Nat.div_self (Nat.pos_of_ne_zero (by positivity))
  · rw [hm, k2, b2, public_kbm h]

end

end Fo.PlaneMatG
