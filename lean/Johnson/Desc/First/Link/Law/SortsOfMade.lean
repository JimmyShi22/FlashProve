-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortsOfMade.lean: **"EVERY ARRAY OF THE LEDGER IS OF ONE OF THE FOUR
SORTS" (`sortsB`, Law/CoefsFit.lean beside this file) AT EVERY MEMBER OF THE PUBLIC PARAMETERS,
FROM THE RETURN OF `Verify.publicOf` ALONE.** Fifteen theorems.
A corollary of the two laws that "Why" below names,
carried as FoZMade.lean and FoZPublic.lean carry `Fo.ZPlan.ZMine`.
Why. `HTailF2.addTreesF` lays the arrays in one fixed order and holds each new number against the
map `ix`: so each array has one of four looks (`addTreesF_looks`, `looks_apart`, and the way back
at each named number: Johnson/Desc/Kinds/Law/AddTreesLooks.lean); and a number stands in one of
the map's three lists of symbol arrays just if it is a matrix's array (`shapeF_trees`,
Johnson/Road/K4/Names/ShapeTrees.lean).
  `piecesF_ft`, `shapeF_ft`: what `shapeF` returns holds the list f that it was handed.
  `sym_at`: the array at a number of one of the three lists is a symbol array.
  `oneRowTable_apart`: the number of a table with one virtual row is none of ZZ's, BZ's, a
  matrix's, a call's member's.
  `sorts_at`: **behind `shapeF` and `addTreesF {} {}`: `sortsB`.** `sortsB_same`: the test reads
  five fields alone. `looks_trimL`: `Fork.trimL` keeps every array's look. `sorts_made`: so at
  whatever agrees in these.
  `planG_sorts`, `seam_sorts`, `planA_sorts`, `planH2_sorts`: at the returns of the three routines
  that lay out a sub-proof's arrays: the cuts are OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean's, line
  by line.
  `public_G_sorts`, `public_A_sorts`, `public_H_sorts`: **at X's own members**: FoZPublic.lean's
  proofs, line by line.
Limits. Nothing on a structure that a later routine of a run has turned. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.CoefsFit
import Johnson.Desc.Kinds.Law.AddTreesLooks
import Johnson.Road.K4.Names.ShapeTrees
import OnBytes.Tie.Pv.Lookup.Ends.FoZTests0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp)
open _root_.Fo (SameP SameRec pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open VerifiableInference.Desc.Kinds.Head.Law.Plan
open OnBytes.Road.K4.Names (shapeF_trees shapeF_pkSize shapeF_ftSize shapeF_px)

/-- `shapeF`'s last act keeps the list of the earlier sub-proofs' arrays. -/
theorem piecesF_ft {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') : tl'.ft = tl.ft := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨f9, _, h⟩ := ok_of_bind h
  obtain ⟨pub, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  rfl

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

variable {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
  {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat} {G : Fork} {T' : Tail2}
  {nU aTX : Array Nat} {hb hbLine : Nat}

/-- What `shapeF` returns holds the list that it was handed. -/
theorem shapeF_ft (e : tl₀.shapeF m txOf f hasU tau = .ok tl) : tl.ft = f := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  exact piecesF_ft e

/-- The array at a number of one of the three lists is a symbol array. -/
theorem sym_at (hs : tl₀.shapeF m txOf f hasU tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) {t : Nat}
    (hi : ∃ i : Nat, tl.ix.PK[i]? = some t ∨ tl.ix.TX[i]? = some t ∨ tl.ix.FT[i]? = some t) :
    ∃ X, G.trees[t]? = some X ∧ X.kind = .symbols := by
  obtain ⟨i, h1 | h1 | h1⟩ := hi
  · have hl : i < tl.pkMat.size := by
      rw [← shapeF_pkSize hs]
      exact (Array.getElem?_eq_some_iff.1 h1).1
    obtain ⟨t', X, e, hX, hk⟩ := addTreesF_atPK ha i hl
    rw [h1] at e
    obtain rfl := Option.some.inj e
    exact ⟨X, hX, hk⟩
  · have hl : i < tl.pxMat.size := by
      rw [← (shapeF_px hs).2.1]
      exact (Array.getElem?_eq_some_iff.1 h1).1
    obtain ⟨t', X, e, hX, hk⟩ := addTreesF_atTX ha i hl
    rw [h1] at e
    obtain rfl := Option.some.inj e
    exact ⟨X, hX, hk⟩
  · have hl : i < tl.ft.size := by
      rw [shapeF_ft hs, ← shapeF_ftSize hs]
      exact (Array.getElem?_eq_some_iff.1 h1).1
    obtain ⟨t', X, e, hX, hk⟩ := addTreesF_atFT ha i hl
    rw [h1] at e
    obtain rfl := Option.some.inj e
    exact ⟨X, hX, hk⟩

/-- The number of a table with one virtual row is none of the other sorts'. -/
theorem oneRowTable_apart (hs : tl₀.shapeF m txOf f hasU tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) {t : Nat} {X : HTree}
    (hX : G.trees[t]? = some X) (hk : X.kind = .table) (h1 : X.rows.size = 1) :
    tl.ix.ZZ ≠ t ∧ tl.ix.BZ ≠ t ∧ (∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ t) ∧
      (∀ p ∈ tl.z1.pieces.toList, p.tree ≠ t) ∧ ∀ p ∈ tl.z2.pieces.toList, p.tree ≠ t := by
  have hZ : tl.ix.ZZ ≠ t := by
    intro e
    obtain ⟨X', hX', -, -, -, -, hr⟩ := addTreesF_atZ ha
    rw [e, hX] at hX'
    obtain rfl := Option.some.inj hX'
    omega
  have hB : tl.ix.BZ ≠ t := by
    intro e
    obtain ⟨X', hX', -, -, -, -, hr⟩ := addTreesF_atB ha
    rw [e, hX] at hX'
    obtain rfl := Option.some.inj hX'
    omega
  obtain ⟨tl0, hp⟩ := shapeF_pieces hs
  refine ⟨hZ, hB, fun mu hmu e => ?_, fun p hp1 e => ?_, fun p hp2 e => ?_⟩
  · obtain ⟨X', hX', hk'⟩ := sym_at hs ha ((shapeF_trees hs t).2 ⟨mu, hmu, e⟩)
    rw [hX] at hX'
    obtain rfl := Option.some.inj hX'
    rw [hk] at hk'
    cases hk'
  · exact hZ ((_root_.Fo.PiecesF.piecesF_pieceOK tl0 tl hp 0 (by decide) p hp1).tree.symm.trans e)
  · exact hZ ((_root_.Fo.PiecesF.piecesF_pieceOK tl0 tl hp 1 (by decide) p hp2).tree.symm.trans e)

/-- **Behind the two routines.** -/
theorem sorts_at (hs : tl₀.shapeF m txOf f hasU tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    sortsB (G.trees.toList.map look) tl = true := by
  unfold sortsB
  rw [List.all_eq_true]
  intro t ht
  have ht' : t < G.trees.size := by
    have k := List.mem_range.1 ht
    rwa [List.length_map, Array.length_toList] at k
  have hX : G.trees[t]? = some G.trees[t] := Array.getElem?_eq_getElem ht'
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range]
  rcases addTreesF_looks ha t _ hX with hU | hM | hZ | hB
  · right
    obtain ⟨n, hn, hUn, hk, hR, -, hr⟩ := hU
    obtain ⟨a1, a2, a3, a4, a5⟩ := oneRowTable_apart hs ha hX hk hr
    have e : (G.trees.toList.map look)[t]? = some (look G.trees[t]) := by
      rw [List.getElem?_map, Array.getElem?_toList, hX]
      rfl
    have h1 : oneRowLook (G.trees.toList.map look) t = true := by
      unfold oneRowLook
      rw [e]
      show (G.trees[t].kind == HKind.table && G.trees[t].R == 1 &&
        G.trees[t].rows.size == 1) = true
      rw [hk, hR, hr]
      rfl
    unfold tableAtB
    simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
      bne_iff_ne, ne_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨n, by omega, hUn⟩, h1⟩, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩
  · exact .inl (.inr ((shapeF_trees hs t).1 hM.1))
  · exact .inl (.inl (.inl hZ.1))
  · exact .inl (.inl (.inr hB.1))

/-- The test reads five fields alone. -/
theorem sortsB_same {sh : List Look} {a b : HTailF2} (h : SameRec a b) :
    sortsB sh b = sortsB sh a := by
  unfold sortsB tableAtB
  rw [h.ix, h.NM, h.gtTree, h.z1, h.z2]

/-- `Fork.trimL` keeps every array's look. -/
theorem looks_trimL (F : Fork) : F.trimL.trees.toList.map look = F.trees.toList.map look := by
  show ((F.trees.map fun X =>
    { X with rows := X.rows.map fun r => { r with L := #[] } }).toList.map look) = _
  rw [Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro X _
  exact look_rows_map X _

/-- **At whatever agrees in the five fields and the looks.** -/
theorem sorts_made (hs : tl₀.shapeF m txOf f hasU tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) (tlc : HTailF2)
    (hr : SameP tl' tlc) (Fc : Fork) (hL : Fc.trees.toList.map look = G.trees.toList.map look) :
    sortsB (Fc.trees.toList.map look) tlc = true := by
  rw [hL, sortsB_same ((addTreesF_sameP ha).trans hr).same]
  exact sorts_at hs ha

/-! ## The three routines -/

theorem planG_sorts (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : sortsB (hp.Fp.trees.toList.map look) hp.tl = true := by
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
    exact sorts_made hS hA _ (ownerIs_sameP tl1 g) _ (looks_trimL Fp)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact sorts_made hS hA _ ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) _
        (looks_trimL Fp)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seam_sorts {g : Settings} {m : Array TMat} {tau col0F ktO aO nU3 hb hbLine : Nat}
    {s s' : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s)
    (e' : s.plan nU3 hb hbLine = .ok s') (tlc : HTailF2) (hr : SameP s'.tl tlc) :
    sortsB (s'.Fp.trees.toList.map look) tlc = true := by
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut e
  obtain ⟨T, hA⟩ := seamPlan_cut e'
  exact sorts_made hS hA tlc hr s'.Fp rfl

theorem planA_sorts (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameP P.seam.tl tlc) : sortsB (P.seam.Fp.trees.toList.map look) tlc = true := by
  obtain ⟨seam0, h0, h1, -⟩ := planA_rows0 settings i cf P e
  exact seam_sorts h0 h1 tlc hr

theorem planH2_sorts (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork)
    (hL : Fc.trees.toList.map look = hp.Fp.trees.toList.map look) :
    sortsB (Fc.trees.toList.map look) hp.tl = true := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact sorts_made hS hA _ (ownerHeld_sameP hO) Fc hL
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ## The public parameters -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_sorts (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : sortsB (hp.Fp.trees.toList.map look) hp.tl = true :=
  planG_sorts X.layers g _ hp (public_G h g hp hg)

theorem public_H_sorts (h : Verify.publicOf pol KL layout = .ok X) :
    sortsB (X.H.Fp.trees.toList.map look) X.H.tl = true := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have k : sortsB (H0.Fp.trimL.trees.toList.map look) H0.tl = true :=
    planH2_sorts _ _ _ _ _ _ _ H0 h0 _ (looks_trimL H0.Fp)
  rw [e]
  exact k

theorem public_A_sorts (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) :
    sortsB (a.seam.Fp.trees.toList.map look) a.seam.tl = true := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameP k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show sortsB (a0.seam.Fp.trees.toList.map look) s.tl = true
    rw [f3] at f2
    exact planA_sorts _ _ _ a0 m2 s.tl f2
  · simp at e1

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.piecesF_ft
#print axioms VerifiableInference.Desc.LinkJoin.shapeF_ft
#print axioms VerifiableInference.Desc.LinkJoin.sym_at
#print axioms VerifiableInference.Desc.LinkJoin.oneRowTable_apart
#print axioms VerifiableInference.Desc.LinkJoin.sorts_at
#print axioms VerifiableInference.Desc.LinkJoin.sortsB_same
#print axioms VerifiableInference.Desc.LinkJoin.looks_trimL
#print axioms VerifiableInference.Desc.LinkJoin.sorts_made
#print axioms VerifiableInference.Desc.LinkJoin.planG_sorts
#print axioms VerifiableInference.Desc.LinkJoin.seam_sorts
#print axioms VerifiableInference.Desc.LinkJoin.planA_sorts
#print axioms VerifiableInference.Desc.LinkJoin.planH2_sorts
#print axioms VerifiableInference.Desc.LinkJoin.public_G_sorts
#print axioms VerifiableInference.Desc.LinkJoin.public_H_sorts
#print axioms VerifiableInference.Desc.LinkJoin.public_A_sorts
