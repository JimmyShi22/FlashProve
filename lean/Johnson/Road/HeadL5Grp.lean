-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5Grp.lean: the shapes of the attention plans in the public part of a stage are
shapes of what the verifier's function Attention.group returns.

The theorems on an attention link's shape begin: "if Attention.group P y sc midQ lines g returns a
plan". The links of a request are made of the plans X.A in what publicOf returns
(OnBytes/Model/VerifyPublic.lean). This file is the joint between the two.

How. At profile 4, publicOf calls Attention.config (OnBytes/Model/AttentionConfig.lean), which runs
group for each g below the number of groups and returns the list of the plans. publicOf then fills
one record in each plan's seam (attentionOwners in OnBytes/Model/VerifyCross.lean, which sets places
of an array and does not shorten it) and joins the result with the plans, member by member. The
shape of a plan is not touched.

Main definitions: shapeA (the shape of the attention plan of group g); midQOf.
Main theorems: mapM_ok, mapM_length (a list of values of a function that may refuse); config_groups;
owners_size; zipWith_at, zipWith_atA; pubOf_sc, scales_of_public, scalesHeld_of_public (the scales
in the public part are the scale file's, and have passed the tests on them); groups_of_public.

What is not claimed. Nothing on what group returns. Nothing on the seams. That publicOf returns a
value is a hypothesis. The program does not import this file.
-/
import Johnson.Road.HeadScan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

/-! ## Tools -/

/-- If a function that may refuse returns a value on every member of a list, the list of the values
has at each place the value on the member at that place. -/
theorem mapM_ok {α β : Type} (f : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → ∀ (i : ℕ) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = .ok b
  | [], _, _, i, a, hi => by simp at hi
  | x :: l, r, h, i, a, hi => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := ok_of_bind h
    obtain ⟨bs, hbs, h⟩ := ok_of_bind h
    have e : b :: bs = r := Except.ok.inj h
    subst e
    cases i with
    | zero =>
      have e0 : x = a := by simpa using hi
      subst e0
      exact ⟨b, rfl, hb⟩
    | succ i =>
      have hi' : l[i]? = some a := by simpa using hi
      obtain ⟨b', h1, h2⟩ := mapM_ok f l bs hbs i a hi'
      exact ⟨b', by simpa using h1, h2⟩

/-- The list of the values is as long as the list. -/
theorem mapM_length {α β : Type} (f : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    have e : [] = r := Except.ok.inj h
    rw [← e]
    rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, -, h⟩ := ok_of_bind h
    obtain ⟨bs, hbs, h⟩ := ok_of_bind h
    have e : b :: bs = r := Except.ok.inj h
    rw [← e, List.length_cons, List.length_cons, mapM_length f l bs hbs]

/-- A place of two lists joined member by member. -/
theorem zipWith_at {α β γ : Type} (f : α → β → γ) : ∀ (as : List α) (bs : List β) (g : ℕ) (a : α)
    (b : β), as[g]? = some a → bs[g]? = some b → (List.zipWith f as bs)[g]? = some (f a b)
  | [], _, g, a, b, ha, _ => by simp at ha
  | _ :: _, [], g, a, b, _, hb => by simp at hb
  | x :: as, y :: bs, 0, a, b, ha, hb => by
    have e1 : x = a := by simpa using ha
    have e2 : y = b := by simpa using hb
    rw [List.zipWith_cons_cons, e1, e2]
    rfl
  | x :: as, y :: bs, g + 1, a, b, ha, hb => by
    rw [List.zipWith_cons_cons]
    have k := zipWith_at f as bs g a b (by simpa using ha) (by simpa using hb)
    simpa using k

/-- The same for arrays. -/
theorem zipWith_atA {α β γ : Type} (f : α → β → γ) (as : Array α) (bs : Array β) {g : ℕ} {a : α}
    {b : β} (ha : as[g]? = some a) (hb : bs[g]? = some b) :
    (as.zipWith f bs)[g]? = some (f a b) := by
  have k : (as.zipWith f bs).toList[g]? = some (f a b) := by
    rw [Array.toList_zipWith]
    exact zipWith_at f _ _ g a b (by simpa using ha) (by simpa using hb)
  rw [← Array.getElem?_toList]
  exact k

/-! ## The verifier's functions -/

/-- **The plans that Attention.config returns are the values of Attention.group**, one for each
group of layers. -/
theorem config_groups {P : Model.PolScan} {y : Model.Layer.Lay} {s : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {c : Attention.Config} (h : Attention.config P y s midQ = .ok c) :
    ∃ lines, c.plans.size = y.NGr ∧ ∀ g, g < y.NGr →
      ∃ Xg, c.plans[g]? = some Xg ∧ Attention.group P y s midQ lines g = .ok Xg := by
  unfold Attention.config at h
  obtain ⟨lines, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨plans, hm, h⟩ := ok_of_bind h
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨-, -, h⟩ := ok_of_bind h
    cases h
    refine ⟨lines, ?_, fun g hg => ?_⟩
    · have k := mapM_length _ _ _ hm
      rw [List.length_range] at k
      show (X0 :: rest).toArray.size = y.NGr
      rw [List.size_toArray]
      exact k
    · obtain ⟨Xg, h1, h2⟩ := mapM_ok _ _ _ hm g g (by simp [hg])
      exact ⟨Xg, by simpa using h1, h2⟩

/-- Filling the records of attention's plans keeps their number. -/
theorem owners_size {p4 : Bool} {NGr : ℕ} {G A r : Array Model.Verify.SubPlan}
    (h : Model.Verify.attentionOwners p4 NGr G A = .ok r) : r.size = A.size := by
  unfold Model.Verify.attentionOwners at h
  split at h
  · obtain ⟨-, -, h⟩ := ok_of_bind h
    unfold Model.Verify.attentionOwnerPlaces at h
    refine foldlM_keeps _ (fun t : Array Model.Verify.SubPlan => t.size = A.size)
      (fun t g t' hI ht => ?_) _ _ _ rfl h
    split at ht
    · obtain ⟨v, -, ht⟩ := ok_of_bind ht
      have e : t.set! g v = t' := Except.ok.inj ht
      rw [← e]
      simpa using hI
    · cases ht
  · have e : A = r := Except.ok.inj h
    rw [e]

/-- The record of the layers' public numbers holds the scales from which it was made. -/
theorem pubOf_sc {y : Model.Layer.Lay} {sc : Model.Layer.Scales} {rope : Array ℕ}
    {wsLay : Model.WsLay} {V : ℕ} {tokv : Array ℕ} {set : Model.Settings} {Z : Model.Layer.Pub}
    (h : Model.Layer.Pub.of y sc rope wsLay V tokv set = .ok Z) : Z.sc = sc := by
  unfold Model.Layer.Pub.of at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨rd, -, h⟩ := ok_of_bind h
  cases h
  rfl

/-- The scales in the public part are what the verifier's function reads off the scale file, and
they have passed its tests on them. -/
theorem scalesBoth_of_public {pol KL : ByteArray} {lay : Option ByteArray}
    {X : Model.Verify.Public} (h : Model.Verify.publicOf pol KL lay = .ok X) :
    Model.Layer.scalesOf X.y.h (Model.fileWords KL) = .ok X.layers.sc ∧
      Model.Layer.scalesHeld X.y.h X.layers.sc = .ok () := by
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P, y⟩, -, h⟩ := ok_of_bind h
  obtain ⟨sc, hsc, h⟩ := ok_of_bind h
  obtain ⟨u, hheld, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_ite2 h
  obtain ⟨layers, hPub, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  have ey : layers.y = y := pubOf_y hPub
  have es : layers.sc = sc := pubOf_sc hPub
  refine ⟨?_, ?_⟩
  · show Model.Layer.scalesOf layers.y.h (Model.fileWords KL) = .ok layers.sc
    rw [ey, es]
    exact hsc
  · show Model.Layer.scalesHeld layers.y.h layers.sc = .ok ()
    rw [ey, es]
    exact hheld

/-- **The scales in the public part are what the verifier's function reads off the scale file.** -/
theorem scales_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) :
    Model.Layer.scalesOf X.y.h (Model.fileWords KL) = .ok X.layers.sc :=
  (scalesBoth_of_public h).1

/-- They have passed the verifier's tests on the scales. -/
theorem scalesHeld_of_public {pol KL : ByteArray} {lay : Option ByteArray}
    {X : Model.Verify.Public} (h : Model.Verify.publicOf pol KL lay = .ok X) :
    Model.Layer.scalesHeld X.y.h X.layers.sc = .ok () :=
  (scalesBoth_of_public h).2

/-- The shape of the attention plan of group g in a public part; the default shape where there is no
such plan. -/
def shapeA (X : Model.Verify.Public) (g : ℕ) : Attention.Shape :=
  ((X.A[g]?).map (·.S)).getD default

/-- The number that names the matrix qa of group g, as publicOf hands it to Attention.config. -/
def midQOf (y : Model.Layer.Lay) (g : ℕ) : ℕ :=
  (((Model.Layer.tailsOf y).getD g {}).mats.getD (Model.Layer.matIx y).iQA {}).aId

/-- **The joint.** At profile 4, each attention plan in the public part of a stage has the shape of
what Attention.group returns for its group, at the parameter file, the layers' layout and the scales
of that public part. It is that value with one record of its seam filled: shape, lookup shape and
what the caller passed are kept. A0: the plans as Attention.config returns them; seenA: what
attentionOwners makes of their seams; the filled record is seenA's. -/
theorem groups_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) :
    ∃ (lines : List Attention.Line) (A0 : Array Attention.Plan)
      (seenG seenA : Array Model.Verify.SubPlan),
      Model.Verify.attentionOwners X.y.h.p4 X.y.NGr seenG
        (A0.map fun Z => ⟨Z.seam.tl, Z.seam.Fp, Z.seam.Tp⟩) = .ok seenA ∧
      ∀ g, g < X.y.NGr →
        ∃ Xg Ag s, Attention.group X.P X.y X.layers.sc (midQOf X.y) lines g = .ok Xg ∧
          A0[g]? = some Xg ∧ seenA[g]? = some s ∧ X.A[g]? = some Ag ∧ Ag.S = Xg.S ∧
          Ag.fs = Xg.fs ∧ Ag.inp = Xg.inp ∧ Ag.seam.tl = s.tl ∧ shapeA X g = Xg.S := by
  obtain ⟨P, y, hpl1, eP, -⟩ := public_parts h
  have hq1 : y.h.p4 = true := by
    rw [layout_shape (layerLayout_of_polLayout hpl1), ← eP]
    exact hp4
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P', y'⟩, hpl, h⟩ := ok_of_bind h
  have e : (P, y) = (P', y') := Except.ok.inj (hpl1.symm.trans hpl)
  cases e
  obtain ⟨sc, -, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  dsimp only at h
  rw [if_pos hq1] at h
  obtain ⟨c, hcfg, h⟩ := ok_of_bind h
  obtain ⟨⟨A0, hC⟩, hpure, h⟩ := ok_of_bind h
  have e2 : (c.plans, c.hCallsA) = (A0, hC) := Except.ok.inj hpure
  cases e2
  obtain ⟨layers, hPub, h⟩ := ok_of_bind h
  obtain ⟨G, -, h⟩ := ok_of_bind h
  obtain ⟨seenA, hown, h⟩ := ok_of_bind h
  obtain ⟨owner, -, h⟩ := ok_of_bind h
  obtain ⟨H, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  cases h
  have ey : layers.y = y := pubOf_y hPub
  have es : layers.sc = sc := pubOf_sc hPub
  obtain ⟨lines, hsz, hgrp⟩ := config_groups hcfg
  have hs2 : seenA.size = c.plans.size := by rw [owners_size hown, Array.size_map]
  refine ⟨lines, c.plans, G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : Model.Verify.SubPlan), seenA, ?_,
    fun g hg => ?_⟩
  · show Model.Verify.attentionOwners layers.y.h.p4 layers.y.NGr _ _ = .ok seenA
    rw [ey]
    exact hown
  have hg' : g < y.NGr := by
    have k : g < layers.y.NGr := hg
    rw [ey] at k
    exact k
  obtain ⟨Xg, h1, h2⟩ := hgrp g hg'
  have hlt : g < seenA.size := by
    rw [hs2, hsz]
    exact hg'
  have hb : seenA[g]? = some seenA[g] := by simp [hlt]
  refine ⟨Xg, _, seenA[g], ?_, h1, hb, zipWith_atA _ _ _ h1 hb, rfl, rfl, rfl, rfl, ?_⟩
  · show Attention.group P layers.y layers.sc (midQOf layers.y) lines g = .ok Xg
    rw [ey, es]
    exact h2
  · unfold shapeA
    dsimp only
    rw [zipWith_atA _ _ _ h1 hb]
    rfl

#print axioms config_groups
#print axioms owners_size
#print axioms scales_of_public
#print axioms groups_of_public

end OnBytes.Road.Hd
