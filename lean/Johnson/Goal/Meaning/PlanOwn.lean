-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PlanOwn.lean: the sizes of an attention sub-proof's own rounds against its
shape, at the plans of the public part.

WHY. An attention plan a of the public part X has a shape a.S and a record a.own of the sizes of the
sub-proof's own rounds. Means (Johnson/Goal/Meaning/Row.lean) speaks at dimOf, sclOf, tbOf of the
shape; a block of the own rounds may be given a.own. The two are tied by the text of Attention.plan
(OnBytes/Model/AttentionPlan.lean), which fills own out of the shape.

  plan_own          where Attention.plan returns P: eleven of the twelve fields of P.own are
                    functions of P.S (lt, lgk, pairs, Lam, planeMessages, score, e, valueM, valueD,
                    attained, bits).
  own_kept          at profile 4 each attention plan of the public part has the shape AND the own
                    rounds' sizes of what Attention.group returns for its group. (The steps are
                    those of Hd.groups_of_public, Johnson/Road/HeadL5Grp.lean, which exports the
                    shape alone.)
  glue_plan_A       so it has those of a plan that Attention.plan has made: the conclusion of the
                    library's statement row_glue_plan_A (OnBytes/Tie/Pv/Tail/GlueRows.lean), at
                    profile 4 and a group below X.y.NGr.
  own_of_shape      so, in the goals' scope, for g < 12: the eleven equations at X.A[g].

What is not claimed. The twelfth field, rows (the number of linear claims and equations), is not
tied here. Nothing on what a block does with these numbers. Nothing on soundness.
-/
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Road.Lane5AttPlan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

/-- **At profile 4 an attention plan of the public part keeps the shape and the own rounds' sizes of
what Attention.group returns.** -/
theorem own_kept {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) :
    ∃ lines : List Attention.Line, ∀ g, g < X.y.NGr →
      ∃ Xg Ag, Attention.group X.P X.y X.layers.sc (midQOf X.y) lines g = .ok Xg ∧
        X.A[g]? = some Ag ∧ Ag.S = Xg.S ∧ Ag.own = Xg.own := by
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
  refine ⟨lines, ?_⟩
  have hs2 : seenA.size = c.plans.size := by rw [owners_size hown, Array.size_map]
  intro g hg
  have hg' : g < y.NGr := by
    have k : g < layers.y.NGr := hg
    rw [ey] at k
    exact k
  obtain ⟨Xg, h1, h2⟩ := hgrp g hg'
  have hlt : g < seenA.size := by
    rw [hs2, hsz]
    exact hg'
  have hb : seenA[g]? = some seenA[g] := by simp [hlt]
  refine ⟨Xg, _, ?_, zipWith_atA _ _ _ h1 hb, rfl, rfl⟩
  show Attention.group P layers.y layers.sc (midQOf layers.y) lines g = .ok Xg
  rw [ey, es]
  exact h2

end OnBytes.Road.Hd

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Model
open OnBytes.Model.Verify (publicOf layerShape)

/-- Eleven fields of the own rounds' sizes, as functions of the shape. -/
structure OwnOfShape (a : Attention.Plan) : Prop where
  lt : a.own.lt = a.S.cf.lt
  lgk : a.own.lgk = a.S.cf.lgk
  pairs : a.own.pairs = a.S.NP
  Lam : a.own.Lam = a.S.Lam
  planeMessages : a.own.planeMessages = (Attention.Counts.of a.S).nKRp
  score : a.own.score = (Attention.Counts.of a.S).score.toList
  e : a.own.e = a.S.nvE
  valueM : a.own.valueM = a.S.nvVM
  valueD : a.own.valueD = a.S.nvVD
  attained : a.own.attained = a.S.nvF
  bits : a.own.bits = a.S.nvH

/-- **Where Attention.plan returns, own is filled out of the shape.** -/
theorem plan_own {settings : Settings} {i : Attention.In} {cf : Attention.Cfg} {P : Attention.Plan}
    (h : Attention.plan settings i cf = .ok P) : OwnOfShape P := by
  unfold Attention.plan at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- **A member of X.A has the shape and the own rounds' sizes of a plan that Attention.plan has
made**, at profile 4. -/
theorem glue_plan_A {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) (hp4 : (layerShape X.P).p4 = true) {g : ℕ}
    (hg : g < X.y.NGr) {a : Attention.Plan} (ha : X.A[g]? = some a) :
    ∃ settings i cf P0, Attention.plan settings i cf = .ok P0 ∧ a.S = P0.S ∧ a.own = P0.own := by
  obtain ⟨lines, H⟩ := Hd.own_kept h hp4
  obtain ⟨Xg, Ag, hG, hA, eS, eO⟩ := H g hg
  obtain rfl : Ag = a := Option.some.inj (hA.symm.trans ha)
  obtain ⟨cf, -, hp, -⟩ := L5.group_plan hG
  exact ⟨_, _, cf, Xg, hp, eS, eO⟩

/-- **In scope: the own rounds' sizes of each attention plan are its shape's.** -/
theorem own_of_shape {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ha : X.A[g]? = some a) : OwnOfShape a := by
  have A := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  obtain ⟨_, _, _, P0, hp, eS, eO⟩ := glue_plan_A h B.p4 (by rw [B.groups]; exact hg) ha
  have O := plan_own hp
  exact ⟨by rw [eO, eS]; exact O.lt, by rw [eO, eS]; exact O.lgk, by rw [eO, eS]; exact O.pairs,
    by rw [eO, eS]; exact O.Lam, by rw [eO, eS]; exact O.planeMessages,
    by rw [eO, eS]; exact O.score, by rw [eO, eS]; exact O.e, by rw [eO, eS]; exact O.valueM,
    by rw [eO, eS]; exact O.valueD, by rw [eO, eS]; exact O.attained, by rw [eO, eS]; exact O.bits⟩

end Meaning

#print axioms OnBytes.Road.Hd.own_kept
#print axioms Meaning.plan_own
#print axioms Meaning.glue_plan_A
#print axioms Meaning.own_of_shape
