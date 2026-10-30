-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BuiltFresh.lean: THE RECORD OF EACH OF THE 25 SEGMENTS, AS THE PUBLIC PART HOLDS IT, BEARS A
CLOSED LIST OF ARRAYS, and, in front of the head's, a ledger to which nothing has happened: in the goals' scope, by the
planner's text.

  `zipped_backT`, `blank_atT`   a record's ledger and list of arrays go unchanged through the two re-dressings of the records
  **`built_fresh`**   l < 24: the record at l is there, `Closed` of its list and `Plain` of its ledger
                      (Honest/K9/PlanFresh.lean); at 24: the record is there, and `Closed` of its list
  `letters_closed`   so of the head's segment's letters, as the code switch's lot reads them off the records

How. The road is the library's (`P1K2.built_cut`, Johnson/P1K2R/BuiltLinkAt.lean), with the list of arrays carried beside the
ledger: the segments alternate, each with its sub-plan's fields (`Meaning.links_alternate`,
Johnson/Goal/Meaning/PlanShapes.lean).

Limits. In the goals' scope (twelve groups with attention), at the hash function `secondHashFunction`. This file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PlanFresh
import Johnson.P1K2R.BuiltLinkAt
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf linksOf builtOf layersPlanOf attentionPlanOf headPlanOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)
open OnBytes.L5.LinksOrder (zipped)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (Closed Plain public_G_fresh public_A_fresh public_H_closed)
open ProofFile (Cl)

/-- A member of the list that is run is a built record, but for its routine. -/
theorem zipped_backT {B : LinksH} {ls : Array LinkH} {k : ℕ} {l : LinkH}
    (h : (zipped B ls)[k]? = some l) : ∃ b, B.links[k]? = some b ∧ b.Fp = l.Fp ∧ b.Tp = l.Tp := by
  unfold zipped at h
  rw [Array.getElem?_zipWith] at h
  cases hb : B.links[k]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hl : ls[k]? with
    | none => rw [hl] at h; cases h
    | some y =>
      rw [hl] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl, rfl⟩

/-- The public part's record at k, from the planner's. -/
theorem blank_atT {Z : ProofFile.Pub} {b : LinksH} (e : ProofFile.Law.blankB b = Z.p.built) {k : ℕ} {x : LinkH}
    (h : b.links[k]? = some x) : ∃ X, Z.p.built.links[k]? = some X ∧ X.Fp = x.Fp ∧ X.Tp = x.Tp := by
  refine ⟨ProofFile.Law.blank x, ?_, rfl, rfl⟩
  rw [← e]
  show (b.links.map ProofFile.Law.blank)[k]? = _
  rw [Array.getElem?_map, h]
  rfl

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The 25 records.** -/
theorem built_fresh (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (∀ l < 24, ∃ X, Z.p.built.links[l]? = some X ∧ Closed X.Tp ∧ Plain X.Fp) ∧
      ∃ b, Z.p.built.links[24]? = some b ∧ Closed b.Tp := by
  have hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← O.W]
    exact O.public
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  obtain ⟨b, hb, eb⟩ := ProofFile.Law.pub_builtOf
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction P.pol lay P.KL = .ok Z from O.pub)
  unfold builtOf at hb
  obtain ⟨l₀, h₀, hB⟩ := OnBytes.L5.LinksOrder.ok_bind hb
  unfold linksOf at h₀
  rw [hq, hN] at h₀ hB
  obtain ⟨-, alt, l24, e24, I24⟩ := Meaning.links_alternate h₀ hB h₀
  have two : ∀ g < 12, (∃ X, Z.p.built.links[2 * g]? = some X ∧ Closed X.Tp ∧ Plain X.Fp) ∧
      ∃ X, Z.p.built.links[2 * g + 1]? = some X ∧ Closed X.Tp ∧ Plain X.Fp := by
    intro g hg
    obtain ⟨s, a', l, l', hs, ha, e1, I1, e2, I2⟩ := alt g hg
    rw [Array.getElem?_mapIdx] at hs
    rw [Array.getElem?_map] at ha
    cases hG : Z.p.X.G[g]? with
    | none => rw [hG] at hs; cases hs
    | some hp =>
      rw [hG] at hs
      obtain rfl := Option.some.inj hs
      cases hA : Z.p.X.A[g]? with
      | none => rw [hA] at ha; cases ha
      | some a =>
        rw [hA] at ha
        obtain rfl := Option.some.inj ha
        obtain ⟨x1, f1, p1, t1⟩ := zipped_backT e1
        obtain ⟨x2, f2, p2, t2⟩ := zipped_backT e2
        obtain ⟨X1, c1, P1, T1⟩ := blank_atT eb f1
        obtain ⟨X2, c2, P2, T2⟩ := blank_atT eb f2
        have eG := public_G_fresh hX g hp hG
        have eA := public_A_fresh hX g a hA
        have q1 : X1.Tp = hp.Tp := T1.trans (t1.trans I1.Tp)
        have q2 : X1.Fp = hp.Fp := P1.trans (p1.trans I1.Fp)
        have q3 : X2.Tp = a.seam.Tp := T2.trans (t2.trans I2.Tp)
        have q4 : X2.Fp = a.seam.Fp := P2.trans (p2.trans I2.Fp)
        exact ⟨⟨X1, c1, by rw [q1]; exact eG.1, by rw [q2]; exact eG.2⟩,
          ⟨X2, c2, by rw [q3]; exact eA.1, by rw [q4]; exact eA.2⟩⟩
  refine ⟨fun l hl => ?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one l with h0 | h1
    · have e : 2 * (l / 2) = l := by omega
      have k := (two (l / 2) (by omega)).1
      rwa [e] at k
    · have e : 2 * (l / 2) + 1 = l := by omega
      have k := (two (l / 2) (by omega)).2
      rwa [e] at k
  · obtain ⟨x, f, -, t⟩ := zipped_backT e24
    obtain ⟨X, c, -, T⟩ := blank_atT eb f
    have q : X.Tp = Z.p.X.H.Tp := T.trans (t.trans I24.Tp)
    exact ⟨X, c, by rw [q]; exact public_H_closed hX⟩

/-- The head's segment's letters, as the code switch's lot reads them off the records. -/
theorem letters_closed (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {HP : First.K2.HeadPar}
    (h : P1K2.pureLetters Bs.G₀ 24 = some HP) : Closed HP.X.Tp := by
  obtain ⟨b, hb, hc⟩ := (built_fresh hS hR O).2
  obtain ⟨ls, -, -, eB, -⟩ := IM.blank_ground O.blank
  unfold P1K2.pureLetters at h
  obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [eB] at hX
  obtain ⟨b', hb', -, t⟩ := zipped_backT hX
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  show Closed X.Tp
  rw [← t]
  exact hc

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.zipped_backT
#print axioms ProofFile.Honest.K9.blank_atT
#print axioms ProofFile.Honest.K9.built_fresh
#print axioms ProofFile.Honest.K9.letters_closed
