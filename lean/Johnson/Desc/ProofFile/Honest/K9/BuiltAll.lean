-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BuiltAll.lean: WHAT HOLDS OF THE LEDGER AND THE LIST OF ARRAYS OF EVERY SUB-PROOF's PLAN HOLDS
OF THE RECORD OF EACH OF THE 25 SEGMENTS, as the public part holds it: in the goals' scope, by the planner's text. General in
the sentence.

  `zipped_backA`, `blank_atA`   a record's ledger, list of arrays and table of names go unchanged through the two re-dressings
                        of the records
  **`built_all`**   Φ at the ledger and the list of each feed-forward plan, of each attention plan's seam and of the head's
                    plan: then at each l < 25 the record is there, and Φ holds of its ledger and list
  `ground_record`   the record that the description's lots read at l is the public part's, in these three fields

How. The road is the library's (`P1K2.built_cut`, Johnson/P1K2R/BuiltLinkAt.lean): the segments alternate, each with its
sub-plan's fields (`Meaning.links_alternate`, Johnson/Goal/Meaning/PlanShapes.lean). Honest/K9/BuiltFresh.lean walks it at two
sentences; here the sentence is a variable.

Limits. In the goals' scope (twelve groups with attention), at the hash function `secondHashFunction`. This file proves no property of a
prover or a protocol.
-/
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
open ProofFile (Cl)

/-- A member of the list that is run is a built record, but for its routine. -/
theorem zipped_backA {B : LinksH} {ls : Array LinkH} {k : ℕ} {l : LinkH}
    (h : (zipped B ls)[k]? = some l) :
    ∃ b, B.links[k]? = some b ∧ b.Fp = l.Fp ∧ b.Tp = l.Tp ∧ b.arrayOf = l.arrayOf := by
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
      exact ⟨b, rfl, rfl, rfl, rfl⟩

/-- The public part's record at k, from the planner's. -/
theorem blank_atA {Z : ProofFile.Pub} {b : LinksH} (e : ProofFile.Law.blankB b = Z.p.built) {k : ℕ} {x : LinkH}
    (h : b.links[k]? = some x) : ∃ X, Z.p.built.links[k]? = some X ∧ X.Fp = x.Fp ∧ X.Tp = x.Tp := by
  refine ⟨ProofFile.Law.blank x, ?_, rfl, rfl⟩
  rw [← e]
  show (b.links.map ProofFile.Law.blank)[k]? = _
  rw [Array.getElem?_map, h]
  rfl

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The 25 records, at any sentence on a plan's ledger and list.** -/
theorem built_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (Φ : Fork → Tail2 → Prop)
    (hG : ∀ (g : ℕ) (hp : Layer.HPlan2), Z.p.X.G[g]? = some hp → Φ hp.Fp hp.Tp)
    (hA : ∀ (g : ℕ) (a : Attention.Plan), Z.p.X.A[g]? = some a → Φ a.seam.Fp a.seam.Tp)
    (hH : Φ Z.p.X.H.Fp Z.p.X.H.Tp) :
    ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ Φ X.Fp X.Tp := by
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
  have two : ∀ g < 12, (∃ X, Z.p.built.links[2 * g]? = some X ∧ Φ X.Fp X.Tp) ∧
      ∃ X, Z.p.built.links[2 * g + 1]? = some X ∧ Φ X.Fp X.Tp := by
    intro g hg
    obtain ⟨s, a', l, l', hs, ha, e1, I1, e2, I2⟩ := alt g hg
    rw [Array.getElem?_mapIdx] at hs
    rw [Array.getElem?_map] at ha
    cases hGg : Z.p.X.G[g]? with
    | none => rw [hGg] at hs; cases hs
    | some hp =>
      rw [hGg] at hs
      obtain rfl := Option.some.inj hs
      cases hAg : Z.p.X.A[g]? with
      | none => rw [hAg] at ha; cases ha
      | some a =>
        rw [hAg] at ha
        obtain rfl := Option.some.inj ha
        obtain ⟨x1, f1, p1, t1, -⟩ := zipped_backA e1
        obtain ⟨x2, f2, p2, t2, -⟩ := zipped_backA e2
        obtain ⟨X1, c1, P1, T1⟩ := blank_atA eb f1
        obtain ⟨X2, c2, P2, T2⟩ := blank_atA eb f2
        have q1 : X1.Tp = hp.Tp := T1.trans (t1.trans I1.Tp)
        have q2 : X1.Fp = hp.Fp := P1.trans (p1.trans I1.Fp)
        have q3 : X2.Tp = a.seam.Tp := T2.trans (t2.trans I2.Tp)
        have q4 : X2.Fp = a.seam.Fp := P2.trans (p2.trans I2.Fp)
        exact ⟨⟨X1, c1, by rw [q1, q2]; exact hG g hp hGg⟩, ⟨X2, c2, by rw [q3, q4]; exact hA g a hAg⟩⟩
  intro l hl
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨x, f, p, t, -⟩ := zipped_backA e24
    obtain ⟨X, c, Pq, T⟩ := blank_atA eb f
    have q : X.Tp = Z.p.X.H.Tp := T.trans (t.trans I24.Tp)
    have q' : X.Fp = Z.p.X.H.Fp := Pq.trans (p.trans I24.Fp)
    exact ⟨X, c, by rw [q, q']; exact hH⟩
  · rcases Nat.mod_two_eq_zero_or_one l with h0 | h1
    · have e : 2 * (l / 2) = l := by omega
      have k := (two (l / 2) (by omega)).1
      rwa [e] at k
    · have e : 2 * (l / 2) + 1 = l := by omega
      have k := (two (l / 2) (by omega)).2
      rwa [e] at k

/-- The record that the description's lots read at l is the public part's, in three fields. -/
theorem ground_record (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} {X : LinkH}
    (h : Bs.G₀.built[l]? = some X) :
    ∃ b, Z.p.built.links[l]? = some b ∧ b.Fp = X.Fp ∧ b.Tp = X.Tp ∧ b.arrayOf = X.arrayOf := by
  obtain ⟨ls, -, -, eB, -⟩ := IM.blank_ground O.blank
  rw [eB] at h
  exact zipped_backA h

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.zipped_backA
#print axioms ProofFile.Honest.K9.blank_atA
#print axioms ProofFile.Honest.K9.built_all
#print axioms ProofFile.Honest.K9.ground_record
