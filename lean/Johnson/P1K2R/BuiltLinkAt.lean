-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/BuiltLinkAt.lean: code switching: THE BUILT LINK AT l, IN THE GOALS' SCOPE, WHERE THE
VALUE IS LAID: its kind, its group, its number of slots and its list of arrays are its own plan's: A
LAW OF THE PLANNER's TEXT: no pinned test, no decision of Lean's kernel. For the conjuncts of
P1K2.linkPlanB and P1K2.headPlanB (Johnson/P1K2R/PlanBools.lean) that read these numbers. NO
SUB-PROTOCOL IMPORTS THIS FILE.
THE ROAD. The public part's built links are builtOf's with the routines blanked
(ProofFile.Law.pub_builtOf, Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean). builtOf is buildLinksH of
linksOf. In scope there are twelve groups with attention (Meaning.scope_plans), and then the links
alternate, each with its sub-plan's numbers (Meaning.links_alternate,
Johnson/Goal/Meaning/PlanShapes.lean). linksOf's three makers of sub-plans take ns and Fp from the
plan.
  public_at_laid    publicOf's value is the public part's plan, at the second hash function
  zipped_back       a member of the list that is run is a built link, but for its routine
  blank_at          the public part's built link at k, from builtOf's
  built_cut         what lies beneath the two statements
  built_link_at     THE STATEMENT at l < 24
  built_head_at     THE STATEMENT at 24
LIMITS. Nothing on arrayOf, nor on what the plans' numbers are. In scope alone (twelve groups with
attention). No soundness is claimed.
-/
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Goal.Meaning.PlanShapes
import Johnson.P5J.LaidOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf linksOf builtOf layersPlanOf attentionPlanOf headPlanOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)
open OnBytes.L5.LinksOrder (zipped)
open Meaning (IsLink)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem public_at_laid (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
  rw [← VerifiableInference.PlanWritten.publicOfO_older]
  exact L.publicO

/-- A member of the list that is run is a built link, but for its routine. -/
theorem zipped_back {B : LinksH} {ls : Array LinkH} {k : ℕ} {l : LinkH}
    (h : (zipped B ls)[k]? = some l) :
    ∃ b, B.links[k]? = some b ∧ b.kind = l.kind ∧ b.g = l.g ∧ b.ns = l.ns ∧ b.Fp = l.Fp := by
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
      exact ⟨b, rfl, rfl, rfl, rfl, rfl⟩

/-- The public part's built link at k, from builtOf's. -/
theorem blank_at {b : LinksH} (e : ProofFile.Law.blankB b = Zp.p.built) {k : ℕ} {x : LinkH}
    (h : b.links[k]? = some x) :
    ∃ X, Zp.p.built.links[k]? = some X ∧ X.kind = x.kind ∧ X.g = x.g ∧ X.ns = x.ns ∧
      X.Fp = x.Fp := by
  refine ⟨ProofFile.Law.blank x, ?_, rfl, rfl, rfl, rfl⟩
  rw [← e]
  show (b.links.map ProofFile.Law.blank)[k]? = _
  rw [Array.getElem?_map, h]
  rfl

/-- **What lies beneath the two statements.** -/
theorem built_cut (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (∀ g < 12, ∃ hp a X X', Zp.p.X.G[g]? = some hp ∧ Zp.p.X.A[g]? = some a ∧
      Zp.p.built.links[2 * g]? = some X ∧ X.kind = 0 ∧ X.g = g ∧ X.ns = hp.ns ∧ X.Fp = hp.Fp ∧
      Zp.p.built.links[2 * g + 1]? = some X' ∧ X'.kind = 1 ∧ X'.g = g ∧ X'.ns = a.ns ∧
        X'.Fp = a.seam.Fp) ∧
      ∃ b, Zp.p.built.links[24]? = some b ∧ b.kind = 2 ∧ b.ns = Zp.p.X.H.ns ∧
        b.Fp = Zp.p.X.H.Fp := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hX := public_at_laid L
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hZ hR hX
  obtain ⟨b, hb, eb⟩ := ProofFile.Law.pub_builtOf
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp from L.pub)
  unfold builtOf at hb
  obtain ⟨l₀, h₀, hB⟩ := OnBytes.L5.LinksOrder.ok_bind hb
  unfold linksOf at h₀
  rw [hq, hN] at h₀ hB
  obtain ⟨-, alt, l24, e24, I24⟩ := Meaning.links_alternate h₀ hB h₀
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨s, a', l, l', hs, ha, e1, I1, e2, I2⟩ := alt g hg
    rw [Array.getElem?_mapIdx] at hs
    rw [Array.getElem?_map] at ha
    cases hG : Zp.p.X.G[g]? with
    | none => rw [hG] at hs; cases hs
    | some hp =>
      rw [hG] at hs
      obtain rfl := Option.some.inj hs
      cases hA : Zp.p.X.A[g]? with
      | none => rw [hA] at ha; cases ha
      | some a =>
        rw [hA] at ha
        obtain rfl := Option.some.inj ha
        obtain ⟨x1, f1, k1, g1, n1, p1⟩ := zipped_back e1
        obtain ⟨x2, f2, k2, g2, n2, p2⟩ := zipped_back e2
        obtain ⟨X1, c1, K1, G1, N1, P1⟩ := blank_at eb f1
        obtain ⟨X2, c2, K2, G2, N2, P2⟩ := blank_at eb f2
        exact ⟨hp, a, X1, X2, rfl, rfl, c1, K1.trans (k1.trans I1.kind), G1.trans (g1.trans I1.g),
          N1.trans (n1.trans I1.ns), P1.trans (p1.trans I1.Fp), c2, K2.trans (k2.trans I2.kind),
          G2.trans (g2.trans I2.g), N2.trans (n2.trans I2.ns), P2.trans (p2.trans I2.Fp)⟩
  · obtain ⟨x, f, k, -, n, p⟩ := zipped_back e24
    obtain ⟨X, c, K, -, N, P⟩ := blank_at eb f
    exact ⟨X, c, K.trans (k.trans I24.kind), N.trans (n.trans I24.ns), P.trans (p.trans I24.Fp)⟩

/-- **The built link at l < 24.** -/
theorem built_link_at (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 24) :
    ∃ X, Zp.p.built.links[l]? = some X ∧ Zp.made.p.built.links[l]? = some X ∧ X.g = l / 2 ∧
      ((l % 2 = 1 ∧ X.kind = 1 ∧
          ∃ a, Zp.p.X.A[l / 2]? = some a ∧ X.ns = a.ns ∧ X.Fp = a.seam.Fp) ∨
        (l % 2 = 0 ∧ X.kind = 0 ∧
          ∃ hp, Zp.p.X.G[l / 2]? = some hp ∧ X.ns = hp.ns ∧ X.Fp = hp.Fp)) := by
  obtain ⟨hp, a, X, X', hG, hA, c1, K1, G1, N1, P1, c2, K2, G2, N2, P2⟩ :=
    (built_cut hZ L).1 (l / 2) (by omega)
  rcases Nat.mod_two_eq_zero_or_one l with h0 | h1
  · have e : 2 * (l / 2) = l := by omega
    rw [e] at c1
    exact ⟨X, c1, c1, G1, Or.inr ⟨h0, K1, hp, hG, N1, P1⟩⟩
  · have e : 2 * (l / 2) + 1 = l := by omega
    rw [e] at c2
    exact ⟨X', c2, c2, G2, Or.inl ⟨h1, K2, a, hA, N2, P2⟩⟩

/-- **The built link at 24: the head's.** -/
theorem built_head_at (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ b, Zp.p.built.links[24]? = some b ∧ Zp.made.p.built.links[24]? = some b ∧ b.kind = 2 ∧
      b.ns = Zp.p.X.H.ns ∧ b.Fp = Zp.p.X.H.Fp := by
  obtain ⟨b, c, K, N, P⟩ := (built_cut hZ L).2
  exact ⟨b, c, c, K, N, P⟩

end P1K2

#print axioms P1K2.public_at_laid
#print axioms P1K2.zipped_back
#print axioms P1K2.blank_at
#print axioms P1K2.built_cut
#print axioms P1K2.built_link_at
#print axioms P1K2.built_head_at
