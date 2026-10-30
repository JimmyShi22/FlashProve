-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AttBackHead.lean: at the lookup on the calls of an
attention link, under the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean) and g < 12
alone: there are public parameters of a lookup whose shape is the field fs of the plan of attention
group g; and wherever the step of the member at the border in front of that lookup accepts, the
hearing at these parameters has returned on the same rounds, and the attention link's field g holds
what was heard. Theorems: each joins earlier ones; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: attention group g stands at link 2 g + 1. `borderOf l d`
(Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the border in front of link l's lookup; d is
false for the lookup on the calls. The hearing at public parameters p is `hearVia p F rs`
(Johnson/Desc/First/Look/Via/Via.lean).

What is shown.
  `border_odd`: the border in front of the lookup on the calls of link 2 g + 1 has the number 14 (2
    g + 1) + 3.
  `site_fs_att_head`: a site on the calls at link 2 g + 1 has public parameters of the shape a.fs,
    where a is the plan at g.
  `att_back_head`: the two together, at the border's number and at every number ft of the first
    tree.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hg`: (in `att_back_head`) g is below 12.
  `hs`, `hl`, `hd`, `ha`: (in `site_fs_att_head`) s is a site of the public part; its link is 2 g +
    1; it is on the calls; a is the plan at g.
No public test is assumed.

How the proof goes. The theorems call `site_calls_head` (Honest/K3/Law/Thread/SiteThereHead.lean),
`back_g_link` (Honest/K3/Law/Thread/AtLink.lean) and `site_facts` (Honest/K3/Law/MemberSite.lean),
and the library's `guard_theorems` and `p4_of_public` (Johnson/Desc/First/Att/GuardPlan.lean) and
`planIs_public` (Johnson/Desc/First/Att/GuardPublic.lean).

Users. Honest/K3/Law/Thread/LaysAttHead.lean calls `border_odd` and `site_fs_att_head`.

Limits. On the verifier's side alone. At the full size alone: that limit comes with `P5J.AtMgA`.
`att_back_head` says nothing where that member's step never accepts. No instance of these hypotheses
is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.First.Att.GuardPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (P placeAt)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The number of the border in front of the lookup on the calls of link 2 g + 1. -/
theorem border_odd (g : Nat) : borderOf (2 * g + 1) false = 14 * (2 * g + 1) + 3 := by
  unfold borderOf ixOf
  have h24 : ¬ (2 * g + 1 = 24) := by omega
  rw [if_neg h24]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A site on the calls at link 2 g + 1 has public parameters of the shape of the plan at g.**
Conditional on `P5J.AtMgA`, the site and the plan. -/
theorem site_fs_att_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (g : Nat) (hl : s.link = 2 * g + 1) (hd : s.digits = false)
    (a : OnBytes.Attention.Plan) (ha : (P5J.At.X Zp).A[g]? = some a) : s.p.shape = some a.fs := by
  unfold lookSites at hs
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ y s hsy
  rw [← f3, ← f4, hl, hd] at f1
  unfold placeAt at f1
  obtain ⟨pl, hpl, e⟩ := Option.map_eq_some_iff.1 f1
  obtain ⟨g1, _, g3, _, _⟩ := VerifiableInference.Desc.First.Att.P.guard_theorems
    (VerifiableInference.Desc.First.Att.P.planIs_public h.pubOne)
    (VerifiableInference.Desc.First.Att.P.p4_of_public h.pubOne ha) ha hpl
    (OnBytes.Params.settingOf Zp.p.X.P.frame)
  rw [← e, g1, g3]

/-- **At the border's number**: public parameters of the shape a.fs at which, wherever the member's
step accepts, the hearing has returned on the same rounds and the attention link's field g holds
what was heard. Conditional on `P5J.AtMgA` and g < 12. No instance of these hypotheses is exhibited
in this file. F is bound by "∃" and held by what functions return at it alone: some value: not said
to be the step's own. -/
theorem att_back_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∀ (a : OnBytes.Attention.Plan) (blk₃ : Block TS ProofFile.Cl), (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : P, p.shape = some a.fs ∧
        ∀ (ft : Nat) (sj s' : TS) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat),
          blk₃.step ft sj rs c = .ok (s', n) →
          ∃ F H G₁, hearVia p F rs = some (H, G₁) ∧
            ∀ att, s'.here = .att att → att.g = some H := by
  intro a blk₃ ha hb
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_calls_head h (2 * g + 1) hl
  refine ⟨s.p, site_fs_att_head h s hs g e1 e2 a ha, fun ft sj s' rs c n hstep => ?_⟩
  have hb' : cF.blocksInOrder[borderOf s.link false]? = some blk₃ := by rw [e1, border_odd]; exact hb
  obtain ⟨F, H, G, _, hv, hput⟩ :=
    back_g_link h s hs (by rw [e1]; exact hl) e2 blk₃ hb' ft sj s' n rs c hstep
  exact ⟨F, H, G, hv, hput⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.border_odd
#print axioms ProofFile.Honest.K3.Law.AtThr.site_fs_att_head
#print axioms ProofFile.Honest.K3.Law.AtThr.att_back_head
