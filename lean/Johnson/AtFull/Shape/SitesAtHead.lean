-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SitesAtHead.lean: UNDER THE HEAD `P5J.AtMgA` A SITE IS MADE AT EACH OF THE
FIFTY ADDRESSES OF THE LOOKUPS' LOT (`ProofFile.Honest.K3.lookSites`,
Johnson/Desc/ProofFile/Honest/K3/Lot.lean). General in the three public files (in the goals' scope).
Two theorems are decided by Lean's kernel, at a written list: a closed fact and its control; the
rest is a joining of laws. Of its eleven imports nine are files of the seal; two are the lookups'
PlanOkGives.lean and MemberSite.lean (both in Johnson/Desc/ProofFile/Honest/K3/Law/; beneath these
two lie the lookups' files and the honest side's frame on which they stand).

What a site asks (`siteAt`), and who pays.
* the public record gives a place there, and the place's numbers give a shape: by the lookups'
  `theStated_plan` (Johnson/Desc/ProofFile/Honest/K3/Law/PlanOkGives.lean), from the member's test
  on the plan, which the head holds (`IM.plan_flat`), and `IM.k3_of` (at every link both lookups are
  the kind's own block at the driver's address, alone);
* the table of places has such a place; at the digits it has just one place of the smallness test's
  kind in that link, with just one round: in scope the table of stretches is the written one
  (`cuts_at`, by `H2K5.Row.cuts_made` and `proof_plans_in_scope`), its places are the written 282
  (`spots_written`), and at these the kernel decides (`spots_fit`).

Main names.
* `cuts_at`, `spots_at`: under the head the table of stretches and the chain's places are the
  written ones. `reqShape_at`: so is the first chain's shape of the request.
* `piece_at`: under the head the driver's piece is the kind's own, at both sorts.
* `spots_fit`: the closed fact: `spotsFitB` accepts at each link below 25. `spots_miss`: a control:
  at link 25 the same test refuses.
* `rng_at`: for l < 25: `rngIn` answers at link l, at the public part's own table of places.
* `site_made_at`: for l < 25 and both sorts d: there is a site s in `lookSites Zp` with s.link = l
  and s.digits = d.

Limits. UNDER THE HYPOTHESIS: six of the eight theorems take h : `P5J.AtMgA OnBytes.secondHashFunction …`. That
this hypothesis can be met is shown only at the hash OnBytes.secondHashFunction and at two named sets of public
files (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean; `headMember_zGap`,
AtFullSide/Top/HeadMemberAtGap.lean); by the first file's own words the example's weights are
synthetic. THE PREMISE ASKS MORE THAN THE PROOFS USE: of h they use the fields scope, reads and laid
alone, straight or through `AtMg.pins` (Johnson/P5T/FenceAtMg.lean), whose proof uses scope and
laid. `site_made_at` pins the site's link and which of the two lookups it is (s.link, s.digits) and
nothing else: every other field of the site is under "there is", tied by membership in `lookSites
Zp` alone. That the list of addresses has no doubles is not shown. One control, at one link, 25; no
control bends a place at a link below 25. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanOkGives
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.AtFull.Desc.SpotsWritten
import Johnson.Desc.First.Att.Row.K5FrontOne
import Johnson.Goal.Numbers.MadeInScope
import Johnson.P5T.FenceAtMg
import Johnson.P5T.WrittenAtScope
import Johnson.P5J.MgAtAll
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName Place)
open VerifiableInference.Desc.K3 (pieceAt isHead)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (pinnedAt_of_row)
open VerifiableInference.PlanWritten.Joined (proof_plans_in_scope)
open ProofFile (spotsOf Spot)
open ProofFile.Honest.K3 (Site lookSites siteAt baseIn rngIn pieceAt_inj)
open ProofFile.Honest.K3.Law (site_facts theStated_plan)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten spots_written)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 The table of places, under the head -/

/-- Under the head the table of stretches is the written one. -/
theorem cuts_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Zp.cuts = cutWritten := by
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨hm, -⟩ := h.toAtMg.pins
  exact H2K5.Row.cuts_made hZ (proof_plans_in_scope h.scope hZ
    (pinnedAt_of_row (by rw [hm, Bool.or_true])))

/-- So the chain's places are the written 282. -/
theorem spots_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (spotsOf Zp.cuts).getD [] = spotsWritten := by
  rw [cuts_at h, spots_written]
  rfl

/-- Under the head the first chain's shape of the request is the written one. -/
theorem reqShape_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Zp.first.shape = shapeFull := by
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨hm, -⟩ := h.toAtMg.pins
  obtain ⟨-, a, -⟩ := P5T.written_at_in_scope h.scope hZ
    (pinnedAt_of_row (by rw [hm, Bool.or_true])) h.laid.laidPOf
  exact a

/-- Under the head the driver's piece is the kind's own. -/
theorem piece_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (d : Bool) :
    pieceAt Zp.p.X l d = IM.k3Ix l d + 1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  rw [O.W] at k4 kN
  unfold pieceAt isHead
  rw [k4, kN]
  by_cases e24 : l = 24
  · rw [e24]
    cases d <;> rfl
  · cases d <;> simp [IM.k3Ix, e24]

/-- The test at the written places: link l has both lookups' places, and just one place of the
smallness test's kind, with just one round. -/
def spotsFitB (l : Nat) : Bool :=
  [false, true].all fun d =>
    (baseIn spotsWritten (IM.k3Place l d)).isSome && (!d || (rngIn spotsWritten l).isSome)

/-- **The closed fact**: the test accepts at each link below 25. -/
theorem spots_fit : ((List.range 25).all spotsFitB) = true := by decide +kernel

/-- A control: there is no link 25. -/
theorem spots_miss : spotsFitB 25 = false := by decide +kernel

/-- Under the head, at every link: the table of places has just one place of the smallness test's
kind there, with just one round. -/
theorem rng_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true := by
  rw [spots_at h]
  have hf : spotsFitB l = true := List.all_eq_true.1 spots_fit l (List.mem_range.2 hl)
  have hf' := List.all_eq_true.1 hf true (by simp)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hf'
  exact hf'.2.resolve_left (by simp)

/-! ## 2 A site at each address -/

/-- **A SITE IS MADE AT EACH OF THE FIFTY ADDRESSES.** -/
theorem site_made_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) : ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', eL, eb, hk, la⟩ := IM.k3_of h.scope h.reads O l hl d
  have hb : b.planOk = true :=
    IM.plan_flat O h.laid.planOk b (List.mem_of_getElem? (IM.hear_at_flat eL eb))
  rw [IM.alone_planOk la] at hb
  rw [O.W] at hk
  obtain ⟨i, d', p, hS, a1, a2, a3, a4, -⟩ := theStated_plan _ _ _ _ _ _ b' hk hb
  obtain rfl : l = i := Option.some.inj a1
  have hpc := piece_at h l d
  obtain rfl : d = d' := pieceAt_inj _ _ _ _ (hpc.trans a2)
  -- the table of places
  have hf : spotsFitB l = true := List.all_eq_true.1 spots_fit l (List.mem_range.2 hl)
  have hf' := List.all_eq_true.1 hf d (by cases d <;> simp)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hf'
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hf'.1
  -- the address
  have hpl : (⟨1, some l, pieceAt Zp.p.X l d, .K3⟩ : Place) = IM.k3Place l d := by rw [hpc]
  have hx : (l, d, (⟨1, some l, pieceAt Zp.p.X l d, .K3⟩ : Place)) ∈ K3Lot.addresses Zp := by
    unfold K3Lot.addresses
    refine List.mem_flatMap.2 ⟨l, List.mem_range.2 ?_, List.mem_map.2 ⟨d, by cases d <;> simp, rfl⟩⟩
    rw [reqShape_at h]
    exact hl
  have key : ∃ s, siteAt Zp.p.X ((spotsOf Zp.cuts).getD [])
      (l, d, (⟨1, some l, pieceAt Zp.p.X l d, .K3⟩ : Place)) = some s := by
    rw [spots_at h, hpl]
    unfold siteAt
    simp only [a3, a4, hn, Option.bind_some]
    cases d with
    | false => exact ⟨_, rfl⟩
    | true =>
      obtain ⟨rr, hr⟩ := Option.isSome_iff_exists.1 (hf'.2.resolve_left (by simp))
      simp only [hr, if_true, Option.map_some]
      exact ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := key
  obtain ⟨-, -, f3, f4, -⟩ := site_facts _ _ _ s hs
  exact ⟨s, List.mem_filterMap.2 ⟨_, hx, hs⟩, f3, f4⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.cuts_at
#print axioms Johnson.AtFull.Shape.spots_at
#print axioms Johnson.AtFull.Shape.reqShape_at
#print axioms Johnson.AtFull.Shape.piece_at
#print axioms Johnson.AtFull.Shape.spots_fit
#print axioms Johnson.AtFull.Shape.spots_miss
#print axioms Johnson.AtFull.Shape.rng_at
#print axioms Johnson.AtFull.Shape.site_made_at
