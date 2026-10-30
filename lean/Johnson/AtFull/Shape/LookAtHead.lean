-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LookAtHead.lean: the lookups (the kind K3) at their seats in the proof file's
own first chain: at every SITE of the public part (`ProofFile.Honest.K3.lookSites`,
Johnson/Desc/ProofFile/Honest/K3/Lot.lean) the member is named by its number in the flat list, the
lot's own block at the site's place is found, and the lookups' own two laws on the chain's shape
hold there, in the frame's own form (`Carries`, `Returns`:
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean). Under the head `P5J.AtMgA`; a joining of laws;
nothing is evaluated.

Main names.
* `lookNo l d`: the member's number: 14 l + `IM.k3Ix l d` + 2.
* `site_place_at`: under the head a site's link is below 25 and its place is the driver's address
  `IM.k3Place s.link s.digits`.
* `look_member_at`: under the head, at a site s: with Bs what the maker's own `ProofFile.baseOf` returns:
  there are the lot's block (a member of `(K3Lot.lot Zp).blocks Bs.G₀` at the site's place) and the
  member b at number `lookNo s.link s.digits` of cF.blocksInOrder; b stands at the lot's block's place and
  passes its test on the plan.
* `look_calls_at`: at a site on the calls: for every filling of the cut's letters whose shape is the
  chain's and whose guards at that number are `callsG s.shape s.p.first`: `Carries`; and, under two
  tests with code on public data (the face's own; at a layers' link: the site's shape is the
  layout's), `Returns`.
* `look_digits_at`: at a site on the digits of a link that is not the head's, with used and claims
  the two numbers of the quiet step behind (tied by `quietAt Zp.p.X s.link true = some (quietDigits
  used claims)`): the same at `digitsG s.shape s.p.first used claims`; `Returns` under two tests
  with code on public data (the face's own; the plan's count behind).

How. `IM.k3_of` (Johnson/IMR/K3Seat.lean: at every link both lookups are the kind's own block at the
driver's address, alone), `IM.hear_at_flat`, `IM.flatIx_scope`, `plans_at`
(Johnson/AtFull/Shape/PlansAtHead.lean), `first_at` (StartAtHead.lean), `site_facts`
(Honest/K3/Law/MemberSite.lean), and the lookups' `carries_calls`, `carries_digits`,
`returns_calls`, `returns_digits` (Honest/K3/Law/Thread/).

Limits. AT A SITE: THAT A SITE IS MADE AT EACH OF THE FIFTY ADDRESSES IS NOT SHOWN HERE: so no count
of members follows from this file alone. (SitesAtHead.lean's site_made_at says that a site of the
link and flag is made at each address.) The head's own digits have no step. The tests on public data
and the equation on the quiet step are premises, paid nowhere here. TWO TESTS ARE HANDED ON WHOLE,
AS THE CALLEES' LAWS HAVE THEM, WITH DISJUNCTS THAT ARE DEAD UNDER THE STATEMENT's OWN PREMISES: at
the calls (s.digits = false) what is truly asked is "s.caller != .layers || sameShape …"; at the
digits below the head (s.digits = true, s.caller ≠ .head) the last disjunct alone (usedAt … == some
…). The premise on the quiet step is an equation between two functions: that only one pair of
numbers meets it is not said. `Carries` is the weak form (the frame's own). No state is shown at
which a guard returns. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesCalls
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesDigits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ReturnsLook
import Johnson.AtFull.Shape.StartAtHead
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName Place)
open VerifiableInference.Desc.K3 (quietAt quietDigits pieceAt isHead)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.ReqLit (shapeFull)
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites usedAt)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (callsG digitsG carries_calls carries_digits returns_calls
  returns_digits)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- The member's number in the flat list. -/
def lookNo (l : Nat) (d : Bool) : Nat := 14 * l + IM.k3Ix l d + 2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head a site's link is below 25 and its place is the driver's address. -/
theorem site_place_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) :
    s.link < 25 ∧ s.at_.place = IM.k3Place s.link s.digits ∧
      (s.link, s.digits, s.at_.place) ∈ K3Lot.addresses Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  rw [O.W] at k4 kN
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, hy, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨-, -, f3, f4, f5, -, -, -⟩ := site_facts _ _ y s hsy
  have hy0 := hy
  unfold K3Lot.addresses at hy
  obtain ⟨j, hj, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
  have f3' : s.link = j := f3
  have f4' : s.digits = e := f4
  have f5' : s.at_.place = ⟨1, some j, pieceAt Zp.p.X j e, .K3⟩ := f5
  subst f3' f4'
  have hl : s.link < 25 := by
    have h1 := List.mem_range.1 hj
    rw [(first_at h).2.1] at h1
    exact h1
  refine ⟨hl, ?_, ?_⟩
  · rw [f5']
    unfold pieceAt isHead
    rw [k4, kN]
    by_cases e24 : s.link = 24
    · rw [e24]
      cases s.digits <;> rfl
    · cases s.digits <;> simp [IM.k3Place, IM.k3Ix, e24]
  · rw [f5']
    exact hy0

/-- **The member at a site.** -/
theorem look_member_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) :
    ∃ (Bs : ProofFile.PureBase) (lot b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      lot ∈ (K3Lot.lot Zp).blocks Bs.G₀ ∧ lot.place = s.at_.place ∧
      cF.blocksInOrder[lookNo s.link s.digits]? = some b ∧ b.place = lot.place ∧ b.planOk = true := by
  obtain ⟨hl, hp, ha⟩ := site_place_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', eL, eb, hk, la⟩ := IM.k3_of h.scope h.reads O s.link hl s.digits
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : s.link ≤ 24) (IM.k3Ix s.link s.digits)] at q
  rw [O.W, ← hp] at hk
  have hpl : b'.place = s.at_.place := IM.theStated_place hk
  have hin : b' ∈ K3Lot.hear Zp := by
    unfold K3Lot.hear
    exact List.mem_filterMap.2 ⟨_, ha, hk⟩
  refine ⟨Bs, b', b, O.made, hin, hpl, q, ?_, plans_at h b (List.mem_of_getElem? q)⟩
  rw [IM.alone_place la, hpl, hp]

/-- **At a site on the calls.** -/
theorem look_calls_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = false) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (lookNo s.link false) = callsG s.shape s.p.first) :
    Carries cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (lookNo s.link false) ∧
      (s.at_.face.ok = true →
        (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true →
        Returns cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (lookNo s.link false)) := by
  obtain ⟨Bs', lot, b, hB, hin, hlp, q, hbp, hpk⟩ := look_member_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (hB.symm.trans O.made)
  rw [hd] at q
  have hm : ∀ blk, cF.blocksInOrder[lookNo s.link false]? = some blk →
      blk ∈ cF.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true := by
    intro blk hk
    obtain rfl : b = blk := Option.some.inj (q.symm.trans hk)
    exact ⟨List.mem_of_getElem? q, hbp, hpk⟩
  exact ⟨carries_calls _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot hin hlp cF.blocksInOrder ft _ hm g vals hg,
    fun hok hT2 => returns_calls _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot hin hlp hok hT2 cF.blocksInOrder ft _
      hm g vals hg⟩

/-- **At a site on the digits of a link that is not the head's.** -/
theorem look_digits_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (hc : s.caller ≠ .head) (used claims : Nat)
    (hq : quietAt Zp.p.X s.link true = some (quietDigits used claims)) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (lookNo s.link true) = digitsG s.shape s.p.first used claims) :
    Carries cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (lookNo s.link true) ∧
      (s.at_.face.ok = true →
        (!s.digits || s.caller == .head ||
          usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true →
        Returns cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (lookNo s.link true)) := by
  obtain ⟨Bs', lot, b, hB, hin, hlp, q, hbp, hpk⟩ := look_member_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (hB.symm.trans O.made)
  rw [hd] at q
  have hm : ∀ blk, cF.blocksInOrder[lookNo s.link true]? = some blk →
      blk ∈ cF.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true := by
    intro blk hk
    obtain rfl : b = blk := Option.some.inj (q.symm.trans hk)
    exact ⟨List.mem_of_getElem? q, hbp, hpk⟩
  exact ⟨carries_digits _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot hin hlp used claims hq cF.blocksInOrder ft _ hm
      g vals hg,
    fun hok hT3 => returns_digits _ _ _ _ _ _ _ _ _ _ _ O s hs hd hc lot hin hlp hok hT3 used
      claims cF.blocksInOrder ft _ hm g vals hg⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.site_place_at
#print axioms Johnson.AtFull.Shape.look_member_at
#print axioms Johnson.AtFull.Shape.look_calls_at
#print axioms Johnson.AtFull.Shape.look_digits_at
#print axioms Johnson.AtFull.Shape.lookNo
