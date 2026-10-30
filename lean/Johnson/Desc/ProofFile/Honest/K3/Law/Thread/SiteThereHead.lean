-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SiteThereHead.lean: under the library's hypothesis
`P5J.AtMgA` a site is there: at each of the 25 links, on the calls outright and on the digits under
one public test `hr` besides, the list `lookSites Zp` (Honest/K3/Lot.lean) holds a site with that
link and that sort; its place is the library's written one and stands in the written list of places.
Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the library's written place of link l's lookup is
`IM.k3Place l d` (Johnson/IMR/K3Seat.lean); the written list of places is `P5J.At.ps`
(Johnson/P5J/LettersAt.lean).

Why. Every theorem of this folder on a site takes "s ∈ lookSites Z" as a hypothesis, and many take
"the site's place stands in the written list". Neither was shown under `P5J.AtMgA`.

What is shown.
  `sub_at_link`: the link's sort, and that the driver asks for a lookup at the lookup's index there.
  `lot_spot_head`: the lot's own sub-protocol at the written place; it passes its test on the plan;
    the table of places has that place.
  `baseIn_of_mem`: a place of the table has rounds in front, by the table.
  `site_there_head`: the site. On the calls: conditional on `P5J.AtMgA` alone. On the digits: also
    on the one public test `hr`.
  `site_calls_head`: the same on the calls, without `hr`.
The last conjunct is the hypothesis `hp` of `lot_at_site` and the field there of `SiteRest'`
(Honest/K3/Law/Thread/LotAtSite.lean): so on the calls both hold under `P5J.AtMgA` with no public
test left.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). The first two theorems take
    instead the goals' scope, the files' reading and the description's return (`lot_spot_head`: and
    its test on the plan).
  `hr`: at the digits: `rngIn` (Honest/K3/Lot.lean) returns a number at the link: the table of
    places has just one place of the kind K8 in that link, and its rows take one round. A test with
    code on the public part. That a place of the kind K8 is there could be shown as here; that it is
    the only one, and that its rows take one round, follows from
    `rng_at` (Johnson/AtFull/Shape/SitesAtHead.lean), which
    states `hr` under `P5J.AtMgA` at every link below 25.
    `rng_head_paid` (Honest/K3/Law/Thread/RngWrittenHolds.lean) also shows `hr` under
    `P5J.AtMgA` at every link below 25.
  `hl`: the link's number is below 25. `hS`, `hR`, `O`: (in the first two theorems) the goals'
    scope, the files' reading, the description's return. `e`: (in `baseIn_of_mem`) the spot's place
    is a.
  `h`: (in `baseIn_of_mem`) sp ∈ ps.

How the proof goes. The proofs call the library's `IM.chain_hear_alone`
(Johnson/IMR/LaidFirst.lean), `IM.base_made` (Johnson/IMR/PureJoin.lean), `IM.lot_of_kind`,
`IM.blocks_mem` (Johnson/IMR/LotKinds.lean), `IM.plan_alone` (Johnson/IMR/PlanAt.lean),
`IM.subs_at`, `IM.subs_att`, `IM.subs_head` (Johnson/IMR/Subs.lean), `k03_pieceAt`
(Johnson/P5J/K03RidesAt.lean), `k03_pieceAt_dig` (Johnson/P5J/K03RidesDigAt.lean) and
`places_are_k3` (Johnson/Desc/Sound/MgAt/K3Open.lean); and, of the files under Honest/K3/,
`theStated_plan` (Honest/K3/Law/PlanOkGives.lean), `theStated_place` (Honest/K3/Law/LotMember.lean),
`address_form`, `site_facts` (Honest/K3/Law/MemberSite.lean) and `pieceAt_inj`
(Honest/K3/LotLaw.lean).

Users. `site_there_head` is called, among others, in Honest/K3/Law/Thread/QuietAtLink.lean and
Honest/K3/Law/Thread/RngHead.lean; `site_calls_head`, among others, in
Honest/K3/Law/Thread/AtLink.lean, which also calls `lot_spot_head`. Honest/K3/Good/MarksHead.lean
and Honest/K3/Law/Thread/LaysNextLight.lean import this file too.

Limits. At the full size alone: that limit comes with `P5J.AtMgA`. No instance of these hypotheses
is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ThereOf
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanOkGives
import Johnson.P5J.K03RidesAt
import Johnson.P5J.K03RidesDigAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching ModelPart)
open VerifiableInference.Desc.K3 (pieceAt)
open VerifiableInference.Desc.Sound.MgAt (places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 Under the description's return, in scope -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The link's sort, and that the driver asks for a lookup at the lookup's index there. Conditional
on the scope, the files' reading and the description's return. -/
theorem sub_at_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ sub, (ProofFile.subsOf Z)[l]? = some sub ∧
      (kindsBeforeBatching sub (l == 0))[IM.k3Ix l d]? = some KindName.K3 ∧
      (2 ≤ IM.k3Ix l d + 1 ∧ IM.k3Ix l d + 1 ≤ 9) := by
  by_cases h24 : l = 24
  · subst h24
    refine ⟨.head, IM.subs_head hS hR O.pub O.blank, ?_, by cases d <;> decide⟩
    unfold kindsBeforeBatching
    cases d <;> rfl
  · have hix : IM.k3Ix l d = if d then 6 else 1 := by
      show (if d then 6 else 1) + (if l = 24 then 1 else 0) = _
      rw [if_neg h24]
      rfl
    rw [hix]
    by_cases he : l % 2 = 0
    · have ej : 2 * (l / 2) = l := by omega
      have hsub := IM.subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [ej] at hsub
      refine ⟨.layers, hsub, ?_, by cases d <;> decide⟩
      unfold kindsBeforeBatching
      cases d <;> rfl
    · have ej : 2 * (l / 2) + 1 = l := by omega
      have hsub := IM.subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [ej] at hsub
      refine ⟨.attention, hsub, ?_, by cases d <;> decide⟩
      unfold kindsBeforeBatching
      cases d <;> rfl

/-- **The lot's own sub-protocol at the written place; it passes its test on the plan; the table of
places has that place.** Conditional on the scope, the files' reading, the description's return and
its test on the plan. -/
theorem lot_spot_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true) (l : Nat)
    (hl : l < 25) (d : Bool) :
    ∃ b' ∈ K3Lot.hear Z, b'.place = IM.k3Place l d ∧ b'.planOk = true ∧
      ∃ sp ∈ Bs.spots, sp.place = IM.k3Place l d := by
  obtain ⟨sub, h1, h2, h3⟩ := sub_at_link hS hR O l hl d
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain l sub h1 (IM.k3Ix l d) .K3 h2 (by decide)
      (by decide) h3
  obtain rfl : L = K3Lot.lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ K3Lot.hear Z := by
    rcases IM.blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  exact ⟨b', hb'', ep, IM.plan_alone O hp e1 e2 hla, sp, hsp, es⟩

end

/-- A place of the table has rounds in front, by the table. -/
theorem baseIn_of_mem (ps : List Spot) (a : Place) (sp : Spot) (h : sp ∈ ps) (e : sp.place = a) :
    ∃ n, baseIn ps a = some n := by
  unfold baseIn
  rw [if_pos (List.any_eq_true.2 ⟨sp, h, by rw [e]; exact beq_self_eq_true a⟩)]
  exact ⟨_, rfl⟩

/-! ## 2 Under `P5J.AtMgA` -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under `P5J.AtMgA` a site is there**, at every link below 25 and either sort; at the library's
written place, which stands in the written list. Conditional on `P5J.AtMgA`; at the digits also on
`hr`: `rngIn` returns a number at the link. No instance of these hypotheses is exhibited in this
file. -/
theorem site_there_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) (hr : d = true → (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place ∈ P5J.At.ps := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', hb', ep, hpk, sp, hsp, es⟩ :=
    lot_spot_head h.scope h.reads O h.laid.planOk l hl d
  have eps : (spotsOf Zp.cuts).getD [] = Bs.spots := by
    rw [(IM.base_made O.made).1]
    rfl
  unfold K3Lot.hear at hb'
  obtain ⟨y, hy, hst⟩ := List.mem_filterMap.1 hb'
  have hpy : y.2.2 = IM.k3Place l d := (theStated_place _ _ _ _ _ _ b' hst).symm.trans ep
  obtain ⟨y1, y2⟩ := address_form Zp y hy
  have e1 : y.1 = l := by
    rw [hpy] at y1
    exact (Option.some.inj y1).symm
  have hpc : (IM.k3Place l d).piece = pieceAt Zp.p.X l d := by
    cases d with
    | false => exact P5J.k03_pieceAt h.toAtMg l
    | true => exact P5J.k03_pieceAt_dig h.toAtMg l
  have e2 : y.2.1 = d := by
    rw [hpy, e1] at y2
    exact pieceAt_inj _ _ _ _ (y2.symm.trans hpc)
  obtain ⟨i, d', p, hS, k1, k2, k3, k4, _⟩ := theStated_plan _ _ _ _ _ _ b' hst hpk
  obtain rfl : y.1 = i := Option.some.inj (y1.symm.trans k1)
  obtain rfl : y.2.1 = d' := pieceAt_inj _ _ _ _ (y2.symm.trans k2)
  obtain ⟨n, hn⟩ := baseIn_of_mem Bs.spots y.2.2 sp hsp (es.trans hpy.symm)
  have hsite : ∃ s, siteAt Zp.p.X Bs.spots y = some s := by
    unfold siteAt
    simp only [k3, k4, hn, Option.bind_some]
    split
    · rename_i hd
      have hr' := hr (e2.symm.trans hd)
      rw [eps, ← e1] at hr'
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hr'
      rw [hq]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := hsite
  obtain ⟨_, _, f3, f4, f5, _, _, _⟩ := site_facts _ _ y s hs
  refine ⟨s, ?_, f3.trans e1, f4.trans e2, f5.trans hpy, ?_⟩
  · unfold lookSites
    exact List.mem_filterMap.2 ⟨y, hy, by rw [eps]; exact hs⟩
  · rw [f5, hpy]
    exact List.mem_of_getElem? (places_are_k3 hl d)

/-- **On the calls: conditional on `P5J.AtMgA` alone.** No instance of these hypotheses is exhibited
in this file. -/
theorem site_calls_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = false ∧ s.at_.place = IM.k3Place l false ∧
      s.at_.place ∈ P5J.At.ps :=
  site_there_head h l hl false fun e => nomatch e

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.sub_at_link
#print axioms ProofFile.Honest.K3.Law.AtThr.lot_spot_head
#print axioms ProofFile.Honest.K3.Law.AtThr.baseIn_of_mem
#print axioms ProofFile.Honest.K3.Law.AtThr.site_there_head
#print axioms ProofFile.Honest.K3.Law.AtThr.site_calls_head
