-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.IMR.K2Seat
import Johnson.IMR.FrameSeat
import Johnson.IMR.PlacesScope
import Johnson.Top.H0.K2Caller.PAtSeated
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.P5J.MgAtAll
/-
Johnson/P1L20R/Stands24AtAll.lean. Code switching (the kind K2) on the proof file's first chain:
THE NUMBERS OF THE PLACE WHOSE SWITCH OPENS GROUP 25 (`ProofFile.pAtK2 Zp 24`, Johnson/Desc/ProofFile/CarryAt.lean) DO NOT
STAND IN THE OUTPUT HEAD's DRESS: UNDER THE HEAD OF THE COMPOSED MEANING's CONSTANT ALONE. No entry test on written
values and no named test on the list of places is spent. Statements and proofs; nothing is evaluated.
THE ROAD. Suppose the first place of the kind that opens group 25 stood in the head's dress. Its dress goes by the head
of its first row's name (`IM.spot_head`, Johnson/IMR/K2Seat.lean): that head is "H", which does not stand behind the
segments: so the place bears a segment's number l. The group that it opens is l (`P1K2.numsAt_grp`,
Johnson/Top/H0/Tw/K2C/GroupAtNums.lean): l = 25. But the IOP as written in Lean is made only where it "lacks nothing"
(`ProofFile.lackingAt`, Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean), and that test asks, for every segment's number that a place bears,
the batching as a function at that number, which is looked up in a list with one entry for each of the plan's
segments: so l is below their number, 25 in scope (`IM.subs_len`, Johnson/IMR/PlacesScope.lean).
  `batch_made`: what `ProofFile.baseOf` lays as that list.
  `link_below`: GENERAL: where nothing is lacking, a place's segment's number is below the number of segments.
  `spot_mem`: a member of the kind's list of places with numbers is a place of the plan's list, of the kind K2.
  `stands24_open`: the statement at an opening of the IOP as written.
  `P1L20.stands24_atAll`: the statement under the head: `P1L20.FramePub.stands24`, to the letter.
What it is not. It does not say that there is such a place (where there is none, the numbers are the dead ones, which
stand in a segment's dress), nor that the dress is the finish's. It gives nothing of the named test `spotsFitB`
(Johnson/Top/H0/K2Caller/PAtSeated.lean). NO EXAMPLE BY A THEOREM OF THIS FILE of the head. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.First.K2 (P2 At)

/-- What `baseOf` lays as the list of the places at which the driver asks for the batching as a function: one entry for
each of the plan's segments. -/
theorem batch_made {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (h : ProofFile.baseOf Z T = .ok B) :
    B.batchAt = (ProofFile.subsOf Z).zipIdx.map fun x =>
      (x.2, (⟨1, some x.2, (kindsBeforeBatching x.1 (x.2 == 0)).length + 1, KindName.K9⟩ : Place)) := by
  unfold ProofFile.baseOf at h
  obtain ⟨ps, _, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨sh, _, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨G, _, h⟩ := ProofFile.Law.exBind_ok h
  cases h
  rfl

/-- **Where nothing is lacking, a place's segment's number is below the number of the plan's segments.** -/
theorem link_below {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (hB : ProofFile.baseOf Z T = .ok B)
    (hw : ProofFile.lackingAt T (ProofFile.partsAt T B) = []) {sp : ProofFile.Spot} (hsp : sp ∈ B.spots) {l : ℕ}
    (hl : sp.place.link = some l) : l < (ProofFile.subsOf Z).length := by
  have hpl : sp ∈ (ProofFile.partsAt T B).places.map (·.1) := by
    rw [IM.places_spots]
    exact hsp
  obtain ⟨⟨sp', y⟩, hm, rfl⟩ := List.mem_map.1 hpl
  unfold ProofFile.lackingAt at hw
  dsimp only at hw
  simp only [List.append_eq_nil_iff] at hw
  obtain ⟨⟨⟨-, hfr⟩, -⟩, -⟩ := hw
  have hmem : l ∈ ((ProofFile.partsAt T B).places.filterMap fun x => x.1.place.link).eraseDups :=
    List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨(sp', y), hm, hl⟩)
  have h1 := List.flatMap_eq_nil_iff.1 hfr l hmem
  simp only [List.append_eq_nil_iff] at h1
  obtain ⟨⟨⟨-, hroad⟩, -⟩, -⟩ := h1
  have hr := IM.ite_nil hroad
  have hr' : l ∈ (ProofFile.partsAt T B).onRoad := List.contains_iff_mem.1 hr
  have hr'' : l ∈ B.batchAt.filterMap fun x =>
      if ((fun (a : Place) => (T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a) x.2).isSome
      then some x.1 else none := hr'
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr''
  have ex : x.1 = l := by
    split at e
    · exact Option.some.inj e
    · cases e
  rw [batch_made hB] at hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  have := (List.mem_zipIdx hz).2.1
  have e2 : z.2 = l := ex
  omega

/-- A member of the kind's list of places with numbers is a place of the plan's list, of the kind K2. -/
theorem spot_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {y : ProofFile.Spot × P2} (hy : y ∈ P1K2.pureSpots Z G)
    {sps : List ProofFile.Spot} (hs : ProofFile.spotsOf Z.cuts = some sps) :
    y.1 ∈ sps ∧ y.1.place.kind = KindName.K2 := by
  unfold P1K2.pureSpots at hy
  rw [hs] at hy
  have hm : y ∈ P1K2.p2All Z G sps := hy
  unfold P1K2.p2All at hm
  split at hm
  · cases hm
  · obtain ⟨sp', hsp', e⟩ := List.mem_filterMap.1 hm
    obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hsp'
    exact ⟨h1, by simpa using h2⟩

/-- **The statement at an opening of the IOP as written in Lean.** -/
theorem stands24_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : (ProofFile.pAtK2 Z 24).stands ≠ .head := by
  unfold ProofFile.pAtK2 ProofFile.pAtK2?
  cases hf : (ProofFile.k2SpotsAt Z).find? (fun x => x.2.grp == 24 + 1) with
  | none =>
    intro h
    cases h
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hg : y.2.grp = 25 := by simpa using List.find?_some hf
    intro h
    have h' : y.2.stands = .head := h
    unfold ProofFile.k2SpotsAt at hy
    rw [O.blank] at hy
    have hy' : y ∈ P1K2.pureSpots Z Bs.G₀ := hy
    have hs := (IM.base_made O.made).1
    obtain ⟨hmem, hk⟩ := spot_mem hy' hs
    obtain ⟨Q, n, _, hn, e⟩ := VerifiableInference.Desc.First.K2Caller.spot_is hy'
    have hst : P1K2.standsOf y.1 = At.head := by
      rw [e] at h'
      exact h'
    have hgn : n.grp = 25 := by
      rw [e] at hg
      exact hg
    have hs' := hs
    unfold ProofFile.spotsOf at hs'
    obtain ⟨hd, m, ⟨-, -, hl, est⟩ | ⟨h9, -⟩⟩ := IM.spot_head _ _ _ _ _ hs' y.1 hmem
    · rw [hst] at est
      by_cases hF : (hd == "F") = true
      · rw [if_pos hF] at est
        cases est
      · rw [if_neg hF] at est
        by_cases hH : (hd == "H") = true
        · have eH : hd = "H" := by simpa using hH
          have hnb : ProofFile.behindLinks hd = false := by
            rw [eH]
            decide
          cases hlk : y.1.place.link with
          | none =>
            rw [hl.1 hlk] at hnb
            cases hnb
          | some l =>
            have h25 := P1K2.numsAt_grp hn
            rw [hlk, hgn] at h25
            have hlt := link_below O.made O.whole hmem hlk
            rw [IM.subs_len hS hR O] at hlt
            have : 25 = l := h25
            omega
        · rw [if_neg hH] at est
          cases est
    · rw [hk] at h9
      cases h9

end H2K12

namespace P1L20

/-- **The numbers at the last switch do not stand in the output head's dress: under the head alone.** -/
theorem stands24_atAll {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (ProofFile.pAtK2 Zp 24).stands ≠ .head := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact H2K12.stands24_open h.scope h.reads O

end P1L20

#print axioms H2K12.batch_made
#print axioms H2K12.link_below
#print axioms H2K12.spot_mem
#print axioms H2K12.stands24_open
#print axioms P1L20.stands24_atAll
