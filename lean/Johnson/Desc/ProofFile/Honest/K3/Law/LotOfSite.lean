-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LotOfSite.lean: where the description returns, the lookups' lot
has a sub-protocol at every site's place. At every size: neither the library's hypothesis
`P5J.AtMgA` nor the goals' scope is assumed. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the table of places is the list `spotsOf Z.cuts`
(Johnson/Desc/ProofFile/Places.lean). The batching as a function is the field batch of a lot
(`ProofFile.Lot`, Johnson/Desc/ProofFile/LotCore.lean). The description's list of lots is `onlineFirstChainBlockTables Z`
(Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean).

What is shown.
  `lot_of_site`, the main theorem: a sub-protocol of the lookups' lot stands at the site's place.
  `spot_of_site`: a site's place is of the kind K3 and stands in the table of places.
  `batch_kind`: a lot of the description's list supplies the batching as a function at places of the
    kind K9 alone.
  `mapM_each`: where `List.mapM` returns on a list, the function has returned at each entry.

Hypotheses that remain, in `lot_of_site`.
  `O`: the description returns (`IM.Open`).
  `hs`: s is a site of the public part Z.
In `batch_kind`: `hL`: L is a lot of the description's list; `hmk`: it supplies the batching as a
function at the place a.

How the proof goes. A site is made only where the table of places has its place. Where the
description returns, every place of the table has its sub-protocol. By `places_of_lot`
(Johnson/Desc/ProofFile/Law/BaseOfLot.lean) that sub-protocol is a lot's own, at that place, or the
batching as a function, which a place of the kind K3 does not have. By `IM.lot_of_kind`
(Johnson/IMR/LotKinds.lean) the lot is the lookups'.

Users. Many theorems of this folder assume "a sub-protocol of the lookups' lot at the site's place".
Honest/K3/Law/Thread/LotAtSite.lean shows it at the full size alone. Honest/K3/Law/LotKind.lean
calls `spot_of_site`; Honest/K3/Law/Thread/LinkLtHead.lean calls `lot_of_site`.

Limits. The statements are on public data alone. No instance of these hypotheses is exhibited in
this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.ProofFile.Law.BaseOfLot
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)

local notation "FS" => VerifiableInference.Desc.First.S

/-- A lot of the description's list supplies the batching as a function at places of the kind K9
alone. -/
theorem batch_kind (Z : Pub) (G : Ground) {L : Lot} (hL : L ∈ onlineFirstChainBlockTables Z) {a : Place}
    {mk : Gatherer → Block FS ProofFile.Cl} (hmk : L.batch G a = some mk) : a.kind = KindName.K9 := by
  unfold onlineFirstChainBlockTables p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  iterate 7 exact nomatch hmk
  · unfold k9Ninth at hmk
    dsimp only at hmk
    split at hmk
    · assumption
    · cases hmk
  iterate 7 exact nomatch hmk

/-- Where `List.mapM` returns on a list, the function has returned at each entry. -/
theorem mapM_each {α β : Type} (f : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → ∀ x ∈ l, ∃ b, f x = .ok b
  | [], _, _, x, hx => nomatch hx
  | a :: l, r, h, x, hx => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e =>
      rw [ha] at h
      exact nomatch h
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e =>
        rw [hl] at h
        exact nomatch h
      | ok bs =>
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨b, ha⟩
        · exact mapM_each f l bs hl x hx'

/-- A site's place stands in the table of places. -/
theorem spot_of_site (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) :
    s.at_.place.kind = KindName.K3 ∧ ∃ sp ∈ (spotsOf Z.cuts).getD [], sp.place = s.at_.place := by
  unfold lookSites at hs
  obtain ⟨y, hy, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨_, _, _, _, f5, _, _, _⟩ := site_facts _ _ y s hsy
  refine ⟨by rw [f5]; exact (k3_alone Z y hy).1, ?_⟩
  unfold siteAt at hsy
  obtain ⟨p, _, h1⟩ := Option.bind_eq_some_iff.1 hsy
  obtain ⟨h, _, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨n, hn, _⟩ := Option.bind_eq_some_iff.1 h2
  unfold baseIn at hn
  split at hn
  · rename_i hany
    obtain ⟨sp, hsp, e⟩ := List.any_eq_true.1 hany
    exact ⟨sp, hsp, by rw [f5]; exact eq_of_beq e⟩
  · exact nomatch hn

/-- **Where the description returns, the lookups' lot has a sub-protocol at every site's place.**
Conditional on the description's return and on s being a site of Z. No instance of these hypotheses
is exhibited in this file. -/
theorem lot_of_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) : ∃ lot ∈ (K3Lot.lot Z).blocks Bs.G₀, lot.place = s.at_.place := by
  obtain ⟨hk, sp, hsp, esp⟩ := spot_of_site Z s hs
  obtain ⟨hspots, _, _, hall⟩ := IM.base_made O.made
  rw [hspots] at hsp
  have hsp' : sp ∈ Bs.spots := hsp
  have hx : ∃ x ∈ (partsAt (pureSeat o Z) Bs).places, x.1 = sp := by
    unfold partsAt
    dsimp only
    exact ⟨_, List.mem_map.2 ⟨sp, hsp', rfl⟩, rfl⟩
  obtain ⟨x, hx, ex⟩ := hx
  obtain ⟨b, hb⟩ := mapM_each _ _ _ O.places x hx
  rcases (ProofFile.Law.places_of_lot _ _ x hx b hb).2 with ⟨L, hL, mk, hmk⟩ | ⟨y, hy, b₁, hb₁, hp, _, _⟩
  · have h9 := batch_kind Z Bs.G₀ (show L ∈ onlineFirstChainBlockTables Z from hL) hmk
    rw [ex, esp, hk] at h9
    exact nomatch h9
  · rw [hall] at hy
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hy
    have hpl : b₁.place = s.at_.place := by rw [hp, ex, esp]
    obtain rfl : L = K3Lot.lot Z :=
      IM.lot_of_kind (show L ∈ onlineFirstChainBlockTables Z from hL) hb₁ (by rw [hpl, hk]; rfl)
    exact ⟨b₁, hb₁, hpl⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.batch_kind
#print axioms ProofFile.Honest.K3.Law.mapM_each
#print axioms ProofFile.Honest.K3.Law.spot_of_site
#print axioms ProofFile.Honest.K3.Law.lot_of_site
