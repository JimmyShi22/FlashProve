-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SitesAtFlat.lean: THE PILE's SITES ON THE FIRST CHAIN OF THE PROOF
FILE's IOP AS WRITTEN IN LEAN: THE LIST, AS A TERM; AND THE MERGING SUB-PROTOCOLS BY NUMBER:
`LayersSite` AND `HeadSite` (Johnson/Desc/K13/Honest/ClaimsIsAt.lean) THERE; and that each returns
only states with failed = none. Definitions with code, and statements with their proofs.

THE LIBRARY HAS THE PLACES. `IM.k4_of`, `IM.k4_yes` (Johnson/IMR/K4Seat.lean): at each of the twelve
layers' segments the third hearing sub-protocol decides just where the layers' own sub-protocol at
the verifier's state (`blockAtS`) does, with failed = none behind it and the reply as it was.
`IM.k11_of` (IMR/K11Seat.lean), `IM.yes_alone` (IMR/SeatForm.lean), `K11.blkAt_decide`
(Johnson/Top/H0/MergeLaw/LotIs.lean): the like for the head's ninth hearing sub-protocol and
`headMergeDecide`. `IM.hear_at_flat` (IMR/FlatIx.lean), `IM.flatIx_scope` (IMR/FlatScope.lean):
their numbers in the chain's list. `IM.Open.W` (IMR/SeatOpen.lean): the blank ground's public data
are Z's own: SO THE LAYOUT OF THE COMMITTED TABLE OF THE WEIGHTS IS ONE AT ALL SITES:
Z.p.X.layers.wsLay. These eight are called. Kin: `K11.K11_sits` (Johnson/K11R/Sits.lean): number
346, from the IOP's own value.
Main names:
  `nclAt Z l`: a segment's public number of claims on the weights, off the built plan. `sigAt c Z
    l`: **the number, on the chain, of the batching round of segment l's merge**: at the head
    `roundsAhead c.blocksInOrder 346`; at l = 2 g `roundsAhead c.blocksInOrder (28 g + 4)` + `layersSigmaAt` at the
    public data for the layers and the plan of group g.
  `layerSite c Z g`, `headSite c Z`, `sitesAt c Z`: **the sites** (`PileSite`,
    Johnson/Desc/K13/Honest/PileInduction.lean): the twelve groups of layers in their order: j = 28
    g + 4, c = 28 g + 14, `leftLay`; then the head: j = 346, c = 352, `leftHead`. All of public data
    and the chain. `mem_sitesAt`, `sitesAt_order`.
  `layersSite_at_flat`: **In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the
    opening of the proof file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank
    ground's holder, the first chain): for each g < 12: number 28 g + 4**: there is K4's data x, of
    the group g, at Z's public data for the layers and the plan of group g, such that: every
    decision of that number has failed = none behind it; and `LayersSite` holds there at p := x's
    data, at the list's own site, at the one layout.
  `headSite_at_flat`: **number 346**: every decision of it has failed = none behind it; and
    `HeadSite` holds there at P := `K11.parOf Z Bs.G₀`, at the list's own site, at the one layout.

What is not claimed. What `roundsAhead` is at these numbers, as a numeral. The other premises of
`ClaimsIs` at a site and of the induction. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.ClaimsIsAt
import Johnson.Desc.K13.Honest.PileInduction
import Johnson.IMR.K4Seat
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope
import Johnson.Top.H0.MergeLaw.LotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.K13.Honest (MergeSite PileSite LayersSite HeadSite roundsAhead
  layersSigmaAt)
open Johnson.Desc.First.Walk (leftLay)
open ProofFile (Cl)

/-! ## The sites -/

/-- A segment's public number of claims on the weights, off the built plan; 0 where the plan has no
such segment. (That it has one, for l < 25: the first conjunct of `cleared_by_sort`,
PileWalkAtFlat.lean of this folder, under that theorem's premises.) -/
def nclAt (Z : ProofFile.Pub) (l : Nat) : Nat := ((Z.p.built.links[l]?).map (·.NCL)).getD 0

/-- **The number, on the chain, of the batching round of segment l's merge.** At the head: as many
rounds as stand in front of number 346. At a layers' segment l = 2 g: as many as stand in front of
number 14 l + 4, and `layersSigmaAt` at the public data for the layers and the plan of group g (0
in its stead where the public data have no such plan: at g < 12 they have one: the fourth conjunct
of `layersSite_at_flat`). At an odd l the term has a value and no meaning. -/
def sigAt (c : Chain S Cl) (Z : ProofFile.Pub) (l : Nat) : Nat :=
  if l = 24 then roundsAhead c.blocksInOrder 346
  else roundsAhead c.blocksInOrder (14 * l + 4) +
    ((Z.p.X.G[l / 2]?).map fun hp => layersSigmaAt Z.p.X.layers hp (l / 2)).getD 0

/-- The site of the layers' group g. -/
def layerSite (c : Chain S Cl) (Z : ProofFile.Pub) (g : Nat) : PileSite :=
  ⟨⟨2 * g, nclAt Z (2 * g), sigAt c Z (2 * g)⟩, 28 * g + 4, 28 * g + 14, leftLay, false⟩

/-- The head's site. -/
def headSite (c : Chain S Cl) (Z : ProofFile.Pub) : PileSite :=
  ⟨⟨24, nclAt Z 24, sigAt c Z 24⟩, 346, 352, leftHead, true⟩

/-- **THE SITES**: the twelve groups of layers in their order, then the head. -/
def sitesAt (c : Chain S Cl) (Z : ProofFile.Pub) : List PileSite :=
  (List.range 12).map (layerSite c Z) ++ [headSite c Z]

/-- Who is in the list. -/
theorem mem_sitesAt {c : Chain S Cl} {Z : ProofFile.Pub} {σ : PileSite} :
    σ ∈ sitesAt c Z ↔ (∃ g < 12, σ = layerSite c Z g) ∨ σ = headSite c Z := by
  unfold sitesAt
  rw [List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro (⟨g, hg, rfl⟩ | h)
    · exact Or.inl ⟨g, List.mem_range.1 hg, rfl⟩
    · exact Or.inr h
  · rintro (⟨g, hg, rfl⟩ | h)
    · exact Or.inl ⟨g, List.mem_range.2 hg, rfl⟩
    · exact Or.inr h

/-- The list stands in the order of the laying. -/
theorem sitesAt_order (c : Chain S Cl) (Z : ProofFile.Pub) :
    (sitesAt c Z).Pairwise fun a b => a.c < b.c := by
  unfold sitesAt
  rw [List.pairwise_append]
  refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro a b hab
    show 28 * a + 14 < 28 * b + 14
    omega
  · intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
    obtain rfl := List.mem_singleton.1 hb
    have := List.mem_range.1 hg
    show 28 * g + 14 < 352
    omega

/-! ## The merging sub-protocols, by number -/

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A LAYERS' SITE's MERGING SUB-PROTOCOL, BY ITS NUMBER.** -/
theorem layersSite_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (g : Nat) (hg : g < 12) :
    ∃ x : Bool × OnBytes.Desc.First.K4.Par,
      x.2.link = 2 * g ∧ x.2.g = g ∧ x.2.P = Z.p.X.layers ∧ Z.p.X.G[g]? = some x.2.hp ∧
      (∀ b, c.blocksInOrder[28 * g + 4]? = some b → ∀ s rs gs t, b.decide s rs gs = .ok t →
        t.failed = none) ∧
      LayersSite c.blocksInOrder (28 * g + 4) { x.2 with k3Runs := true } (layerSite c Z g).m
        Z.p.X.layers.wsLay := by
  obtain ⟨Lk, b₀, x, e1, e2, -, hla, h1, h2, h3, h4, -, -⟩ := IM.k4_of hS hR O g hg
  rw [O.W] at h3 h4
  have hb₀ := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 2, show 14 * (2 * g) + 2 + 2 = 28 * g + 4 by omega] at hb₀
  refine ⟨x, h1, h2, h3, h4, fun b hb s rs gs t hd => ?_, ⟨b₀, hb₀⟩, ?_, ?_, ?_⟩
  · obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
    exact ((IM.k4_yes hla s t rs gs).1 hd).2.1
  · intro b hb s rs gs t hd
    obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
    exact ((IM.k4_yes hla s t rs gs).1 hd).1
  · show sigAt c Z (2 * g) = roundsAhead c.blocksInOrder (28 * g + 4) + layersSigmaAt x.2.P x.2.hp x.2.g
    unfold sigAt
    rw [if_neg (by omega), show 14 * (2 * g) + 4 = 28 * g + 4 by omega,
      show 2 * g / 2 = g by omega, h4, h3, h2]
    rfl
  · show Z.p.X.layers.wsLay = x.2.P.wsLay
    rw [h3]

/-- **THE HEAD's SITE's MERGING SUB-PROTOCOL, BY ITS NUMBER.** -/
theorem headSite_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) :
    (∀ b, c.blocksInOrder[346]? = some b → ∀ s rs gs t, b.decide s rs gs = .ok t → t.failed = none) ∧
      HeadSite c.blocksInOrder 346 (K11.parOf Z Bs.G₀) (headSite c Z).m Z.p.X.layers.wsLay := by
  obtain ⟨Lk, b₀, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  have hb₀ := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at hb₀
  have hy : ∀ s t rs gs, b₀.decide s rs gs = .ok t →
      Johnson.Desc.First.ForkMerge.headMergeDecide (K11.parOf Z Bs.G₀) s rs = .ok t ∧
        t.failed = none := fun s t rs gs hd => by
    obtain ⟨y, hf, -⟩ := (IM.yes_alone hla (by decide) s t rs gs).1 hd
    rw [K11.blkAt_decide] at y
    exact ⟨y, hf⟩
  refine ⟨fun b hb s rs gs t hd => ?_, ⟨b₀, hb₀⟩, ?_, rfl, ?_⟩
  · obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
    exact (hy s t rs gs hd).2
  · intro b hb s rs gs t hd
    obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
    exact (hy s t rs gs hd).1
  · show Z.p.X.layers.wsLay = Bs.G₀.W.layers.wsLay
    rw [O.W]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.mem_sitesAt
#print axioms ProofFile.Honest.K13.sitesAt_order
#print axioms ProofFile.Honest.K13.layersSite_at_flat
#print axioms ProofFile.Honest.K13.headSite_at_flat
