-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SitesClaims.lean: THE PREMISE `sites` OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN, BY CALLS; AND THE MEMBER OF `PileWalk` AS IT STANDS WITH THAT. Conditional statements with
their proofs.

`ClaimsIs` at a layers' site and at the head's follows from named premises (`claimsIs_layers`,
`claimsIs_head`: Johnson/Desc/K13/Honest/ClaimsIsAt.lean). Of these, `LayersSite` and `HeadSite` are
shown at the chain's own numbers (SitesAtFlat.lean of this folder). Here the two are joined.
Under: In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the proof
file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the first
chain); for the member also hp: every sub-protocol of the chain's list passes its own test on the
plan.
Main names:
  `sites_of_fronts`: **`ClaimsIs` at every site of `sitesAt c Z`**, at any start, from: hfront:
    `LayersFront` at each number 28 g + 4 (three sentences on the fold's state in front of it: its
    ledger; what the lookup returned; its tokens) · hlaw: `ClaimsFromHearing` at each group g (the
    law on the claims, from the hearing's own return), asked at every K4's data with Z's public data
    for the layers, the plan of group g and the number g · hhead: `HeadClaimIs` at number 346 and
    segment 24. Szd, Tie, tokOf: free parameters, as in ClaimsIsAt.lean: HERE BY THE GROUP g: each
    group has its own three.
  `pileWalk_at_chain`, `pileIs_at_chain`: **`PileWalk`, and so `PileIs`, at c.blocksInOrder, the IOP's own
    start, the border 355, the filler over `sitesAt c Z`**, from FIVE premises: hfront · hlaw ·
    hhead · hreach (`reach`) · hfive (`stays` at the five numbers in front of a site's laying:
    StaysAtFlat.lean).

What is not claimed. Any of the five; that they can be met together; that hp holds. It is none of
the library's goals. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.StaysAtFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (PileSite PileWalk PileIs ClaimsIs SiteClaims FoldReaches
  pileBySites pileIs_of_claimsIs LayersFront ClaimsFromHearing HeadClaimIs claimsIs_layers
  claimsIs_head roundsAhead)
open ProofFile (Cl)

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Xi : Type}

/-- **`ClaimsIs` AT EVERY SITE OF THE LIST, BY CALLS**: from: at each group of layers: the three
sentences on the fold's state in front of the merging sub-protocol (`LayersFront`) and the law on
the claims (`ClaimsFromHearing`), the second asked at every K4's data with the library's public
data for the layers, the plan of group g and the number g; at the head: the law on the claim. -/
theorem sites_of_fronts (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Xi → S)
    (claims : SiteClaims Xi) (asked : Xi → E) {Szd : Nat → Fork → Prop}
    {Tie : Nat → Xi → List Fmt.Drawn → Forest.Heard → Prop} {tokOf : Nat → Xi → Array Nat}
    (hfront : ∀ g < 12, LayersFront c.blocksInOrder start (28 * g + 4) (Szd g) (Tie g) (tokOf g))
    (hlaw : ∀ g < 12, ∀ p : OnBytes.Desc.First.K4.Par, p.P = Z.p.X.layers →
      Z.p.X.G[g]? = some p.hp → p.g = g →
      ClaimsFromHearing p (2 * g) (roundsAhead c.blocksInOrder (28 * g + 4)) claims (Szd g) (Tie g)
        (tokOf g))
    (hhead : HeadClaimIs c.blocksInOrder start 346 24 claims asked) :
    ∀ σ ∈ sitesAt c Z,
      ClaimsIs c.blocksInOrder start σ.j σ.m Z.p.X.layers.wsLay σ.left claims asked σ.head := by
  intro σ hσ
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · obtain ⟨x, _, h2, h3, h4, _, hL⟩ := layersSite_at_flat hS hR O g hg
    exact claimsIs_layers hL (hfront g hg) (hlaw g hg { x.2 with k3Runs := true } h3 h4 h2)
  · exact claimsIs_head (headSite_at_flat hS hR O).2 hhead

/-- **THE MEMBER OF `PileWalk` AT THE IOP's OWN FIRST CHAIN AND START, WITH `sites` BY CALLS.** -/
theorem pileWalk_at_chain (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E) {Szd : Nat → Fork → Prop}
    {Tie : Nat → Xi → List Fmt.Drawn → Forest.Heard → Prop} {tokOf : Nat → Xi → Array Nat}
    (hfront : ∀ g < 12,
      LayersFront c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) (28 * g + 4) (Szd g) (Tie g) (tokOf g))
    (hlaw : ∀ g < 12, ∀ p : OnBytes.Desc.First.K4.Par, p.P = Z.p.X.layers →
      Z.p.X.G[g]? = some p.hp → p.g = g →
      ClaimsFromHearing p (2 * g) (roundsAhead c.blocksInOrder (28 * g + 4)) claims (Szd g) (Tie g)
        (tokOf g))
    (hhead : HeadClaimIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 346 24 claims asked)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hfive : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileWalk c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n Z.p.X.layers.wsLay Z.first.lin
      (sitesAt c Z) claims asked VerifiableInference.Desc.First.S.rows :=
  pileWalk_at_desc_five hS hR O hp pubOf n claims asked
    (sites_of_fronts hS hR O _ claims asked hfront hlaw hhead) hreach hfive

/-- **So `PileIs` there.** -/
theorem pileIs_at_chain (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E) {Szd : Nat → Fork → Prop}
    {Tie : Nat → Xi → List Fmt.Drawn → Forest.Heard → Prop} {tokOf : Nat → Xi → Array Nat}
    (hfront : ∀ g < 12,
      LayersFront c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) (28 * g + 4) (Szd g) (Tie g) (tokOf g))
    (hlaw : ∀ g < 12, ∀ p : OnBytes.Desc.First.K4.Par, p.P = Z.p.X.layers →
      Z.p.X.G[g]? = some p.hp → p.g = g →
      ClaimsFromHearing p (2 * g) (roundsAhead c.blocksInOrder (28 * g + 4)) claims (Szd g) (Tie g)
        (tokOf g))
    (hhead : HeadClaimIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 346 24 claims asked)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hfive : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n
      (pileBySites Z.p.X.layers.wsLay Z.first.lin ((sitesAt c Z).map (·.m)) claims) asked :=
  pileIs_of_claimsIs
    (pileWalk_at_chain hS hR O hp pubOf n claims asked hfront hlaw hhead hreach hfive)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.sites_of_fronts
#print axioms ProofFile.Honest.K13.pileWalk_at_chain
#print axioms ProofFile.Honest.K13.pileIs_at_chain
