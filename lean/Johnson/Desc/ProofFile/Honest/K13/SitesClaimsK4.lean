-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SitesClaimsK4.lean: `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN, WITH THE LAW ON THE LAYERS' CLAIMS MET BY THE LIST OF CLAIMS THAT THE HONEST PARTS'
FUNCTION MAKES: FROM THE TEN PREMISES NAMED BELOW. One definition: a premise's form; and conditional
statements with their proofs.

SitesClaims.lean of this folder has the member from five premises; one, hlaw, is `ClaimsFromHearing`
at each group of layers. ClaimsIsLayers.lean of this folder shows `ClaimsFromHearing` of the list
that the honest parts' function makes (`layersClaims`), by `claims_are`
(Honest/K4/Law/ClaimsAre.lean). Here the two are joined, group by group:
`claimsFromHearing_layers` is called, and then `pileWalk_at_chain`.
Main names:
  `K4PubsAt c Z Qs`: what is asked of the public data Qs g of K4's honest parts, for each g < 12:
    its data for the layers are Z's; its plan is the plan of group g; its group is g; as many rounds
    stand in front of its first as in front of number 28 g + 4 of the chain's list. All public.
  `hlaw_of_k4`: **hlaw**, at Szd g := `OnBytes.PscRun.Sized`, Tie g x h fo := ((wOf g x).look h).zk
    = fo.zk, tokOf g x := (wOf g x).tokv; from `K4PubsAt` and: the parameter's arm at segment 2 g is
    `layersClaims (Qs g) (wOf g)`. wOf: by the group, how the small input of K4's parts is made of
    the instance: a free parameter.
  `pileWalk_at_chain_k4`, `pileIs_at_chain_k4`: **`PileWalk`, and so `PileIs`, at c.blocksInOrder, the IOP's
    own start, the border 355**, from ten premises: hS, hR (the public files are in the goals' scope
    and are read) · O (the library's "opened") · hp (`planOk` at each of the list) · `K4PubsAt` (hQ)
    · the arms (hcl) · hfront at these three · hhead · hreach · hfive. pubOf, how an instance's
    public part is read, is a free parameter.

What is not claimed. Any of these premises; that they can be met together. `PileWalk` and `PileIs`
are implications from the return of the verifier's fold: where no fold returns they speak of
nothing. `pileWalk_at_chain_k4` and `pileIs_at_chain_k4` ARE CALLED BY NOTHING YET:
`k13_pileIs_at_head` (PileIsAtHead.lean) calls `pileIs_at_chain` and `hlaw_of_k4` by hand; the two
stand as the joined form, for a caller that has `K4PubsAt` and the arms as premises. That this is
the list which the seated halves of kind K4's lot merge is not shown (K4PubsTerm.lean's head). It is
none of the library's goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.SitesClaims
import Johnson.Desc.ProofFile.Honest.K13.ClaimsIsLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (PileSite PileWalk PileIs SiteClaims FoldReaches
  pileBySites pileIs_of_claimsIs LayersFront ClaimsFromHearing HeadClaimIs roundsAhead)
open ProofFile (Cl)

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Xi : Type}

/-- **What is asked of the public data of K4's honest parts, group by group.** -/
def K4PubsAt (c : Chain S Cl) (Z : ProofFile.Pub) (Qs : Nat → K4Pub) : Prop :=
  ∀ g < 12, (Qs g).P = Z.p.X.layers ∧ Z.p.X.G[g]? = some (Qs g).hp ∧ (Qs g).g = g ∧
    (Qs g).r0 = roundsAhead c.blocksInOrder (28 * g + 4)

/-- **THE LAW ON THE LAYERS' CLAIMS, GROUP BY GROUP, BY THE CLAIMS THAT THE HONEST PARTS' FUNCTION
MAKES.** -/
theorem hlaw_of_k4 {c : Chain S Cl} {Z : ProofFile.Pub} (claims : SiteClaims Xi) (Qs : Nat → K4Pub)
    (wOf : Nat → Xi → K4In) (hQ : K4PubsAt c Z Qs)
    (hcl : ∀ g < 12, ∀ x hd, claims (2 * g) x hd = layersClaims (Qs g) (wOf g) x hd) :
    ∀ g < 12, ∀ p : OnBytes.Desc.First.K4.Par, p.P = Z.p.X.layers →
      Z.p.X.G[g]? = some p.hp → p.g = g →
      ClaimsFromHearing p (2 * g) (roundsAhead c.blocksInOrder (28 * g + 4)) claims OnBytes.PscRun.Sized
        (fun x h fo => ((wOf g x).look h).zk = fo.zk) (fun x => (wOf g x).tokv) := by
  intro g hg p hP hhp hgp
  obtain ⟨q1, q2, q3, q4⟩ := hQ g hg
  rw [← q4]
  exact claimsFromHearing_layers (Qs g) (wOf g) (hP.trans q1.symm)
    (Option.some.inj (hhp.symm.trans q2)) (hgp.trans q3.symm) (hcl g hg)

/-- **`PileWalk`, FROM THE TEN PREMISES THAT THE HEAD NAMES.** -/
theorem pileWalk_at_chain_k4 (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E) (Qs : Nat → K4Pub) (wOf : Nat → Xi → K4In)
    (hQ : K4PubsAt c Z Qs)
    (hcl : ∀ g < 12, ∀ x hd, claims (2 * g) x hd = layersClaims (Qs g) (wOf g) x hd)
    (hfront : ∀ g < 12, LayersFront c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) (28 * g + 4)
      OnBytes.PscRun.Sized (fun x h fo => ((wOf g x).look h).zk = fo.zk)
      (fun x => (wOf g x).tokv))
    (hhead : HeadClaimIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 346 24 claims asked)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hfive : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileWalk c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n Z.p.X.layers.wsLay Z.first.lin
      (sitesAt c Z) claims asked VerifiableInference.Desc.First.S.rows :=
  pileWalk_at_chain hS hR O hp pubOf n claims asked (Szd := fun _ => OnBytes.PscRun.Sized)
    (Tie := fun g x h fo => ((wOf g x).look h).zk = fo.zk) (tokOf := fun g x => (wOf g x).tokv)
    hfront (hlaw_of_k4 claims Qs wOf hQ hcl) hhead hreach hfive

/-- **So `PileIs` there**, from the same ten. -/
theorem pileIs_at_chain_k4 (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E) (Qs : Nat → K4Pub) (wOf : Nat → Xi → K4In)
    (hQ : K4PubsAt c Z Qs)
    (hcl : ∀ g < 12, ∀ x hd, claims (2 * g) x hd = layersClaims (Qs g) (wOf g) x hd)
    (hfront : ∀ g < 12, LayersFront c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) (28 * g + 4)
      OnBytes.PscRun.Sized (fun x h fo => ((wOf g x).look h).zk = fo.zk)
      (fun x => (wOf g x).tokv))
    (hhead : HeadClaimIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 346 24 claims asked)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hfive : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n
      (pileBySites Z.p.X.layers.wsLay Z.first.lin ((sitesAt c Z).map (·.m)) claims) asked :=
  pileIs_of_claimsIs (pileWalk_at_chain_k4 hS hR O hp pubOf n claims asked Qs wOf hQ hcl hfront
    hhead hreach hfive)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.hlaw_of_k4
#print axioms ProofFile.Honest.K13.pileWalk_at_chain_k4
#print axioms ProofFile.Honest.K13.pileIs_at_chain_k4
#print axioms ProofFile.Honest.K13.K4PubsAt
