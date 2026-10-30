-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ClaimsIsLayers.lean: `ClaimsIs`
(Johnson/Desc/K13/Honest/PileDefs.lean) AT A LAYERS' SITE, AT THE CLAIMS THAT THE FUNCTION OF THE
HONEST PARTS OF THE LAYERS' OWN ROUNDS MAKES. One definition with code, and conditional statements
with their proofs.

Johnson/Desc/K13/Honest/ClaimsIsAt.lean has `ClaimsIs` at a layers' site from three named premises;
the third, `ClaimsFromHearing`, is a law on the claims in letters. Here it is shown of the list
that the honest parts' function makes, by `claims_are` (Honest/K4/Law/ClaimsAre.lean), which is
called.
Main names:
  `layersClaims Q wOf`: the parameter's arm: of the instance x and the challenges hd: `mergeClaimsAt
    Q (wOf x) (ptsOf Q (wOf x) hd)` (Johnson/Desc/K4/Honest/Merge.lean, Front.lean), as an array.
    wOf: how the small input of K4's parts is made of the instance: a letter.
  `claimsFromHearing_layers`: **`ClaimsFromHearing` at that arm**, at Szd := `OnBytes.PscRun.Sized`,
    Tie x h fo := ((wOf x).look h).zk = fo.zk, tokOf x := (wOf x).tokv, a := Q.r0; where p's public
    data, plan and group are Q's.
  `claimsIs_layers_at`: **`ClaimsIs` at the site**, from: p's public data, plan and group are Q's
    (hP, hhp, hg); `LayersSite`; `LayersFront` at these three; as many rounds stand in front of
    number j as Q.r0 says; the parameter's arm at the site's segment is `layersClaims`.

What is not claimed. Any of these premises, at any chain. `ClaimsFromHearing` and `ClaimsIs` are
implications (from a return of `hear`; of the fold): they may speak of nothing. `claimsIs_layers_at`
IS CALLED BY NOTHING YET: the road to `ClaimsIs` that this folder takes is `sites_of_fronts`
(SitesClaims.lean), which calls the library's `claimsIs_layers` itself; it stands as that law at
this arm, for a caller at one site. Q, the parts' public data, is a letter: that this is the list
which the seated halves of kind K4's lot merge is not shown (K4PubsTerm.lean's head). Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Desc.K13.Honest.ClaimsIsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E)
open OnBytes.Model (WsClaim WsLay)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (SiteClaims MergeSite ClaimsIs ClaimsFromHearing LayersSite
  LayersFront claimsIs_layers roundsAhead)
open Johnson.Desc.First.Walk (leftLay)
open ProofFile.Honest.K4 (claims_are)

variable {Xi Cl : Type}

/-- **The parameter's arm at a layers' segment.** wOf: how the small input of K4's parts is made of
the instance. -/
def layersClaims (Q : K4Pub) (wOf : Xi → K4In) (x : Xi) (hd : List Fmt.Drawn) :
    Option (Array WsClaim) :=
  (mergeClaimsAt Q (wOf x) (ptsOf Q (wOf x) hd)).map (·.toArray)

/-- **THE LAW ON THE CLAIMS, AT THAT ARM.** -/
theorem claimsFromHearing_layers (Q : K4Pub) (wOf : Xi → K4In) {p : Par} (hP : p.P = Q.P)
    (hhp : p.hp = Q.hp) (hg : p.g = Q.g) {claims : SiteClaims Xi} {link : Nat}
    (hcl : ∀ x hd, claims link x hd = layersClaims Q wOf x hd) :
    ClaimsFromHearing p link Q.r0 claims OnBytes.PscRun.Sized
      (fun x h fo => ((wOf x).look h).zk = fo.zk) (fun x => (wOf x).tokv) := by
  intro x tk fo F G t u o ds h cl n hH hS hD hl hh hzk htk hn hc
  rw [hP, hhp, hg] at hH hl hn
  rw [hP, hg] at hc
  rw [hcl]
  unfold layersClaims
  rw [claims_are (wOf x) h hH hS ds hD hl hh hzk htk n hn cl hc]
  simp

/-- **`ClaimsIs` AT A LAYERS' SITE.** -/
theorem claimsIs_layers_at (Q : K4Pub) (wOf : Xi → K4In) {p : Par} (hP : p.P = Q.P)
    (hhp : p.hp = Q.hp) (hg : p.g = Q.g) {bs : List (Block S Cl)} {start : Xi → S} {j : Nat}
    {m : MergeSite} {lay : WsLay} {claims : SiteClaims Xi} {asked : Xi → E}
    (hcl : ∀ x hd, claims m.link x hd = layersClaims Q wOf x hd)
    (hr0 : roundsAhead bs j = Q.r0) (hS : LayersSite bs j p m lay)
    (hF : LayersFront bs start j OnBytes.PscRun.Sized
      (fun x h fo => ((wOf x).look h).zk = fo.zk) (fun x => (wOf x).tokv)) :
    ClaimsIs bs start j m lay leftLay claims asked false :=
  claimsIs_layers hS hF (hr0 ▸ claimsFromHearing_layers Q wOf hP hhp hg hcl)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.claimsFromHearing_layers
#print axioms ProofFile.Honest.K13.claimsIs_layers_at
#print axioms ProofFile.Honest.K13.layersClaims
