-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SitesOfLaws.lean: THE SITES AND THE CLAIMS' TEXT AT ANY SIZE
(SitesOfDefs.lean of this folder) ARE, IN THE GOALS' SCOPE, THE WRITTEN ONES: `sitesAt`
(SitesAtFlat.lean) AND, AT EVERY SITE's SEGMENT, `claimsText` (ClaimsText.lean). Four definitions,
and statements with their proofs.

So every law that is shown of the filler over the written sites and the written text carries over to
the filler over the general ones, in scope: that step is `pileAtChain_scope` (PileOfAnySizeAt.lean).
Main names:
`layerSiteOf`, `headSiteOf`, `siteOfSeg`, `sitesOf c Z`: **THE SITES, AT ANY SIZE**, with the
numbers of the sub-protocol that merges and of the one that lays the row, and the reader of what the
merge left. The segment's last sub-protocol, which lays the row, stands five behind the batching, so
six behind the last one in front of it: `IM.flatIx c l 12` (6 + 6); at the head's segment 14
(8 + 6). Nothing outside this file names the four: they are a bridge to `mergeSitesOf_eq`; of
`sitesOf` no caller reads the fields j, c, left and head.
`sitesOf_m`: **at every size: (sitesOf c Z).map (·.m) = mergeSitesOf c Z.**
`nclOfSeg_eq`, `blankHPlan_eq`, `smallInOf_eq`: the three definitions that were typed anew are one
with the earlier ones.
`groupOfSeg_layers`, `headSegOf_scope`: in scope: the group of segment 2 g is g, for g < 12; the
head's segment is 24.
`layerSiteOf_eq`, `headSiteOf_eq`, `sitesOf_eq_sitesAt`: **IN SCOPE: sitesOf c Z = sitesAt c Z**;
`mergeSitesOf_eq`: so mergeSitesOf c Z = (sitesAt c Z).map (·.m).
`k4PubOfSeg_eq`, `claimsTextOf_layers`, `claimsTextOf_head`, `claimsTextOf_at_sites`: **IN SCOPE, AT
EVERY SITE's SEGMENT: claimsTextOf at lookAt and Q₀ is claimsText at fun g => lookAt (2 * g) and fun
g => Q₀ (2 * g).**
Called: `IM.subs_all` (Johnson/IMR/PlacesScope.lean), `IM.flatIx_scope`
(Johnson/IMR/FlatScope.lean), `IM.ground_named`, `IM.blank_ground` (Johnson/IMR/PureJoin.lean),
`VerifiableInference.OnPublicFiles.zipped_g` (Johnson/Desc/First/Look/K03LeftQ.lean), `mem_sitesAt`
(SitesAtFlat.lean), `claimsText_arm` (ClaimsText.lean).

"IN SCOPE" STANDS FOR THREE PREMISES, in ten of the fourteen statements: hS (`VerifierAndGoals.InScope`), hR
(`VerifierAndGoals.readFiles`) and O (`IM.Open`, Johnson/IMR/SeatOpen.lean: the maker of the IOP as written in
Lean returned, opened letter by letter). SO c AND Z ARE NOT FREE THERE: O pins both. AT THE FORMAT's
EARLIER HASH ALONE. Who pays: under the library's one hypothesis at the full size all three are its
fields (PileOfAnySizeAt.lean). That the three can be met together is not shown here: where they
cannot, the ten speak of nothing. This file's imports reach Johnson/Goal/ (through
Johnson/IMR/PureJoin.lean). What is not claimed. ANYTHING AT ANOTHER SIZE THAN THE GOALS', but
`sitesOf_m` and the three equations of the definitions typed anew: not that K4 or K11 stands at the
number named; not that the row is laid at the number named (beyond the sub-protocols in front of the
batching `IM.flatIx` is arithmetic alone); not that the filler over these sites yields a row. At a
segment that is no site's the two texts may part. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.SitesOfDefs
import Johnson.Desc.ProofFile.Honest.K13.ClaimsText
import Johnson.IMR.PlacesScope
import Johnson.IMR.PureJoin
import Johnson.Desc.First.Look.K03LeftQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.K13.Honest (MergeSite PileSite roundsAhead layersSigmaAt)
open Johnson.Desc.First.Walk (leftLay)
open ProofFile (Cl)

/-! ## The sites with their numbers and readers, at any size -/

/-- The site of a layers' segment l. -/
def layerSiteOf (c : Chain S Cl) (Z : ProofFile.Pub) (l : Nat) : PileSite :=
  ⟨⟨l, nclOfSeg Z l, sigOfSeg c Z false l⟩, IM.flatIx c l 2, IM.flatIx c l 12, leftLay, false⟩

/-- The site of the head's segment l. -/
def headSiteOf (c : Chain S Cl) (Z : ProofFile.Pub) (l : Nat) : PileSite :=
  ⟨⟨l, nclOfSeg Z l, sigOfSeg c Z true l⟩, IM.flatIx c l 8, IM.flatIx c l 14, leftHead, true⟩

/-- A segment's site, by its sort. An attention segment has none. -/
def siteOfSeg (c : Chain S Cl) (Z : ProofFile.Pub) : ModelPart → Nat → Option PileSite
  | .layers, l => some (layerSiteOf c Z l)
  | .attention, _ => none
  | .head, l => some (headSiteOf c Z l)

/-- **THE SITES, AT ANY SIZE**: the segments' sites in the segments' order. -/
def sitesOf (c : Chain S Cl) (Z : ProofFile.Pub) : List PileSite :=
  (ProofFile.subsOf Z).zipIdx.filterMap fun x => siteOfSeg c Z x.1 x.2

/-- **At every size the sites' public numbers are `mergeSitesOf`.** -/
theorem sitesOf_m (c : Chain S Cl) (Z : ProofFile.Pub) :
    (sitesOf c Z).map (·.m) = mergeSitesOf c Z := by
  unfold sitesOf mergeSitesOf
  rw [List.map_filterMap]
  refine List.filterMap_congr fun x _ => ?_
  obtain ⟨sub, l⟩ := x
  cases sub <;> rfl

/-! ## The three definitions that were typed anew -/

theorem nclOfSeg_eq : nclOfSeg = nclAt := rfl

theorem blankHPlan_eq : blankHPlan = blankPlan := rfl

theorem smallInOf_eq : smallInOf = smallIn := rfl

/-! ## In the goals' scope they are the written ones -/

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the group of segment 2 g is g. -/
theorem groupOfSeg_layers (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (g : Nat) (hg : g < 12) :
    groupOfSeg Z (2 * g) = g := by
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨l, -, a, -, ga, -⟩ := nam g hg
  obtain ⟨ls, -, -, eB, -⟩ := IM.blank_ground O.blank
  rw [eB] at a
  obtain ⟨b, hb, -, gb⟩ := VerifiableInference.OnPublicFiles.zipped_g a
  unfold groupOfSeg
  rw [hb]
  exact gb.trans ga

/-- In scope the head's segment is number 24. -/
theorem headSegOf_scope (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) : headSegOf Z = 24 := by
  unfold headSegOf
  rw [IM.subs_all hS hR O]
  decide

/-- In scope a layers' site is the written one. -/
theorem layerSiteOf_eq (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (l g : Nat) (hl : l = 2 * g)
    (hg : g < 12) : layerSiteOf c Z l = layerSite c Z g := by
  subst hl
  unfold layerSiteOf layerSite sigOfSeg sigAt
  rw [IM.flatIx_scope hS hR O (by omega) 2, IM.flatIx_scope hS hR O (by omega) 12,
    groupOfSeg_layers hS hR O g hg, if_neg (show ¬ (false = true) by decide),
    if_neg (show ¬ 2 * g = 24 by omega), show 2 * g / 2 = g by omega,
    show 14 * (2 * g) + 2 + 2 = 28 * g + 4 by omega,
    show 14 * (2 * g) + 12 + 2 = 28 * g + 14 by omega]
  rfl

/-- In scope the head's site is the written one. -/
theorem headSiteOf_eq (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) :
    headSiteOf c Z 24 = headSite c Z := by
  unfold headSiteOf headSite sigOfSeg sigAt
  rw [IM.flatIx_scope hS hR O (Nat.le_refl 24) 8, IM.flatIx_scope hS hR O (Nat.le_refl 24) 14,
    if_pos rfl, if_pos rfl]
  rfl

/-- **IN SCOPE THE SITES AT ANY SIZE ARE THE WRITTEN SITES.** -/
theorem sitesOf_eq_sitesAt (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) :
    sitesOf c Z = sitesAt c Z := by
  unfold sitesOf
  rw [IM.subs_all hS hR O]
  show [layerSiteOf c Z 0, layerSiteOf c Z 2, layerSiteOf c Z 4, layerSiteOf c Z 6,
      layerSiteOf c Z 8, layerSiteOf c Z 10, layerSiteOf c Z 12, layerSiteOf c Z 14,
      layerSiteOf c Z 16, layerSiteOf c Z 18, layerSiteOf c Z 20, layerSiteOf c Z 22,
      headSiteOf c Z 24] = _
  rw [layerSiteOf_eq hS hR O 0 0 rfl (by decide),
    layerSiteOf_eq hS hR O 2 1 rfl (by decide),
    layerSiteOf_eq hS hR O 4 2 rfl (by decide),
    layerSiteOf_eq hS hR O 6 3 rfl (by decide),
    layerSiteOf_eq hS hR O 8 4 rfl (by decide),
    layerSiteOf_eq hS hR O 10 5 rfl (by decide),
    layerSiteOf_eq hS hR O 12 6 rfl (by decide),
    layerSiteOf_eq hS hR O 14 7 rfl (by decide),
    layerSiteOf_eq hS hR O 16 8 rfl (by decide),
    layerSiteOf_eq hS hR O 18 9 rfl (by decide),
    layerSiteOf_eq hS hR O 20 10 rfl (by decide),
    layerSiteOf_eq hS hR O 22 11 rfl (by decide),
    headSiteOf_eq hS hR O]
  rfl

/-- So in scope the general public numbers are the written sites'. -/
theorem mergeSitesOf_eq (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) :
    mergeSitesOf c Z = (sitesAt c Z).map (·.m) := by
  rw [← sitesOf_m, sitesOf_eq_sitesAt hS hR O]

/-- In scope the public data of K4's parts at segment 2 g are the written ones of group g. -/
theorem k4PubOfSeg_eq (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (Q₀ : Nat → K4Pub) (g : Nat)
    (hg : g < 12) : k4PubOfSeg c Z Q₀ (2 * g) = k4PubsOf c Z (fun g => Q₀ (2 * g)) g := by
  unfold k4PubOfSeg k4PubsOf
  rw [IM.flatIx_scope hS hR O (by omega) 2, groupOfSeg_layers hS hR O g hg,
    show 14 * (2 * g) + 2 + 2 = 28 * g + 4 by omega]
  rfl

/-- In scope, at a layers' segment, the two texts are one. -/
theorem claimsTextOf_layers (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (lookAt : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) (g : Nat)
    (hg : g < 12) :
    claimsTextOf c Z lookAt headArm Q₀ (2 * g) =
      claimsText c Z (fun g => lookAt (2 * g)) headArm (fun g => Q₀ (2 * g)) (2 * g) := by
  funext x hd
  unfold claimsTextOf
  rw [headSegOf_scope hS hR O, if_neg (by omega), k4PubOfSeg_eq hS hR O Q₀ g hg,
    claimsText_arm c Z _ headArm _ g hg]
  rfl

/-- In scope, at the head's segment, the two texts are one. -/
theorem claimsTextOf_head (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (lookAt : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) :
    claimsTextOf c Z lookAt headArm Q₀ 24 =
      claimsText c Z (fun g => lookAt (2 * g)) headArm (fun g => Q₀ (2 * g)) 24 := by
  funext x hd
  unfold claimsTextOf
  rw [headSegOf_scope hS hR O, if_pos rfl]
  rfl

/-- **IN SCOPE, AT EVERY SITE's SEGMENT, THE TWO TEXTS ARE ONE.** -/
theorem claimsTextOf_at_sites (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (lookAt : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) :
    ∀ σ ∈ sitesAt c Z, claimsTextOf c Z lookAt headArm Q₀ σ.m.link =
      claimsText c Z (fun g => lookAt (2 * g)) headArm (fun g => Q₀ (2 * g)) σ.m.link := by
  intro σ hσ
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · exact claimsTextOf_layers hS hR O lookAt headArm Q₀ g hg
  · exact claimsTextOf_head hS hR O lookAt headArm Q₀

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.sitesOf_m
#print axioms ProofFile.Honest.K13.nclOfSeg_eq
#print axioms ProofFile.Honest.K13.blankHPlan_eq
#print axioms ProofFile.Honest.K13.smallInOf_eq
#print axioms ProofFile.Honest.K13.groupOfSeg_layers
#print axioms ProofFile.Honest.K13.headSegOf_scope
#print axioms ProofFile.Honest.K13.layerSiteOf_eq
#print axioms ProofFile.Honest.K13.headSiteOf_eq
#print axioms ProofFile.Honest.K13.sitesOf_eq_sitesAt
#print axioms ProofFile.Honest.K13.mergeSitesOf_eq
#print axioms ProofFile.Honest.K13.k4PubOfSeg_eq
#print axioms ProofFile.Honest.K13.claimsTextOf_layers
#print axioms ProofFile.Honest.K13.claimsTextOf_head
#print axioms ProofFile.Honest.K13.claimsTextOf_at_sites
#print axioms ProofFile.Honest.K13.layerSiteOf
#print axioms ProofFile.Honest.K13.headSiteOf
#print axioms ProofFile.Honest.K13.siteOfSeg
#print axioms ProofFile.Honest.K13.sitesOf
