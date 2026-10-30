-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileOfAnySizeAt.lean: UNDER THE LIBRARY's ONE HYPOTHESIS AT THE
FULL SIZE AND THE FORMAT's EARLIER HASH THE PILE's FILLER AT ANY NUMBER OF SEGMENTS
(`pileOfAnySize`, PileOfAnySize.lean of this folder) IS, AT A BASE's GROUND, THE FILLER OVER THE
TEXT OF THE CLAIMS WITH ALL ITS ARMS LAID. Five statements with their proofs; no definition. CUT OUT
OF PileOfAnySizeLaw.lean (NO PART OF THE LIBRARY), STATEMENTS AND PROOFS TO THE SIGN, the namespace
and the names as they were: so that a caller need not stand on that file's last statement, which
names a fixed filling of a prover.

Main names: `pileAtChain_scope`: in the goals' scope the filler over the chain is `fillerAt` over
`claimsText`, at every text of the head's claims and every Q₀; `claimsText_light_layers`: its piece
at a layers' segment. `headFourN_scope`, `headArmOfSeg_scope`: in scope the head's four parameters
"at two numbers" and the text of the head's claims are the written ones. `pileOfAnySize_at`: **under
h, at a base's ground, `pileOfAnySize headArmOfSeg Q₀` is that filler.** The base is any: nothing
ties it to the public part.

Limits. EVERY STATEMENT HERE IS AT THE FULL SIZE: in the goals' scope or under h. THAT THE FILLER
YIELDS THE RIGHT ROWS AT ANOTHER NUMBER OF SEGMENTS IS SHOWN BY NO THEOREM. `pileOfAnySize_at` says
that two functions are one: not that either yields a row. No statement names a prover, a filling of
a prover or a thread (three such names stand idle in an `open` line, as they came with the cut). "In
the goals' scope", "in scope": three premises: hS (the scope), hR (the files' reading) and O
(`IM.Open`: the opening, which alone ties the chain c to the public part Z); under h all three are
h's fields. This file's imports reach Johnson/Goal/, Honest/Thread/ and Honest/K3/Law/Thread/: a
caller of `pileOfAnySize_at` loses the lightness of PileOfAnySize.lean.

What is not claimed. That h holds at any public files. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySizeAll
import Johnson.Desc.ProofFile.Honest.K13.SitesOfLaws
import Johnson.Desc.ProofFile.Honest.K13.LightLookLaw
import Johnson.Desc.ProofFile.Honest.K13.AcceptedByTies
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesStatement
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block Chain FileDescription Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Honest (MergeSite SiteClaims roundsAhead pileRowAt pileBySites)
open ProofFile.Honest.K11 (headFourOfK6 headMergeClaims)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 callsShape headKeysOfK3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile (Cl)

/-! ## In the goals' scope it is the written one -/

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope, at a layers' segment, the written text of the claims at the light look by the segment
is the written text at the full look by the group. -/
theorem claimsText_light_layers (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q : Nat → K4Pub) (g : Nat)
    (hg : g < 12) :
    claimsText c Z (fun g => lookOfSeg Z c (2 * g)) headArm Q (2 * g) =
      claimsText c Z (lookOfK3 Z c) headArm Q (2 * g) := by
  funext x hd
  rw [claimsText_arm c Z _ headArm Q g hg, claimsText_arm c Z _ headArm Q g hg]
  have e : IM.flatIx c (2 * g) 1 = 28 * g + 3 := by
    rw [IM.flatIx_scope hS hR O (by omega) 1]
    omega
  unfold lookOfSeg
  rw [e]
  exact layersClaims_light (k4PubsOf c Z Q g) (smallIn Z (lookOfK3 Z c g)) (callsShape Z g) _ x hd

/-- In scope the head's four parameters "at two numbers", at the head's segment and the two counts,
are the written ones. -/
theorem headFourN_scope (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (G : ProofFile.Ground) :
    K11.headFourN (headSegOf Z) (roundsAhead c.blocksInOrder (IM.flatIx c (headSegOf Z) 2))
        (roundsAhead c.blocksInOrder (IM.flatIx c (headSegOf Z) 3)) Z G =
      headFourOfK6 (headKeysOfK3 c) (roundsAhead c.blocksInOrder 341) Z G := by
  rw [headSegOf_scope hS hR O, IM.flatIx_scope hS hR O (Nat.le_refl 24) 3,
    IM.flatIx_scope hS hR O (Nat.le_refl 24) 2]
  rfl

/-- In scope the text of the head's claims is the written one. -/
theorem headArmOfSeg_scope (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (Bs' : ProofFile.PureBase) :
    headArmOfSeg c Z Bs'.G₀ =
      headArmOf (headFourOfK6 (headKeysOfK3 c) (roundsAhead c.blocksInOrder 341)) Z Bs' := by
  funext x hd
  unfold headArmOfSeg headArmOf K11.headClaimsN headMergeClaims
  rw [headFourN_scope hS hR O Bs'.G₀]

/-- **IN SCOPE THE FILLER OVER THE CHAIN AT ANY NUMBER OF SEGMENTS IS THE WRITTEN FILLER OVER THE
WRITTEN TEXT OF THE CLAIMS**, at every text of the head's claims and every Q₀. -/
theorem pileAtChain_scope (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) :
    pileAtChain c Z headArm Q₀ =
      fillerAt c Z (claimsText c Z (lookOfK3 Z c) headArm (fun g => Q₀ (2 * g))) := by
  unfold pileAtChain fillerAt
  rw [mergeSitesOf_eq hS hR O]
  refine pileBySites_congr _ _ _ fun m hm => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hm
  rw [claimsTextOf_at_sites hS hR O (lookOfSeg Z c) headArm Q₀ σ hσ]
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · exact claimsText_light_layers hS hR O headArm _ g hg
  · funext x hd
    show claimsText c Z _ headArm _ 24 x hd = claimsText c Z _ headArm _ 24 x hd
    rw [claimsText_head, claimsText_head]

end

/-! ## Under the library's one hypothesis at the full size -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **UNDER h THE FILLER AT ANY NUMBER OF SEGMENTS IS THE WRITTEN FILLER**, at a base's ground. -/
theorem pileOfAnySize_at (Q₀ : ProofFile.Pub → Nat → K4Pub) (Bs : ProofFile.PureBase) :
    pileOfAnySize headArmOfSeg Q₀ Zp Bs.G₀ =
      fillerAt cF Zp (claimsText cF Zp (lookOfK3 Zp cF)
        (headArmOf (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp Bs)
        (fun g => Q₀ Zp (2 * g))) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  unfold pileOfAnySize pileBoxOfAnySize
  rw [h.laid.chain]
  show pileAtChain cF Zp (headArmOfSeg cF Zp Bs.G₀) (Q₀ Zp) = _
  rw [pileAtChain_scope h.scope h.reads O, headArmOfSeg_scope h.scope h.reads O Bs]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.claimsText_light_layers
#print axioms ProofFile.Honest.K13.headFourN_scope
#print axioms ProofFile.Honest.K13.headArmOfSeg_scope
#print axioms ProofFile.Honest.K13.pileAtChain_scope
#print axioms ProofFile.Honest.K13.pileOfAnySize_at
