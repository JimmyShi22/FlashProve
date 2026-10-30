-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HonestAtHome.lean: THE HONEST SIDE's COUNT AT THE TOLD RECORD OF THE GOALS'
DESCRIPTION WITH ITS NUMBER OF COINS LAID ANEW: `((theTerms placeHolderCoins).T Z).reBound (b Z)`
over the input `(flashProveDescription.reBound b).input Z allZeroDigest []`, b a letter (the record on which the members of
theWider stand); and **HonestWithin (Ladder.lean) at every member theWider K ⟨b, gen⟩, in scope,
where protocolDataWellFormed says yes**, from bounds on K's sampler and prover alone. Calls: it adds no strength.

Main names.
  passHome         the one test on first blocks there (firstBlockTestAtDescriptionData,
    Johnson/Goal/Conditions/HonestAtDescriptionDataAtFiles.lean).
  firstIs_home, passFits_home, reading_home   the premises of the count there: NO PREMISE.
  det_home         the carried runs' value there, at every hash function (det_carryF).
  depths_home      in scope, where protocolDataWellFormed says yes, the three request trees have the depths 0, 0,
  6.
  allF_home        so, at a draw whose three paths have their trees' depths, allF is
    7068035999651.
  queryBound_home  THE HONEST PROVER's PROGRAM THERE asks the hash function at most
    8 + 7068035999651 times on every path: at every printer, strategy, instance and draw.
  queryBound_drawn a prover that draws one number and then runs such a program.
  honestWithin_wider_live   THE STATEMENT.

What the last asks. The public files are read and in scope · protocolDataWellFormed says yes · K.sample asks
nothing · K.prove asks at most 8 + 7068035999651 times (by queryBound_drawn and queryBound_home,
where K.prove draws a number and runs proveForm at these letters).

Limits. That protocolDataWellFormed accepts is proved in Lean, in the side library (outside the main library and
with that library's own limits), at the written copy of the full-size example's files under every
acceptance policy in scope (theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean; see
Johnson/Goal/Conditions/HomeLast.lean, limit 4); that theorem is not called here. The scope is wider
than these files; elsewhere in it that protocolDataWellFormed accepts stays a premise. "A path has its tree's
depth" is a premise on the draws (a clause of Coins.Fit, OnBytes/Prover/Inv.lean). THE CAPS ARE OF
OUR CHOOSING. No K is written here. NO COMPLETENESS.
Local letters (notation of this file alone). ℌ: the compiler's input Description.input
  (Description.reBound flashProveDescription b) Z allZeroDigest [] · 𝔗: the told record over it, LayoutsByPublicReading.reBound (HonestTerms.T
  (theTerms placeHolderCoins) Z) (b Z).
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HonestAtLive
import Johnson.Goal.Conditions.KeyDepthAtThe
import Johnson.Goal.Numbers.DepthAtThe
import Johnson.Goal.Conditions.ReBound
import Johnson.Goal.Conditions.PlaceHolderCoins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.Prover TypedOracleCompiler.Compile.Batch.Cms

/-- A prover that draws one number and then runs a program without further draws. -/
theorem queryBound_drawn {α : Type} {N : ℕ} (c : Fin (N + 1) → Rom.OComp (rom 256) α) (q : ℕ)
    (h : ∀ a, (c a).QueryBound q) :
    (RandomizedAlgorithm.sample N fun a =>
      (deterministicOf (ofRom (c a))).toRandomized).QueryBound q :=
  fun a => queryBound_deterministicOf _ q (queryBound_ofRom _ q (h a))

section
/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- the input there -/
local notation "ℌ" => Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []
/-- the told record there -/
local notation "𝔗" => LayoutsByPublicReading.reBound (HonestTerms.T (theTerms placeHolderCoins) Z) (b Z)

theorem k_pos_home : 0 < (ℌ).queryLayout.K := k_pos (sAt Z) allZeroDigest []

/-- The one test on first blocks there. -/
abbrev passHome : Pass 256 (typedOracleCarrier (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits) := firstBlockTestAtDescriptionData (sAt Z) allZeroDigest []

theorem firstIs_home (d : (𝔗).D) : FirstIs (k_pos_home b Z) ((𝔗).m d) :=
  firstIs_layoutsByPublicReading (sAt Z) allZeroDigest [] d

theorem passFits_home (d : (𝔗).D) :
    PassFits (ℌ).queryLayout ((𝔗).Sd d) (k_pos_home b Z) (passHome b Z) :=
  passFits_layoutsByPublicReading (sAt Z) allZeroDigest [] d

theorem reading_home : (𝔗).Pub.QueryBound 8 :=
  pub8_queries OnBytes.Tie.recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay

/-- **The three request trees' depths.** -/
theorem depths_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (ℌ).queryLayout.depthReqT = 0 ∧ (ℌ).queryLayout.depthReqL = 0 ∧ (ℌ).queryLayout.depthReq = 6 :=
  ⟨depthReqT_the Z live allZeroDigest [], rfl, depth_the Z scope live⟩

variable {Kap Form : Type}

/-- The carried runs' value there, at every hash function. -/
theorem det_home (b₀ : (ℌ).LeafBody) (st : Strats (ℌ).protocol Kap) (capT' capL' capB' : ℕ → ℕ)
    (g : Fam (rom 256)) (d : (𝔗).D)
    (isk : (ℌ).Index × (ℌ).protocol.EncodingRandomness × (ℕ → Bits)) (x : (ℌ).Instance)
    (dw : Draw 256 (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap) :
    (carryF (𝔗) (fun _ => passHome b Z) d
      (runsAt (𝔗) b₀ st capT' capL' capB' d isk x dw)).det g =
      (runsAt (𝔗) b₀ st capT' capL' capB' d isk x dw).det (readBlocks ((𝔗).m d) g) := by
  exact det_carryF (𝔗) b₀ st capT' capL' capB' (firstIs_home b Z) (passFits_home b Z) g d isk x
    dw

/-- **allF there, as a numeral.** -/
theorem allF_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (dw : Draw 256 (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap)
    (pT : dw.coT.path.length = (ℌ).queryLayout.depthReqT) (pL : dw.coL.path.length = (ℌ).queryLayout.depthReqL)
    (pB : dw.coB.path.length = (ℌ).queryLayout.depthReq) :
    allF (ℌ).queryLayout (capT (sAt Z)) capL (capB (sAt Z)) dw = 7068035999651 :=
  allF_written (sAt Z) allZeroDigest [] (key_built_written Z scope live) (proof_built_written Z scope live)
    dw (pT.trans (depths_home b Z scope live).1) (pL.trans (depths_home b Z scope live).2.1)
    (pB.trans (depths_home b Z scope live).2.2)

/-- **The honest prover's program there.** -/
theorem queryBound_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (b₀ : (ℌ).LeafBody) (st : Strats (ℌ).protocol Kap) (iskOf : (𝔗).D → (ℌ).Index × (ℌ).protocol.EncodingRandomness × (ℕ → Bits))
    (x : (ℌ).Instance)
    (drawOf : (𝔗).D → Draw 256 (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap)
    (print : (𝔗).D → Raw 256 (ℌ).protocol (ℌ).offlineRoundSplits (ℌ).linkRoundSplits → Form)
    (paths : ∀ d, (drawOf d).coT.path.length = (ℌ).queryLayout.depthReqT ∧
      (drawOf d).coL.path.length = (ℌ).queryLayout.depthReqL ∧
      (drawOf d).coB.path.length = (ℌ).queryLayout.depthReq) :
    (proveForm (𝔗) b₀ st (capT (sAt Z)) capL (capB (sAt Z))
      (fun d => carryF (𝔗) (fun _ => passHome b Z) d) iskOf x drawOf print).QueryBound
      (8 + 7068035999651) := by
  exact queryBound_proveForm (𝔗) b₀ st (capT (sAt Z)) capL (capB (sAt Z)) iskOf x drawOf print 8
    _ (reading_home b Z) (firstIs_home b Z) (passFits_home b Z) fun d =>
      le_of_eq (allF_home b Z scope live (drawOf d) (paths d).1 (paths d).2.1 (paths d).2.2)

end

/-- **HonestWithin at every member theWider K ⟨b, gen⟩, in scope, where protocolDataWellFormed says yes.** -/
theorem honestWithin_wider_live (K : TheCoins) (W : WiderCoins K) (o : SecondHashFunctionType) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hS : K.sample.QueryBound 0)
    (hP : ∀ w ρ p t, (K.prove Z (settingsOfRead pp) w ρ p t).QueryBound (8 + 7068035999651)) :
    HonestWithin (theWider K W o) Z (settingsOfRead pp) :=
  honestWithin_theWider K W o Z pp hr 0 _ hS hP (by
    rw [count₀_live Z scope live]
    exact honest_number)

end FlashProve

#print axioms FlashProve.queryBound_drawn
#print axioms FlashProve.k_pos_home
#print axioms FlashProve.firstIs_home
#print axioms FlashProve.passFits_home
#print axioms FlashProve.reading_home
#print axioms FlashProve.depths_home
#print axioms FlashProve.det_home
#print axioms FlashProve.allF_home
#print axioms FlashProve.queryBound_home
#print axioms FlashProve.honestWithin_wider_live
