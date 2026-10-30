-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/HomeTies.lean: the connecting lemmas at homeR b Z: those that the proof of
homeExact uses, and home_beside.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves. At the parameters of Johnson/LinkSim/AtHome/SpecHome.lean, it proves three
kinds of premise. First, each premise of Spec.exactOfText (Johnson/LinkSim/AtText/SpecExact.lean)
that concerns public parameters or the honest data. Second, both premises of Spec.linkShiftIn
(Johnson/LinkSim/AtText/SpecShiftIn.lean). Third, part of what PremW asks of the link's protocol
besides a simulator: two counts and locality (home_beside). None of the nine lemmas asks that the
files be in scope or the description live.

How it fits. homeExact (Johnson/LinkSim/AtHome/Home.lean) and roadCloses (RoadCloses.lean) use
home_stages, home_want, home_stored, home_keys and home_cols. home_upTo (RoadCloses.lean) uses
home_sizes and home_claim; home_claim uses home_meant. link_all_met (CompileFiller.lean) uses
home_beside.

Main names (namespace OnBytes.LinkSim.AtHome).
  home_stages     the stages of the protocol's plan have a first one (frFirst :: frRest).
  home_want       every position that the verifier queries in one of the prover's own trees is one
                  at which the proximity test's schedule opens that tree (WantTie), for every list
                  of challenges.
  home_stored     each position at which the prover's algorithm opens a stored table is among the
                  positions that the protocol's challenges ask of that table (StoredTie).
  home_keys       the honest data's keys are the instance's two keys (by definition).
  home_cols       the honest data's stored column at a position in range is the column in the
                  input oracles' symbol there.
  home_meant      at a valid private input and instance, the instance, the two encodings and the
                  polynomials of their rows satisfy Meant (Johnson/Prover/Link/LinkYesStm.lean),
                  the relation under which the link's acceptance is proved.
  home_sizes      the public premises on sizes hold at the challenges of every verifier message.
  home_claim      the premise on the honest run, at a valid private input and instance and at the
                  challenges of every verifier message and at all coins that are 0 outside the
                  places: at the last stage, the claim left at the base case is true at the honest
                  prover's last message, or the element sampled there is 0.
  home_beside     LinkBeside (Johnson/LinkSim/Spec.lean), part of what PremW asks of the link's
                  protocol besides a simulator: two counts and locality. At homeR b Z's own
                  protocol structure, at 62 and 62, the link's verifier reads at most 62
                  positions of the first table and 62 of the copy, and is local.

Limits.
"Valid" is validLk (Johnson/LinkSim/Spec.lean) at any range of indices and any set of seeds. Of it,
only "the instance is the two honest OOD samples" is used.

Notes.
- On acceptance at every ρ: the simulator computes one disclosed value from the verifier's final
  equation. The simulated value equals the honest one plus a verifier challenge times the error, at
  the honest run, of the claim left at the base case, so the two agree exactly where that claim is
  true or that challenge is 0. At homeR b Z this disjunction is proved for every valid input, every
  ρ and all coins C with InPlaces C, that is, 0 outside the sizes (home_claim,
  Johnson/LinkSim/AtHome/HomeTies.lean; InPlaces, Johnson/LinkSim/AtText/Places.lean), so homeExact
  needs no such premise. It is not a proof that the verifier accepts at every ρ.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.SpecHome
import Johnson.LinkSim.AtText.SeamAtFull
import Johnson.LinkSim.AtText.SeamAtFull2
import Johnson.LinkSim.AtText.SeamAtFull3
import Johnson.LinkSim.AtText.SeamClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open PV.EntryFive (dsF xsF)
open Johnson.Prover.Link (LCoins BEnd linOf keysOf yCol Meant frFirst frRest fr_cons drawsOf)
open _root_.Desc.K15 (frP p12Of)
open _root_.Iop (twoExternalStrings Rho)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (SOf drawnSL)
open OnBytes.LinkSim (validLk LinkBeside)
open OnBytes.LinkSim.AtText (Sizes InPlaces linkEnd LamZero ClaimTrue)
open OnBytes.LinkSim.Seam

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-! ## The public parameters -/

/-- The stages of the link's plan at the full-size parameters begin with frFirst. -/
theorem home_stages : (p12Of frP).nums.stages = frFirst :: frRest := fr_cons

/-- Every position that the verifier queries in the prover's own trees is one at which the proximity
test's schedule opens that tree. -/
theorem home_want (Ds : List Fmt.Drawn) : WantTie dsF (sched frRest frFirst 6 1) Ds :=
  fr_wantTie frFirst frRest fr_cons Ds

/-- Each stored-table position that the prover's algorithm opens is one that the protocol's
challenges ask of that table. -/
theorem home_stored (Ds : List Fmt.Drawn) : StoredTie frP frS.P.T.a dsF xsF Ds := fr_storedTie Ds

/-- The public premises on sizes hold at the challenges of every verifier message. -/
theorem home_sizes (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsF))) :
    Sizes frP frS 97 (drawsOf (drawnSL (ckP .two) dsF ρ.2)) := fr_sizes ρ

/-! ## The honest data -/

/-- The honest data's keys are the instance's two keys, by definition. -/
theorem home_keys (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (x : RecFull × RecFull) :
    (homeIn b Z w x).keys = keysOf x := rfl

/-- The honest data's stored column at a position in range is the column in the input oracles'
symbol there. -/
theorem home_cols (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (x : RecFull × RecFull) (bb : Bool)
    (pos : ℕ) (h : pos < 2 ^ frS.P.T.a) :
    (homeIn b Z w x).y bb pos =
      ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd (homeExt b Z w) (posOf frS.P.T.a bb pos h)).2 := by
  show yCol frS.P.T.a (homeExt b Z w) bb pos = _
  unfold yCol posOf
  rw [dif_pos h]

/-- **At a valid private input and instance the honest data are Meant.** -/
theorem home_meant (b : PublicFiles → ℕ) (Z : PublicFiles) (ok : (homeR b Z).Index → Prop)
    (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop) (w : HomeWt b Z) (x : RecFull × RecFull)
    (hv : validLk (homeR b Z).protocol ok Gs w x) :
    Meant x (homeExt b Z w) (homeIn b Z w x).M₀ (homeIn b Z w x).M₁ := by
  obtain ⟨-, -, -, rfl⟩ := hv
  have h := meant_home b Z w.1 w.2.1.1 w.2.2.1 w.2.1.2 w.2.2.2 _ _ rfl rfl
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **The premise on the honest run**: at the last stage, the claim left at the base case is true at
the honest prover's last message, or the element sampled there is 0. -/
theorem home_claim (b : PublicFiles → ℕ) (Z : PublicFiles) (ok : (homeR b Z).Index → Prop)
    (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop) (w : HomeWt b Z) (x : RecFull × RecFull)
    (hv : validLk (homeR b Z).protocol ok Gs w x) (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsF))) :
    ∀ C, InPlaces frP frS C → ∀ e,
      linkEnd frP frS 97 (homeIn b Z w x) C (drawsOf (drawnSL (ckP .two) dsF ρ.2)) = some e →
      LamZero (drawsOf (drawnSL (ckP .two) dsF ρ.2)) e ∨ ClaimTrue (p12Of frP) e :=
  fr_claimPremise x (homeExt b Z w) _ _ (home_meant b Z ok Gs w x hv) ρ.2

/-! ## The link's protocol -/

/-- **Part of what PremW asks of the link's protocol besides a simulator: two counts and locality**,
at homeR b Z's own protocol structure: at most 62 positions read in each table, and a local
verifier. -/
theorem home_beside (b : PublicFiles → ℕ) (Z : PublicFiles) : LinkBeside (homeR b Z).protocol 62 62 :=
  ⟨(fr_linkCounts _ (dataAtFiles flashProveData Z).dec).1, (fr_linkCounts _ (dataAtFiles flashProveData Z).dec).2.1,
    (fr_linkCounts _ (dataAtFiles flashProveData Z).dec).2.2⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.home_beside
#print axioms OnBytes.LinkSim.AtHome.home_want
#print axioms OnBytes.LinkSim.AtHome.home_stored
#print axioms OnBytes.LinkSim.AtHome.home_sizes
#print axioms OnBytes.LinkSim.AtHome.home_keys
#print axioms OnBytes.LinkSim.AtHome.home_cols
#print axioms OnBytes.LinkSim.AtHome.home_meant
#print axioms OnBytes.LinkSim.AtHome.home_claim
