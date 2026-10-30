-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeIdle.lean: at explicit placeholder parameters, ten of the thirteen
hypotheses of completeOn_last (LastFits, Johnson/Goal/Conditions/HomeLast.lean) hold outright; the
other three, on the files, are taken as conditions.

What this file proves. lastFits_idle: for every b, all public files Z, every x₀ and all pp: if the
reader returns pp at Z, Z is in the goals' scope and the description's own Boolean test on the files
(protocolDataWellFormed) accepts, then LastFits (idleArgs b Z x₀) Z pp (idleAlpha b Z) holds. These three
conditions are the list's own clauses read, scope and live; the other ten clauses hold outright: no
proof of theirs takes one of the three as a premise. (honest names read, inside yesAt; it is proved
at every predicate Yes: honest_idle.) idleArgs is an explicit Lean term but for three variables: b
(the committer's coins are numbered from 0 to b Z), Z₀ (the files at whose salt length the
committer's bytes are cut; lastFits_idle takes Z₀ := Z) and x₀ (the instance where the builder
builds nothing). three_le_idleAlpha: the number idleAlpha b Z is at least 3, so completeOn_last
bounds nothing at these parameters (limit 1).

What it is for: a guard. A hypothesis that no parameters can satisfy compiles without a warning, and
a theorem under it is vacuous. By lastFits_idle the thirteen clauses do not contradict each other
wherever read, scope and live hold; where these are proved: Johnson/Goal/Conditions/HomeLast.lean,
limit 4. The guard stands at the description's own input homeR b Z, with its three interactive
protocols, not at a small example. (What it does not give: limits 1 and 3.)

What "idle" means. An idle prover is a placeholder: a value of the library's structure Honest
(Iop/InteractiveOracleProof.lean) whose abort set is everything (Bad and Hid are Set.univ). So every clause that
speaks of verifier messages outside the abort set holds vacuously. The Lean names keep the word.

The parameters (idleArgs).
  - The three provers (idleHs; idleRecs, Johnson/Prover/At/IdleAt.lean). Their input oracles are the
    encodings of the index, as HonFit asks. The key file's and the proof file's run idleW
    (Johnson/Prover/Print/IdleStrat.lean): fixed messages, except that the joining message and the
    third message hold the two run values that are stored in that prover's coin (Honest.Coin), and
    the proof file's front message holds the copy's number that the prover is given. The link's
    sends default messages (Strat.dflt). It is not the explicit link prover linkRec of
    Johnson/Prover/Link/LinkFrame.lean.
  - No OOD seed is set aside, and every fall (a further excepted set) is empty. ζ is 0, and pT, pL,
    pO are 1.
  - The two whole files' provers have coins CoinRuns Unit; κOf is kapToy and runs is runsToy
    (Johnson/Goal/Conditions/HomeTieMet.lean).
  - The three bounds on proof-of-work attempts are 0. The sampler's and the prover's numbers have
    one value each (B = N = 0; the commitment randomness is Unit).
  - In the raw value (the field raw of LastArgs) every byte string is empty and n is 0; in the byte
    coins the body for empty leaves is fillB b Z, the place 0, the path empty. The copy's encoding
    randomness r is padB b Z ((riDigits Z).e 0): entry 0 of the enumeration riDigits Z, that is
    every pad and tail 0 (by inspection: Johnson/Top/EnumDigits.lean); ra = 0 names the same value
    for the first table (EndArgs.pads). drawK tidies the byte strings
    (OnBytes/Prover/Print/Tidy.lean): missing bytes become 0, a run value that fails the format's
    test becomes the constant one32, and a short path is filled with zero digests.
  - The committer's bytes for each leaf are fitBytes m of the empty string, that is m zero bytes (by
    inspection), m the plan's salt length at Z₀.
  - The other fields: κ₀ is ((), (), ()), the shape sL of the copy's file's binding tree is ⟨0, 0⟩,
    and every byte string of the form fb is empty.

How it fits. Johnson/Goal/Conditions/HomeLast.lean states the list and the theorem under it.
lastFits_idle_named (AtFullSide/Home/HomeAtNamed.lean) removes the three conditions at the written
copies of the two named sets of files. The clause honest comes from honFit_idle_layoutsByPublicReading
(Johnson/Prover/At/IdleAt.lean), lawT and lawB from stratLaw_idle
(Johnson/Prover/Print/IdleStrat.lean), and tie from tie_toy
(Johnson/Goal/Conditions/HomeTieMet.lean).
This file states no goal.

Names (namespace FlashProve).
  idleHs, idleCoins, idleArgs   the three placeholder provers; the raw byte coins (empty strings);
    the parameters.
  honest_idle, lawT_idle, lawB_idle   the clauses honest (at every predicate Yes), lawT and lawB.
  idleAlpha, three_le_idleAlpha   the number at which the list holds; it is at least 3.
  lastFits_idle   the theorem.

Limits, the weightiest first.
  1. It says nothing on completeness. The number α at which the list is satisfied is at least 3, and
    a bound on a probability by such a number holds of every argument system. No verifier is said to
    accept anything.
  2. Which clauses hold vacuously, or by the choice of the sets alone: honest.accT, accL, accB
    (nothing is outside the abort sets) · honest.whT, whL, whB (everything is in the abort sets) ·
    honest.prZ (no seed is set aside) · honest.prT, prL, prB (a probability is at most 1) · number
    (α is the sum itself). Which do not: honest.num · honest.extT, extL, extB · lawT · lawB · tie ·
    bytes · flat · the three bounds.
  3. What this guard cannot see: a contradiction that runs through acceptance; and whether the list
    can be satisfied at small probabilities.
  4. The three clauses on the files (read, scope, live) are conditions here. b and x₀ stay variables
    (Z₀ is set to Z).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeLast
import Johnson.Goal.Conditions.HomeTieMet
import Johnson.Prover.At.IdleAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open OnBytes.Prover (ThreeProvers Falls HonFit alphaAll carryF)
open OnBytes.Prover.Print (ByteCoins fitBytes size_fitBytes)
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open LPFD.Full (saltG sTG sBG)
open Johnson.Prover.Print

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ)

/-- The three idle (placeholder) provers at the description's input homeR b Z. -/
def idleHs (Z : PublicFiles) : ThreeProvers (homeR b Z).protocol :=
  recsReBound (b Z) (idleRecs ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))

/-- Raw byte coins: empty strings. -/
def idleCoins (Z : PublicFiles) :
    ByteCoins (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits) :=
  ⟨.empty, .empty, .empty, fun _ _ _ _ => .empty, fillB b Z, 0, [], .empty⟩

/-- **The idle parameters.** Z₀: the files at whose salt length the committer's bytes are cut. -/
def idleArgs (Z₀ : PublicFiles) (x₀ : (Z : PublicFiles) → (homeR b Z).Instance) : LastArgs b Unit 0 0 where
  Hs := idleHs b
  Fs := fun Z => Falls.none (idleHs b Z)
  Zs := fun _ _ _ => ∅
  capT := fun _ _ => 0
  capL := fun _ _ => 0
  capB := fun _ _ => 0
  ρOf := fun _ => ()
  ra := fun _ _ => 0
  sb := fun _ _ => fitBytes (saltG (dataAtFiles flashProveData Z₀).G) .empty
  Kap₀ := fun _ => Unit × Unit × Unit
  raw := fun Z _ _ _ =>
    { r := padB b Z ((riDigits Z).e 0)
      own := fun _ => .empty
      n := 0
      κ₀ := ((), (), ())
      bT := idleCoins b Z
      bL := idleCoins b Z
      bB := idleCoins b Z }
  κOf := fun _ => kapToy
  runs := fun _ => runsToy
  sL := ⟨0, 0⟩
  x₀ := x₀
  fb := ⟨[], .empty, .empty, .empty, .empty, .empty⟩
  ζ := 0
  pT := 1
  pL := 1
  pO := 1

variable (Z : PublicFiles) (x₀ : (Z : PublicFiles) → (homeR b Z).Instance)

/-- The clause "honest": at every predicate Yes. -/
theorem honest_idle (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop) (d : (homeT b Z).D) :
    HonFit (idleHs b Z) (Falls.none _) (homeR b Z).queryLayout ((homeT b Z).Sd d) Yes (fun _ _ => ∅) 0 1 1
      1 :=
  honFit_reBound ((theTerms placeHolderCoins).T Z) (b Z) d
    (idleRecs ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])) (Falls.none _) Yes (fun _ _ => ∅) 0 1 1 1
    (honFit_idle_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] d Yes)

/-- The clause "lawT". -/
theorem lawT_idle (i : (homeR b Z).Index) (r : (homeR b Z).protocol.EncodingRandomness) (e₁ : (homeR b Z).protocol.OutOfDomainSeed)
    (κ : CoinRuns Unit × Unit × CoinRuns Unit) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
      (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty ((idleHs b Z).strats.T i r e₁ κ)
      (runsToy κ).1.1 (runsToy κ).1.2 :=
  stratLaw_idle (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
    (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty (front₀ (dataAtFiles flashProveData Z).G.rec₀)
    ⟨(join₀ (dataAtFiles flashProveData Z).G.rec₀).answers, _root_.Run.digToBytes κ.1.2.1⟩
    (_root_.Run.digToBytes κ.1.2.2)

/-- The clause "lawB". -/
theorem lawB_idle (i : (homeR b Z).Index) (r : (homeR b Z).protocol.EncodingRandomness) (e₂ : (homeR b Z).protocol.OutOfDomainSeed)
    (x : (homeR b Z).Instance) (n : ℕ) (κ : CoinRuns Unit × Unit × CoinRuns Unit) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ((idleHs b Z).strats.B i r e₂ x n κ)
      (runsToy κ).2.1 (runsToy κ).2.2 :=
  stratLaw_idle (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ⟨(front₀ (dataAtFiles flashProveData Z).G.z₀.2).answers, n⟩
    ⟨(join₀ (dataAtFiles flashProveData Z).G.z₀.2).answers, _root_.Run.digToBytes κ.2.2.2.1⟩
    (_root_.Run.digToBytes κ.2.2.2.2)

/-- The number at which the idle parameters satisfy LastFits: alphaAll at bounds on attempts 0, at ζ
= 0 and at pT = pL = pO = 1. -/
def idleAlpha : ℝ≥0∞ :=
  alphaAll (homeR b Z).queryLayout (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0 1 1 1

/-- It is at least 3: a bound on a probability by it says nothing. -/
theorem three_le_idleAlpha : 3 ≤ idleAlpha b Z := by
  unfold idleAlpha alphaAll
  refine le_trans (le_of_eq ?_) le_add_self
  norm_num

/-- **LastFits is satisfied at the idle parameters**, at an α of at least 3, where the bound says
nothing: its three clauses on the files are taken as conditions; the other ten hold outright. -/
theorem lastFits_idle {pp : Inst.Model.ScalesAndPolicy} (read : readFiles Z = .ok pp) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : LastFits (idleArgs b Z x₀) Z pp (idleAlpha b Z) where
  read := read
  scope := scope
  live := live
  honest := fun d => honest_idle b Z _ d
  lawT := fun _ _ e₁ κ => lawT_idle b Z _ _ e₁ κ
  lawB := fun _ r e₂ x n κ => lawB_idle b Z _ r e₂ x n κ
  tie := fun k r h => tie_toy k r h
  bytes := fun _ _ => size_fitBytes _ _
  flat := rfl
  capT := fun _ => Nat.pos_of_ne_zero (by decide)
  capL := fun _ => Nat.pos_of_ne_zero (by decide)
  capB := fun _ => Nat.pos_of_ne_zero (by decide)
  number := le_rfl

end FlashProve

