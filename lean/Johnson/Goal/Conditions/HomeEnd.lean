-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeEnd.lean: a reduction. If twelve named hypotheses (EndFits) hold, the
argument system with the library's verify() and a prover side given by parameters is complete on the
requests that can be served, with error at most α.

What this file proves. completeOn_end: let E be any value of the open parameters (the structure
EndArgs), Z public files, pp parsed parameters, Yes any predicate on pairs of an index and an
instance, and α a number. If EndFits E Z pp Yes α holds, then the argument system that is built from
E at Z is complete on the requests that can be served, with error at most α (CompleteOn,
VerifiableInference/Steps.lean; CanServe, VerifiableInference/CanServe.lean). It is a reduction, for
all E and every Yes. Johnson/Goal/Conditions/HomeLast.lean has the sharper form (completeOn_last).
Its head tells what CompleteOn says in words, which system this is, and which hypotheses are proved:
read it first.
No hypothesis assumes that verify() accepts, or that the compiled verifier (verifyAtKeyRoot) accepts. Three
fields of the one clause honest assume that an interactive verifier accepts (accT, accL, accB). The
way from there to verify() is proved in Lean, in two steps, which home_yes
(Johnson/Prover/Home/Yes.lean) joins.
  1. all_good (Johnson/Prover/All/Good.lean), under its own conditions, speaks outside an event
     whose probability allY_law (Johnson/Prover/All/Law.lean) bounds by the sum of the error terms.
     There the typed runs (the compiled prover's runs over typed oracles) yield a proof with the
     properties Ends, the three interactive verifiers accept, the test on the copy's number accepts,
     and the compiled verifier accepts at the committer's own key.
  2. printed_end, in this file: under EndFits, for a served request with the model's own output,
     these facts imply that verify() accepts the printed form (the proof as bytes), at the
     commitment that is the digest of the committer's own key. Of the three interactive verifiers'
     accepts it takes the key file's and the proof file's as premises (aT, aB), not the link's.
     EndFits is a premise whole, so accL stands in it; of EndFits the proof uses scope, live,
     served, good, lawT and lawB, not honest (by inspection). The printer is an explicit Lean term:
     printB (Johnson/Prover/At/PrintedBound.lean) at the prover's coins.
The prover's coins are a value of the structure Draw (Johnson/Prover/All/Defs.lean): the copy's
encoding randomness r, its salts s and number n; the three interactive provers' coins κ; the three
compiled runs' coins coT, coL, coB. They are free variables here: draw asks lengths, good ties coT,
coL, coB to the byte coins (parameters too), lawT and lawB read κ (lawB r and n too); no clause puts
a distribution on them.

The twelve hypotheses (EndFits), at one Z.
  read, scope, live: the reader returns pp at Z; Z is in the goals' scope (InScope); the
    description's own Boolean test on the files (protocolDataWellFormed) accepts.
  served: for every served request with the model's own output, the input's builder builds the
    instance E.xOf Z p o, and Yes holds of the weights' index and that instance.
  honest: HonFit (Johnson/Prover/All/OfHonest.lean) at Yes, at every value d of the public reading:
    the completeness of the system's three interactive protocols, as a hypothesis, and the largest.
    Johnson/Goal/Conditions/HomeLast.lean tells its fourteen fields, and that the link's four are
    proved for the explicit link prover, under linkFits_at's conditions.
  bytes: for each leaf, the commitment randomness holds as many bytes as the plan's salt has. A
    length alone.
  draw: every value of the prover's coins (E.drawOf Z d ρ a) has the lengths that the compiled runs
    ask (DrawFit, Johnson/Prover/All/Yes.lean). Lengths, and one bound on a number (slot) in each of
    the three runs' coins.
  good: GoodOwesB (Johnson/Prover/At/PrintedBound.lean), at all weights, every t and a, and every
    hash function. The fields coT, coL, coB of the prover's coins are those made of the byte coins,
    and these can be printed. The configuration's digest has 32 bytes, and the copy's file's binding
    tree has one leaf. The bounds on attempts, the depths, the widths and the copy's number are
    below 2^64. The committer's and the copy's tables are as the printer asks, at that digest
    (TableOwes).
  lawT, lawB: StratLaw (Johnson/Prover/Print/StratLaw.lean) of the key file's and of the proof
    file's strategy, at the field κ of the prover's coins and at the byte coins' two run values, at
    every seed.
  carried: the parameter carry, which runs a typed program over the one hash function, returns the
    typed runs' value.
  number: the sum of the error terms (alphaAll, Johnson/Prover/All/Law.lean) is at most α.

How it fits. completeOn_end_of calls completeOn_member_of
(Johnson/Goal/Conditions/HomeAtWider.lean), the same conclusion from a more general list. It proves
that list's premises from EndFits: the commitment's value (commit_member), the bounds on the
excepted sets (small_of_honest, Johnson/Prover/All/OfHonest.lean) and JoinRest
(Johnson/Prover/Home/Letters.lean; joinRest_end), whose field printed comes from printed_end and
printed_home_law (Johnson/Prover/At/PrintedLaw.lean). The test on sizes that the printer needs
(wordsFitAt, Johnson/Goal/Meaning/PublicSizesAt.lean) is no hypothesis: it follows from scope and
live (wordsFitAt_the, Johnson/Goal/Meaning/WordsFitAtThe.lean).
Johnson/Goal/Conditions/HomeLast.lean (endFits_of_last, completeOn_last) uses completeOn_end.
This file states no goal. It defines EndFits, completeOn_end's one premise.

Names (namespace FlashProve).
  EndArgs   the open parameters: three provers (values of Honest), falls, seeds set aside, bounds on
    attempts, ρOf, ra, sb (commitment randomness), drawOf (the prover's coins), three byte coins,
    sL, xOf, carry, fb, four numbers.
  kapOf, EndArgs.pads   the type of the three interactive provers' coins; the first table's encoding
    randomness (EncodingRandomness: pads and tails) that the commitment randomness names through ra.
  EndArgs.args, EndFits   the parameters of completeOn_member_of (HomeArgs) at E, with the explicit
    printer; the twelve hypotheses.
  verify_end   where verify() at descriptionOfDataOnBytes flashProveData accepts, at one hash function, so does the
    system's verifier.
  completeOn_end_of, completeOn_end   the theorem with b and the generator gen as parameters, under
    hgen; the theorem at committerCoinCountLessOne and namedGen.

Limits, the weightiest first.
  1. Under Johnson/ and AtFullSide/ EndFits is concluded through endFits_of_last alone, so at the
    placeholders of Johnson/Goal/Conditions/HomeLast.lean, limit 1, at an α that is at least 3,
    where the bound says nothing. This file defines no prover, no prover's coins and no carry: they
    are parameters of EndArgs. HomeLast.lean defines carry, and the prover's coins as a function of
    a raw value that stays a parameter; the explicit link prover linkRec is defined in
    Johnson/Prover/Link/LinkFrame.lean (the placeholders' link prover is not that one:
    Johnson/Goal/Conditions/HomeIdle.lean).
  2. Not settled: served and honest both constrain the one parameter Yes. served puts every
    served request with the model's output into Yes; honest asks acceptance at all of Yes. CanServe
    admits every value that the integer model admits (16 bits, up to 32,767). If the description's
    lookups admit fewer values, served puts into Yes an instance at which an interactive verifier
    accepts nothing. honest can hold at such a Yes only if the abort set and the fall together, or
    the seeds set aside, have probability 1 there; number then forces α ≥ 1, and the statement
    bounds nothing. (Argued on paper, not proved. At a large enough α, at least 3, the list is
    satisfied whatever the lookups admit, where read, scope and live hold: lastFits_idle,
    Johnson/Goal/Conditions/HomeIdle.lean.) This file does not prove whether the lookups admit fewer
    values. What hangs on it: if they do, the theorem stays true and gives no bound below 1 at that
    Z, whatever provers are given (argued, as above); if they do not, this question falls away (the
    ten other fields stay unshown). A theorem that bears on it, on the library's tables and not on
    the
    description's lookups: means_of_served (Johnson/Goal/Meaning/ServedMeans.lean; see that file's
    limits). served is proved at an explicit instance and the explicit Yes yesAt, which is not empty
    (served_home, yesAt_met, Johnson/Goal/Conditions/HomeServed.lean, in scope); the question then
    rests in honest alone.
  3. draw is asked at every d and ρ: more than is used; it is the form of JoinRest's field. lawT and
    lawB are asked at every seed, at all weights and (lawB) at all requests, the unserved too: more
    than printed_home_law uses. They can be satisfied by the interactive provers' coins' type alone,
    not by honest conduct (how: HomeLast.lean, limit 6).
  4. Limits 2, 3, 4, 7 and 8 of Johnson/Goal/Conditions/HomeLast.lean apply here too (2: the
    prover's side is given by parameters; 3: not the goals' G3'pol; 4: where live is proved; 7: no
    distribution on any randomness; nothing says that the copy's encoding randomness differs from
    the first table's; 8: the limits of the family theWider).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeAtWider
import Johnson.Prover.At.PrintedLaw
import Johnson.Prover.At.HomeMore
import Johnson.Prover.All.OfHonest
import Johnson.Goal.Meaning.PublicSAt
import Johnson.Goal.Meaning.WordsFitAtThe

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
open OnBytes.Prover (Strats Draw Raw Bads ThreeProvers Falls HonFit DrawFit Ends pack runsAt alphaAll
  JoinRest)
open OnBytes.Prover.Print (ByteCoins)
open TypedOracleCompiler.Compile.Batch (typedOracleFamily)
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open Johnson.Prover.Print

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- The type of the three interactive provers' coins. -/
abbrev kapOf {b : PublicFiles → ℕ} (Hs : (Z : PublicFiles) → ThreeProvers (homeR b Z).protocol) (Z : PublicFiles) : Type :=
  (Hs Z).T.Coin × (Hs Z).Lk.Coin × (Hs Z).B.Coin

/-- **The open parameters of completeOn_end**: all that this file does not fix. -/
structure EndArgs (b : PublicFiles → ℕ) (Rand : Type) (B N : ℕ) where
  /-- the three interactive protocols' provers (ThreeProvers: three values of Honest): strategies and abort
  sets -/
  Hs : (Z : PublicFiles) → ThreeProvers (homeR b Z).protocol
  /-- the falls (Johnson/Prover/All/OfHonest.lean): for each private input, instance and coin of a
  prover a further set of lists of verifier messages at which no acceptance is asked -/
  Fs : (Z : PublicFiles) → Falls (Hs Z)
  /-- the seeds that are set aside -/
  Zs : (Z : PublicFiles) → (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed
  capT : PublicFiles → ℕ → ℕ
  capL : PublicFiles → ℕ → ℕ
  capB : PublicFiles → ℕ → ℕ
  ρOf : Fin (B + 1) → Rand
  ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1)
  sb : Rand → ℕ → ByteArray
  /-- the prover's coins (Draw), as a function of the public reading, the commitment randomness and
  the prover's number -/
  drawOf : (Z : PublicFiles) → (homeT b Z).D → Rand → Fin (N + 1) →
    Draw 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits (kapOf Hs Z)
  /-- the three compiled runs' coins, as bytes -/
  bcT : (Z : PublicFiles) → (homeT b Z).D → Rand → Fin (N + 1) →
    ByteCoins (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  bcL : (Z : PublicFiles) → (homeT b Z).D → Rand → Fin (N + 1) →
    ByteCoins (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  bcB : (Z : PublicFiles) → (homeT b Z).D → Rand → Fin (N + 1) →
    ByteCoins (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  /-- the shape of the copy's file's binding tree -/
  sL : OnBytes.Params.LinBindingShape
  xOf : (Z : PublicFiles) → List Token → List Token → (homeR b Z).Instance
  carry : (Z : PublicFiles) → (d : (homeT b Z).D) →
    OComp (typedOracleFamily 256 (homeR b Z).queryLayout.K
        (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits))
      (Raw 256 (homeR b Z).protocol (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits) →
    OComp (rom 256) (Raw 256 (homeR b Z).protocol (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  /-- what the printer hands over where a search has run out -/
  fb : FormBytes
  ζ : ℝ≥0∞
  pT : ℝ≥0∞
  pL : ℝ≥0∞
  pO : ℝ≥0∞

variable {b : PublicFiles → ℕ} {Rand : Type} {B N : ℕ} (E : EndArgs b Rand B N)

/-- The first table's encoding randomness (EncodingRandomness: pads and tails) that the commitment randomness names
through ra, read at the input at b. -/
def EndArgs.pads (Z : PublicFiles) (ρ : Rand) : (homeR b Z).protocol.EncodingRandomness := padB b Z ((riDigits Z).e (E.ra Z ρ))

/-- **HomeArgs at these parameters**: the strategies are the three provers'; the sets are the
provers' abort sets, each with the fall at the field κ of the prover's coins, and the seeds set
aside; the printer is an explicit term: printB (Johnson/Prover/At/PrintedBound.lean) at the prover's
coins. -/
def EndArgs.args : HomeArgs b Rand B N where
  Kap := kapOf E.Hs
  st := fun Z => (E.Hs Z).strats
  capT := E.capT
  capL := E.capL
  capB := E.capB
  ρOf := E.ρOf
  ra := E.ra
  sb := E.sb
  drawOf := E.drawOf
  xOf := E.xOf
  carry := E.carry
  print := fun Z s w ρ _ _ a d y =>
    printB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) (backB b Z s w) (E.pads Z ρ) (E.drawOf Z d ρ a) E.fb y
  Bs := fun Z s w p o t a d => (E.Hs Z).bads (E.Fs Z) (E.Zs Z) (backB b Z s w) (E.pads Z (E.ρOf t))
    (E.drawOf Z d (E.ρOf t) a).r (E.xOf Z p o) (E.drawOf Z d (E.ρOf t) a).n
    (E.drawOf Z d (E.ρOf t) a).κ
  ζ₁ := E.ζ
  ζ₂ := E.ζ
  δT := E.pT
  δL := E.pL
  δB := E.pO

/-- **The twelve hypotheses of completeOn_end**, at one Z. Yes: any predicate on an index and an
instance; served and honest constrain it. -/
structure EndFits (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (α : ℝ≥0∞) : Prop where
  /-- the files -/
  read : readFiles Z = .ok pp
  scope : InScope Z = true
  live : protocolDataWellFormed (asDescriptionFiles Z) = true
  /-- the request: a served request with the model's own output is built, and Yes holds of it -/
  served : ∀ w p o, CanServe (settingsOfRead pp) w p o →
    ModelOutput (settingsOfRead pp) w p o →
    (homeR b Z).buildInstance (p, o) [] = some (E.xOf Z p o) ∧
      Yes (backB b Z (settingsOfRead pp) w) (E.xOf Z p o)
  /-- the three provers and the falls: acceptance, and the probabilities of what is excepted -/
  honest : ∀ d, HonFit (E.Hs Z) (E.Fs Z) (homeR b Z).queryLayout ((homeT b Z).Sd d) Yes (E.Zs Z) E.ζ E.pT
    E.pL E.pO
  /-- the commitment randomness: as many bytes for each leaf as the plan's salt has -/
  bytes : ∀ ρ j, (E.sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G
  /-- The clauses on the prover's coins. (1) Every value of drawOf has the lengths that the compiled
  runs ask -/
  draw : ∀ d ρ a, DrawFit (homeR b Z).queryLayout (homeR b Z).compilerParameters (E.drawOf Z d ρ a)
  /-- (2) At all weights, every t and a, and every hash function (no value is excepted): the fields
  coT, coL, coB are those made of the byte coins; these can be printed; the bounds on attempts,
  depths, widths and the copy's number are below 2^64; the committer's and the copy's tables are as
  the printer asks, at the configuration's digest -/
  good : ∀ w t a (hash : Hash),
    GoodOwesB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) (_root_.Run.digToBytes (cAt Z hash))
      (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) E.sL
      (E.bcT Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a)
      (E.bcL Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a)
      (E.bcB Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a)
      (E.capT Z) (E.capL Z) (E.capB Z) (backB b Z (settingsOfRead pp) w) (E.pads Z (E.ρOf t))
      (saltsAt ((homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash))) (E.sb (E.ρOf t)))
      (E.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a)
  /-- (3) One value of the prover's coins holds κ beside what the byte coins make: what the printer
  asks of the key file's and of the proof file's strategy, at its field κ and at the byte coins' two
  run values, at every seed -/
  lawT : ∀ w t a (hash : Hash) e₁,
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
      (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty
      ((E.Hs Z).strats.T (backB b Z (settingsOfRead pp) w) (E.pads Z (E.ρOf t)) e₁
        (E.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).κ)
      (E.bcT Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).run2
      (E.bcT Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).run3
  lawB : ∀ w p o t a (hash : Hash) e₂,
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      ((E.Hs Z).strats.B (backB b Z (settingsOfRead pp) w)
        (E.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).r e₂ (E.xOf Z p o)
        (E.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).n
        (E.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).κ)
      (E.bcB Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).run2
      (E.bcB Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (E.ρOf t) a).run3
  /-- carry, which runs a typed program over the hash function, returns the typed runs' value -/
  carried : ∀ w ρ p o a d g,
    (E.carry Z d (runsAt (homeT b Z) (fillB b Z) (E.Hs Z).strats (E.capT Z) (E.capL Z) (E.capB Z) d
      (backB b Z (settingsOfRead pp) w, E.pads Z ρ, saltsAt ((homeT b Z).part d) (E.sb ρ))
      (E.xOf Z p o) (E.drawOf Z d ρ a))).det g =
    (runsAt (homeT b Z) (fillB b Z) (E.Hs Z).strats (E.capT Z) (E.capL Z) (E.capB Z) d
      (backB b Z (settingsOfRead pp) w, E.pads Z ρ, saltsAt ((homeT b Z).part d) (E.sb ρ))
      (E.xOf Z p o) (E.drawOf Z d ρ a)).det (readBlocks ((homeT b Z).m d) g)
  /-- the sum of the error terms is at most α -/
  number : alphaAll (homeR b Z).queryLayout (E.capT Z) (E.capL Z) (E.capB Z) E.ζ E.ζ E.pT E.pL E.pO ≤ α

section
variable (gen : (Z : PublicFiles) → Rand → Digest → Digest → Fin (b Z + 1)) {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
  {Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop} {α : ℝ≥0∞}

local notation "He" => homeH E.args gen Z (settingsOfRead pp)
local notation "Se" => systemOfRecord (atSecondHashFunction (member E.args gen)) Z (settingsOfRead pp)

/-- Where verify() at flashProveDescription (that is `descriptionOfDataOnBytes flashProveData`) accepts a commitment and a form at one hash
function, so does the system's verifier: by verify_record
(Johnson/Goal/Conditions/WiderComplete.lean). -/
theorem verify_end (X : Commitment) (p o : List Token) (Y : FormBytes) (hash : Hash)
    (h : (verify flashProveDescription Z (flashProveDescription.parse Z) X p o Y).evaluate hash = true) :
    ((Se).verify X p o Y).evaluate hash = true :=
  (congrArg (fun v => (v X p o Y).evaluate hash)
    (verify_record (homeK E.args) ⟨b, gen⟩ Z (settingsOfRead pp))).trans h

/- Lean compares these by their names: left open, it walks the programs' trees and its stack runs
over. A bad result on Lean: with holes for arguments and Rom.OComp.det open, the field "printed"
ended in "Stack overflow detected" (exit 134). So printed_end writes every argument out, and these
nine names are made irreducible for this section. -/
attribute [local irreducible] Rom.OComp.det OnBytes.Prover.runsAt OnBytes.Prover.pack
  Johnson.Prover.Print.printB Rom.readBlocks TypedOracleCompiler.Compile.Batch.Cms.committerAtFixedCoins
  TypedOracleCompiler.Compile.Batch.Cms.verifyAtKeyRoot ZKCP.digestUnder saltsAt

section
variable (w : ModelWeights (settingsOfRead pp)) (p o : List Token) (t : Fin (B + 1))
  (a : Fin (N + 1)) (hash : Hash)

/- Short names, for this section alone (above: He, the parameters homeH of the general lemma; Se,
the goals' system at the member): the public reading's value · the typed oracles read out through
its coding · the index · the first table's encoding randomness (E.pads) · the committer's salts ·
the prover's coins · the typed runs' value. -/
local notation "𝕕" => Rom.OComp.det (_root_.Run.famOne hash) (LayoutsByPublicReading.Pub (homeT b Z))
local notation "𝕘" => readBlocks (LayoutsByPublicReading.m (homeT b Z) 𝕕) (_root_.Run.famOne hash)
local notation "𝕚" => backB b Z (settingsOfRead pp) w
local notation "𝕣" => EndArgs.pads E Z (EndArgs.ρOf E t)
local notation "𝕤" => saltsAt (LayoutsByPublicReading.part (homeT b Z) 𝕕) (EndArgs.sb E (EndArgs.ρOf E t))
local notation "𝕨" => EndArgs.drawOf E Z 𝕕 (EndArgs.ρOf E t) a
local notation "𝕪" => Rom.OComp.det 𝕘 (runsAt (homeT b Z) (fillB b Z) (ThreeProvers.strats (EndArgs.Hs E Z))
  (EndArgs.capT E Z) (EndArgs.capL E Z) (EndArgs.capB E Z) 𝕕 (𝕚, 𝕣, 𝕤) (EndArgs.xOf E Z p o) 𝕨)

/-- **Where the typed runs yield a proof, verify() accepts the printed form**: printed_home_law
(Johnson/Prover/At/PrintedLaw.lean) at these parameters: the reading by pub_det_home
(Johnson/Prover/At/HomeAt.lean), PublicS by publicS_built (Johnson/Goal/Meaning/PublicSAt.lean). -/
theorem printed_end (F : EndFits E Z pp Yes α) (hd : CanServe (settingsOfRead pp) w p o)
    (hm : ModelOutput (settingsOfRead pp) w p o)
    (π : TypedOracleCompiler.Compile.Batch.Cms.OfflineLinkOnlineProof 256 (homeR b Z).protocol (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (e₁ e₂ : (homeR b Z).protocol.OutOfDomainSeed) (τT : _root_.Iop.Tr (homeR b Z).protocol.offline.shape)
    (τL : _root_.Iop.Tr (homeR b Z).protocol.link.shape) (τB : _root_.Iop.Tr (homeR b Z).protocol.onlineBatch.loc.shape)
    (hp : pack 𝕚 𝕨 𝕪 = .ok (π, e₁, e₂, τT, τL, τB))
    (hE : Ends (homeR b Z).queryLayout ((homeT b Z).Sd 𝕕) ((homeT b Z).cA 𝕕) (homeR b Z).fixedSample (fillB b Z)
      (E.Hs Z).strats (E.capT Z) (E.capL Z) (E.capB Z) 𝕘 𝕚 𝕣 𝕤 (E.xOf Z p o) 𝕨 π e₁ e₂ τT τL τB)
    (aT : (homeR b Z).protocol.offline.accept ((homeR b Z).protocol.recOf 𝕚 𝕣 e₁) ((homeR b Z).protocol.encodeIndex 𝕚 𝕣) τT = true)
    (aB : (homeR b Z).protocol.onlineBatch.loc.accept (E.xOf Z p o, (homeR b Z).protocol.recOf 𝕚 (𝕨).r e₂)
      ((homeR b Z).protocol.encodeIndex 𝕚 (𝕨).r) τB = true)
    (hn : ((homeT b Z).Sd 𝕕).num (𝕨).n τB.plains = true)
    (hv : (TypedOracleCompiler.Compile.Batch.Cms.verifyAtKeyRoot (homeR b Z).queryLayout ((homeT b Z).Sd 𝕕) ((homeT b Z).cA 𝕕)
      (homeR b Z).fixedSample (homeR b Z).compilerParameters
      ((TypedOracleCompiler.Compile.Batch.Cms.committerAtFixedCoins (homeR b Z).queryLayout ((homeT b Z).Sd 𝕕) (fillB b Z) 𝕚 𝕣
        𝕤).det 𝕘).1 (E.xOf Z p o) π).det 𝕘 = true) :
    (verify flashProveDescription Z (flashProveDescription.parse Z)
      (ZKCP.digestUnder hash (homeT b Z).encT ((homeT b Z).part 𝕕,
        ((TypedOracleCompiler.Compile.Batch.Cms.committerAtFixedCoins (homeR b Z).queryLayout ((homeT b Z).Sd 𝕕) (fillB b Z) 𝕚 𝕣
          𝕤).det 𝕘).1)) p o
      (printB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) 𝕚 𝕣 𝕨 E.fb 𝕪)).evaluate hash = true :=
  printed_home_law b Z hash 𝕕 (pub_det_home b Z hash) F.scope p o (fillB b Z) (E.Hs Z).strats
    (E.capT Z) (E.capL Z) (E.capB Z) 𝕚 𝕣 𝕤 (E.xOf Z p o) 𝕨 π e₁ e₂ τT τL τB
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) E.sL (E.bcT Z 𝕕 (E.ρOf t) a) (E.bcL Z 𝕕 (E.ρOf t) a)
    (E.bcB Z 𝕕 (E.ρOf t) a) E.fb
    (Meaning.publicS_built Z F.live (Meaning.wordsFitAt_the Z F.scope F.live)).1 hp hE aT aB
    (F.good w t a hash) (F.lawT w t a hash e₁) (F.lawB w p o t a hash e₂) hn
    (F.served w p o hd hm).1 hv

end

set_option maxHeartbeats 1600000 in
/-- **JoinRest (Johnson/Prover/Home/Letters.lean) from EndFits.** -/
theorem joinRest_end (F : EndFits E Z pp Yes α) :
    JoinRest (He) (CanServe (settingsOfRead pp)) where
  carry_det := F.carried
  wires := wires_member Z
  draw := F.draw
  acc := fun w p o hd hm _ _ d =>
    OnBytes.Prover.accAt_of_honest (F.honest d) _ _ _ _ (F.served w p o hd hm).2
  printed := fun w p o hd hm t a hash π e₁ e₂ τT τL τB hp hE aT _ aB hn hv =>
    verify_end E gen _ p o _ hash
      (printed_end E w p o t a hash F hd hm π e₁ e₂ τT τL τB hp hE aT aB hn hv)

set_option maxHeartbeats 1600000 in
/-- **CompleteOn, from EndFits, of the system with the library's verify() and a prover side given by
parameters** (HomeLast.lean, limit 2), with b and gen as parameters, under hgen: the generator's
number is the pair's. -/
theorem completeOn_end_of
    (hgen : ∀ ρ c I, (gen Z ρ c I).val = (E.ra Z ρ).val + ((riDigits Z).n + 1) *
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt c (E.sb ρ))).val)
    (F : EndFits E Z pp Yes α) : CompleteOn (Se) (CanServe (settingsOfRead pp)) α :=
  completeOn_member_of E.args gen Z F.read α F.bytes
    (commit_member E.args gen Z F.read F.bytes hgen)
    (fun w p o hd hm _ _ d =>
      OnBytes.Prover.small_of_honest (F.honest d) _ _ _ _ _ _ (F.served w p o hd hm).2)
    F.number (joinRest_end E gen F)

end

/-- **CompleteOn, from EndFits, of the system with the library's verify() and a prover side given by
parameters** (HomeLast.lean, limit 2): the main theorem, at committerCoinCountLessOne and namedGen. -/
theorem completeOn_end {Rand : Type} {B N : ℕ} (E : EndArgs committerCoinCountLessOne Rand B N) {Z : PublicFiles}
    {pp : Inst.Model.ScalesAndPolicy} {Yes : (homeR committerCoinCountLessOne Z).Index → (homeR committerCoinCountLessOne Z).Instance → Prop} {α : ℝ≥0∞}
    (F : EndFits E Z pp Yes α) :
    CompleteOn (systemOfRecord (atSecondHashFunction (member E.args (namedGen E.ra E.sb))) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp)) α :=
  completeOn_end_of E (namedGen E.ra E.sb) (fun _ _ _ => rfl) F

end FlashProve

#print axioms FlashProve.verify_end
#print axioms FlashProve.printed_end
#print axioms FlashProve.joinRest_end
#print axioms FlashProve.completeOn_end_of
#print axioms FlashProve.completeOn_end
