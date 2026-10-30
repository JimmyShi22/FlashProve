-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeLast.lean: a reduction. If thirteen named hypotheses (LastFits) hold,
the argument system with the library's verify() and a prover side given by parameters is complete on
the requests that can be served, with error at most α.

What this file proves. completeOn_last: let A be any value of the open parameters (the structure
LastArgs), Z public files, pp parsed parameters, and α a number. If LastFits A Z pp α holds, then
the argument system that is built from A at Z is complete on the requests that can be served, with
error at most α (CompleteOn, VerifiableInference/Steps.lean; CanServe,
VerifiableInference/CanServe.lean). Spelled out: take any weights and any request in CanServe whose
output is the model's own. Sample the commitment randomness, commit, prove and verify. Then the
verifier rejects with probability at most α, over a hash function sampled uniformly at random and
the random choices of the sampler and the prover (Prob, VerifiableInference/RandomOracleModel.lean).
It is a reduction, for all A: from the completeness of three interactive protocols to the
completeness of the compiled system on bytes, under the list's other clauses. No hypothesis assumes
that verify() accepts, or that the compiled verifier accepts. Three fields of the one clause honest
assume that an interactive verifier accepts (accT, accL, accB). A bound below 1 follows once
parameters A with provers that run the key file's and the proof file's protocols are given that
satisfy the list at a small α (whether such A exist: limit 5).
Which system. Its verifier is verify() at the description descriptionOfDataOnBytes flashProveData, with that description's
own parser (verify_record, Johnson/Goal/Conditions/WiderComplete.lean). That is the description
which the library's goals read: atSecondHashFunction theDescription = descriptionOfDataOnBytes flashProveData (theDescription_eq,
Johnson/Goal/Description/Description.lean). What is built from A is the sampler, the committer's
coins and the prover (limit 2).

What is proved of the list, and what is open.
  - Proved: honest's four fields on the link (extL, whL, accL, prL with pL = 0), for the explicit
    link prover linkRec (Johnson/Prover/Link/LinkFrame.lean) at linkNext
    (Johnson/Prover/Link/LinkAll.lean): linkFits_at (Johnson/Goal/Conditions/LinkFitsAt.lean), if Z
    is in scope, protocolDataWellFormed accepts and the fall at the link is empty.
  - Proved: read, scope and live, at the files of limit 4; capT, capL and capB at explicit bounds,
    if Z is in scope and protocolDataWellFormed accepts (caps_home, Johnson/Goal/Conditions/NumberAtHome.lean); tie
    at two explicit maps, over any three types of further coins (tie_toy,
    Johnson/Goal/Conditions/HomeTieMet.lean).
  - Proved: all thirteen together, where read, scope and live hold, at idle parameters and an
    α that is at least 3 (limit 1).
  - Not shown at homeR b Z: honest's other ten fields (extT, extB, whT, whB, accT, accB, prT, prB,
  prZ,
    num) at provers that run the key file's and the proof file's protocols; lawT, lawB and tie at
    these; a small α.

The thirteen hypotheses (LastFits), at one Z.
  read, scope, live: the reader returns pp at Z; Z is in the goals' scope (InScope); the
    description's own Boolean test on the files (protocolDataWellFormed) accepts.
  honest: HonFit (Johnson/Prover/All/OfHonest.lean) at the set of true instances yesAt, at every
    value d of the public reading. It is the completeness of the system's three interactive
    protocols, as a hypothesis: the key file's (T), the link proof, here called the link (L), and
    the proof file's (B). A holds a prover for each (a value of the library's structure Honest,
    Iop/InteractiveOracleProof.lean) and a further family of excepted sets for each (a fall). For each of the three
    HonFit asks four things. (ext) The prover's input oracles are the encoding of its index; for the
    link, the two encodings. (acc) Take an index with a true instance in yesAt, any value of the
    encoding randomness (the encoder's second argument, HolographicProtocol's type EncodingRandomness; a free variable here), every
    coin c of that interactive prover (Honest.Coin), and an out-of-domain (OOD) seed that is not set
    aside. Then the interactive verifier accepts every transcript that is the prover's own run but
    for nonces, passes all proof-of-work checks, and has its verifier messages outside the prover's
    abort set (withheld) and the fall. (pr) For the same indices, at every seed and each fixed coin,
    abort set and fall together have probability at most pT, pL, pO over the verifier's messages.
    (wh) They contain a list of verifier messages whenever they contain it with its proof-of-work
    bits set to 0. Two fields more: the OOD seeds that are set aside have probability at most ζ
    (prZ), and the proof file's prover sends the copy's number that it is given (num). This is the
    largest hypothesis.
  lawT, lawB: StratLaw (Johnson/Prover/Print/StratLaw.lean) of T's and of B's strategy: at every
    coin κ the strategy sends the two run values that are read off κ, and its words and columns can
    be printed. A run value is a byte string that a strategy sends in its joining message or in its
    third message (StratLaw.run2, run3).
  tie: four run values that fit (Runs4.Fit, Johnson/Prover/Print/DrawOwes.lean) can be read back off
    the three interactive provers' coins.
  bytes: for each leaf, the commitment randomness holds as many bytes as the plan's salt has. A
    length alone.
  flat, capT, capL, capB: the copy's file's binding tree has one leaf; the three bounds on
    proof-of-work attempts are below 2^64.
  number: the sum of the error terms (alphaAll, Johnson/Prover/All/Law.lean) is at most α: the
    failure of the three proof-of-work searches, ζ twice, and pT, pL, pO.

How it fits. EndFits (Johnson/Goal/Conditions/HomeEnd.lean) is a list of twelve clauses with more
parameters, and completeOn_end proves the same conclusion from it. LastArgs.endArgs gives some of
these parameters as explicit Lean terms; its docstring lists them. With these, endFits_of_last
proves four of EndFits' clauses from this list's clauses: served (served_home), draw
(drawFit_drawK_home), good (good_last) and carried (det_home). It derives EndFits' lawT and lawB
from this list's lawT, lawB and tie (runs_last), and passes six clauses on unchanged. Five clauses
are this list's own: tie, flat, capT, capL, capB.
draw and good hold at every raw value (the field raw of LastArgs) because drawAt rewrites it: bytes
are cut or filled with 0, a failing run value becomes one32, numbers are reduced, a short path is
filled with zero digests (OnBytes/Prover/Print/Tidy.lean). Empty strings pass.
This file states no goal. It defines LastFits, completeOn_last's one premise.

Names (namespace FlashProve).
  LastArgs, LastArgs.endArgs, LastFits   the open parameters; EndFits' parameters (EndArgs) at them;
    the thirteen hypotheses.
  runs_last   under tie, the four run values of the byte coins are read off the field κ of the
    prover's coins as drawK builds them.
  good_last, endFits_of_last   EndFits' clause good, and all of EndFits, from LastFits.
  completeOn_last_of   the theorem with b (the committer's coins are numbered from 0 to b Z) and the
    generator gen as parameters, under hgen.
  completeOn_last   the theorem, at committerCoinCountLessOne and namedGen.

Limits, the weightiest first.
  1. Under Johnson/ and AtFullSide/ every theorem that concludes LastFits either takes the list
    itself as a premise, in this form or another, or does so at placeholder provers (lastFits_idle,
    Johnson/Goal/Conditions/HomeIdle.lean, with read, scope and live as its conditions;
    lastFits_idle_named, AtFullSide/Home/HomeAtNamed.lean, without them, at the written copies of
    the two named sets of files). Their three provers abort at every verifier message, and the list
    holds at an α that is at least 3, where the bound says nothing. That rules out clauses that
    contradict each other outright. It cannot see a contradiction that runs through acceptance, nor
    whether the list holds at an α below 1 (HomeIdle.lean, limit 3). Under Johnson/Prover/,
    Johnson/Goal/ and AtFullSide/ the only provers that are defined for the key file's or the proof
    file's protocol are placeholders (idleRecs, Johnson/Prover/At/IdleAt.lean; the silent
    theProvers, Johnson/Goal/Description/Named.lean), so no A there joins the explicit link prover
    with provers that run the other two protocols.
  2. The committer's and the prover's side is given by parameters. The description is member
    A.endArgs.args (namedGen A.ra A.sb) (Johnson/Goal/Conditions/HomeAtWider.lean), of the family
    theWider (Johnson/Goal/Conditions/WiderAtThe.lean), which the library calls stand-in
    descriptions: verifier, parser and the reading of the further public files (readMore) are
    descriptionOfDataOnBytes flashProveData's. As a term it is not theDescription, whose own prover side is a silent
    placeholder (theProvers, Johnson/Goal/Description/Named.lean). This file connects neither that
    committer nor that prover with the release's programs, and does not say that a program of the
    release computes verify().
  3. It is not the goals' G3'pol. There is no bound on the prover side's queries here, and α is a
    parameter, where G3'pol asks alpha = 2^-40; and these theorems conclude CompleteOn, at the
    model's own output, where G3'pol asks CompleteFor at every output that can be served and meets
    the policy. The bound stands apart (honestWithin_member,
    Johnson/Goal/Conditions/HonestAtMember.lean).
  4. live. protocolDataWellFormed (Johnson/Goal/Description/Live.lean) is a Boolean function of the public files:
    the description's three makers return a value, both files' data have the full-size depth, its
    test on numbers passes, and none of the six lists of rounds is empty. That it accepts is proved
    in Lean, in the side library (outside the main library and with that library's own limits), at
    the written copy storedPublicFiles of the full-size example's files under every acceptance policy in scope
    (theLive_zFull, AtFullSide/Top/LiveAtFull.lean; theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean;
    zGap is one of these: zGap_eq). scope is proved in the main library (inScope_zAt,
    Johnson/Goal/Files/ScopeAtPolicies.lean), and read follows from scope (read_of_scope,
    Johnson/LPFPol/LiveAtPolicy.lean). The scope is wider, by five more free numbers and the scale
    file (six written examples of that part pass InScope and the reader: checked by evaluation,
    Johnson/Goal/Meaning/ScopeRun.lean): see Johnson/Goal/Description/LiveSaysNo.lean. There live
    stays a hypothesis of the list; at files in scope the verdict is the same at every policy in
    scope (theLive_in_range, Johnson/LPFPol/LiveCorollaries.lean), and it follows from two returns
    of the makers (theLive_of_two, Johnson/AtFull/Top/LiveOfTwo.lean). Our joined theorems
    (named_three, lastFits_idle_named, linkFits_named) are stated at the written copies of the two
    named sets of files, storedPublicFiles and zGap; AtFullSide/Home/HomeAtNamed.lean's head grades these
    proofs, and says what a written copy, a Lean term, is not tied to. The side library's limits, as
    AtFullSide/Top/LiveAtFull.lean's head has them: it is built with a larger thread stack than the
    files under lean/Johnson/; nothing in the main library imports that file, so only a build of the
    side library shows a break in it; no independent checker has replayed it. One constant beneath
    these theorems (Johnson.Unfolds.Layout.lay_chars, AtFullSide/Layout/TieRfl.lean) fails in Lean's
    kernel at the default thread stack and passes inside lean --tstack=131072, compiled and
    replayed; the toolchain's re-checker (leanchecker) has not completed on it at any shell stack
    limit tried (it stops with the same message as the kernel at the default stack, "deep recursion
    detected"; lean/THEOREM.md,
    "Its reach").
  5. A matter that is not settled sits in honest. yesAt holds every well-formed request that is true
    under the files' policy at some weights' index, whether it can be served or not. If the
    description's lookups admit fewer values than the integer model admits, honest can hold at yesAt
    only at error
    terms that sum to at least 1 (argued on paper, not proved: Johnson/Goal/Conditions/HomeEnd.lean,
    limit 2). By HonFit.mono (Johnson/Prover/All/OfHonest.lean) a proof of honest at any larger set
    of instances is enough.
  6. lawT and lawB are asked at every seed, at all weights and at every coin κ, and lawB at all
    instances and numbers too. They can be satisfied by the interactive provers' coins' type alone:
    by a prover whose strategy sends the run values that are stored in its coin.
  7. The raw value (the field raw of LastArgs) is a free variable: no clause says how it is made,
    and nothing is said of its distribution. The commitment randomness is open too: Rand, B, ρOf,
    ra, sb are parameters; the sampler maps a number from 0 to B by ρOf; B = 0 is allowed; bytes
    asks a length alone. The prover encodes one copy of the committed table for each request. No
    clause says that the copy's encoding randomness differs from the first table's or from another
    copy's; at the idle parameters it is the first table's (HomeIdle.lean).
  8. All limits of Johnson/Goal/Conditions/WiderAtThe.lean, which are those of the family theWider,
    apply here too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeEnd
import Johnson.Goal.Conditions.HomeServed
import Johnson.Goal.Conditions.HonestAtHome
import Johnson.Prover.At.DrawHome

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
open LPFD.Full (saltG sTG sBG)
open Johnson.Prover.Print

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **The open parameters of completeOn_last**: all that this file does not fix. -/
structure LastArgs (b : PublicFiles → ℕ) (Rand : Type) (B N : ℕ) where
  /-- the three interactive protocols' provers (ThreeProvers: three values of Honest): strategies and abort
  sets -/
  Hs : (Z : PublicFiles) → ThreeProvers (homeR b Z).protocol
  /-- the falls (Johnson/Prover/All/OfHonest.lean) -/
  Fs : (Z : PublicFiles) → Falls (Hs Z)
  /-- the seeds that are set aside -/
  Zs : (Z : PublicFiles) → (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed
  capT : PublicFiles → ℕ → ℕ
  capL : PublicFiles → ℕ → ℕ
  capB : PublicFiles → ℕ → ℕ
  ρOf : Fin (B + 1) → Rand
  ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1)
  sb : Rand → ℕ → ByteArray
  /-- what the prover's coins are made of, beside the four run values: the type of the strategies'
  further coins; the raw value -/
  Kap₀ : PublicFiles → Type
  raw : (Z : PublicFiles) → (homeT b Z).D → Rand → Fin (N + 1) →
    DrawRaw (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits (Kap₀ Z)
  /-- the three interactive provers' coins, from the further coins and the byte coins' four run
  values; and the four run values read back off these coins -/
  κOf : (Z : PublicFiles) → Kap₀ Z × Runs4 → kapOf Hs Z
  runs : (Z : PublicFiles) → kapOf Hs Z → Runs4
  /-- the shape of the copy's file's binding tree -/
  sL : OnBytes.Params.LinBindingShape
  /-- the instance where the builder builds nothing; the form where a search has run out -/
  x₀ : (Z : PublicFiles) → (homeR b Z).Instance
  fb : FormBytes
  ζ : ℝ≥0∞
  pT : ℝ≥0∞
  pL : ℝ≥0∞
  pO : ℝ≥0∞

variable {b : PublicFiles → ℕ} {Rand : Type} {B N : ℕ} (A : LastArgs b Rand B N)

/-- **EndArgs at these parameters.** Given as explicit terms: the prover's coins as a function of
raw (drawK, Johnson/Prover/At/DrawHome.lean: drawAt of Johnson/Prover/Print/DrawOwes.lean at the raw
value, at the plan's numbers and the told part of the reading, its κ mapped by κOf) · its byte coins
(the raw ones, tidied) · the instance of a request (xAt, Johnson/Goal/Conditions/HomeServed.lean) ·
how a typed program runs over the hash function (carryF at passHome,
Johnson/Goal/Conditions/HonestAtHome.lean). No clause of LastFits names raw. -/
def LastArgs.endArgs : EndArgs b Rand B N where
  Hs := A.Hs
  Fs := A.Fs
  Zs := A.Zs
  capT := A.capT
  capL := A.capL
  capB := A.capB
  ρOf := A.ρOf
  ra := A.ra
  sb := A.sb
  drawOf := fun Z d ρ a => drawK (A.κOf Z) (numsAt (dataAtFiles flashProveData Z) A.sL)
    (_root_.Run.digToBytes ((homeT b Z).part d)) (A.raw Z d ρ a)
  bcT := fun Z d ρ a =>
    (A.raw Z d ρ a).bT.tidy (saltG (dataAtFiles flashProveData Z).G) (sTG (dataAtFiles flashProveData Z).G)
  bcL := fun Z d ρ a => (A.raw Z d ρ a).bL.tidy (saltG (dataAtFiles flashProveData Z).G) A.sL
  bcB := fun Z d ρ a =>
    (A.raw Z d ρ a).bB.tidy (saltG (dataAtFiles flashProveData Z).G) (sBG (dataAtFiles flashProveData Z).G)
  sL := A.sL
  xOf := fun Z => xAt b Z (A.x₀ Z)
  carry := fun Z d => carryF (homeT b Z) (fun _ => passHome b Z) d
  fb := A.fb
  ζ := A.ζ
  pT := A.pT
  pL := A.pL
  pO := A.pO

/-- **The thirteen hypotheses of completeOn_last**, at one set of public files Z. -/
structure LastFits (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (α : ℝ≥0∞) : Prop where
  /-- the files -/
  read : readFiles Z = .ok pp
  scope : InScope Z = true
  live : protocolDataWellFormed (asDescriptionFiles Z) = true
  /-- the three provers and the falls, at the explicit set of true instances yesAt -/
  honest : ∀ d, HonFit (A.Hs Z) (A.Fs Z) (homeR b Z).queryLayout ((homeT b Z).Sd d) (yesAt b Z read) (A.Zs Z)
    A.ζ A.pT A.pL A.pO
  /-- what the printer asks of the key file's and of the proof file's strategy: conditions on the
  provers alone: at every coin κ the strategy sends the two run values that are read off κ, and its
  words and columns can be printed -/
  lawT : ∀ w ρ e₁ (κ : kapOf A.Hs Z),
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
      (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty
      ((A.Hs Z).strats.T (backB b Z (settingsOfRead pp) w) (A.endArgs.pads Z ρ) e₁ κ)
      (A.runs Z κ).1.1 (A.runs Z κ).1.2
  lawB : ∀ w r e₂ x n (κ : kapOf A.Hs Z),
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      ((A.Hs Z).strats.B (backB b Z (settingsOfRead pp) w) r e₂ x n κ)
      (A.runs Z κ).2.1 (A.runs Z κ).2.2
  /-- One value of the prover's coins holds the same bytes in κ and in the byte coins: four run
  values that fit (Runs4.Fit, Johnson/Prover/Print/DrawOwes.lean: 32 bytes each, each passing the
  format's test on a run value) can be read back off the three interactive provers' coins. It is
  asked only at run values that fit, because a prover's coins (Honest.Coin, Iop/InteractiveOracleProof.lean) are a
  finite type: asked at all byte strings it could hold at no provers. That it can be satisfied at
  finite coins is proved by tie_toy (Johnson/Goal/Conditions/HomeTieMet.lean), a statement about
  types and two maps. Where it is proved together with honest at homeR b Z: the head's limit 1. -/
  tie : ∀ k r, Runs4.Fit r → A.runs Z (A.κOf Z (k, r)) = r
  /-- the commitment randomness: as many bytes for each leaf as the plan's salt has -/
  bytes : ∀ ρ j, (A.sb ρ j).size = saltG (dataAtFiles flashProveData Z).G
  /-- numbers: the copy's file's binding tree has one leaf; the bounds on attempts are below 2^64;
  the sum. The three bounds are parameters. At the explicit bounds capT (sAt Z), capL and capB (sAt
  Z) (Johnson/Goal/Conditions/HonestNumber.lean: 2^(work + 6) - 1 at the work of the three files'
  own rounds) the three clauses hold if Z is in scope and protocolDataWellFormed accepts (caps_home,
  Johnson/Goal/Conditions/NumberAtHome.lean). That theorem is not used in this file. -/
  flat : A.sL.logLeaves = 0
  capT : ∀ j, A.capT Z j < 2 ^ 64
  capL : ∀ j, A.capL Z j < 2 ^ 64
  capB : ∀ j, A.capB Z j < 2 ^ 64
  number : alphaAll (homeR b Z).queryLayout (A.capT Z) (A.capL Z) (A.capB Z) A.ζ A.ζ A.pT A.pL A.pO ≤ α

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {α : ℝ≥0∞}

/- Lean compares these by their names (the warning at the like attribute in HomeEnd.lean). -/
attribute [local irreducible] Rom.OComp.det OnBytes.Prover.runsAt Rom.readBlocks
  Johnson.Prover.Print.drawK OnBytes.Prover.carryF

/-- The clause "good" at the prover's coins as drawK builds them: good_home
(Johnson/Prover/At/DrawHome.lean); the digest by part_homeT
(Johnson/Goal/Conditions/HomeAtWider.lean). -/
theorem good_last (F : LastFits A Z pp α) (w : ModelWeights (settingsOfRead pp)) (t : Fin (B + 1))
    (a : Fin (N + 1)) (hash : Hash) :
    GoodOwesB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) (_root_.Run.digToBytes (cAt Z hash))
      (saltG (dataAtFiles flashProveData Z).G) A.sL
      (A.endArgs.bcT Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a)
      (A.endArgs.bcL Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a)
      (A.endArgs.bcB Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a)
      (A.capT Z) (A.capL Z) (A.capB Z) (backB b Z (settingsOfRead pp) w)
      (A.endArgs.pads Z (A.ρOf t))
      (saltsAt ((homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash))) (A.sb (A.ρOf t)))
      (A.endArgs.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a) := by
  have e : cAt Z hash = (homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash)) :=
    (part_homeT b Z hash).symm
  rw [e]
  exact good_home b Z F.scope F.live (A.κOf Z)
    (_root_.Run.digToBytes ((homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash)))) A.sL
    (A.capT Z) (A.capL Z) (A.capB Z) (backB b Z (settingsOfRead pp) w) (A.endArgs.pads Z (A.ρOf t))
    (A.sb (A.ρOf t)) (A.raw Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a) F.flat
    (_root_.Run.size_digToBytes _) F.capT F.capL F.capB fun j _ =>
      (F.bytes (A.ρOf t) j).le.trans (Meaning.sizesSay_the Z F.scope F.live).salt

/-- **What tie is used for**: off the field κ of the prover's coins as drawK builds them the four
run values of the byte coins are read: drawK_κ (Johnson/Prover/At/DrawHome.lean); the tidied values
fit (coinsPrint_tidy, OnBytes/Prover/Print/Tidy.lean). -/
theorem runs_last (F : LastFits A Z pp α) (d : (homeT b Z).D) (ρ : Rand) (a : Fin (N + 1)) :
    A.runs Z (A.endArgs.drawOf Z d ρ a).κ =
      (((A.endArgs.bcT Z d ρ a).run2, (A.endArgs.bcT Z d ρ a).run3),
        ((A.endArgs.bcB Z d ρ a).run2, (A.endArgs.bcB Z d ρ a).run3)) := by
  have h64 := (Meaning.sizesSay_the Z F.scope F.live).salt
  have cT := OnBytes.Prover.Print.coinsPrint_tidy (saltG (dataAtFiles flashProveData Z).G)
    (sTG (dataAtFiles flashProveData Z).G) (A.raw Z d ρ a).bT h64
  have cB := OnBytes.Prover.Print.coinsPrint_tidy (saltG (dataAtFiles flashProveData Z).G)
    (sBG (dataAtFiles flashProveData Z).G) (A.raw Z d ρ a).bB h64
  show A.runs Z (drawK (A.κOf Z) (numsAt (dataAtFiles flashProveData Z) A.sL)
    (_root_.Run.digToBytes ((homeT b Z).part d)) (A.raw Z d ρ a)).κ = _
  rw [drawK_κ]
  exact F.tie _ _
    ⟨cT.fit.run2, cT.fit.run3, cB.fit.run2, cB.fit.run3, cT.ok2, cT.ok3, cB.ok2, cB.ok3⟩

/-- **EndFits (Johnson/Goal/Conditions/HomeEnd.lean) from LastFits.** -/
theorem endFits_of_last (F : LastFits A Z pp α) : EndFits A.endArgs Z pp (yesAt b Z F.read) α where
  read := F.read
  scope := F.scope
  live := F.live
  served := fun w p o hd hm => served_home b Z F.scope F.read (A.x₀ Z) w p o hd hm
  honest := F.honest
  bytes := F.bytes
  draw := fun d ρ a => drawFit_drawK_home b Z (A.κOf Z)
    (_root_.Run.digToBytes ((homeT b Z).part d)) A.sL (A.raw Z d ρ a) F.flat
    (_root_.Run.size_digToBytes _) (Meaning.sizesSay_the Z F.scope F.live).salt
  good := good_last A F
  lawT := fun w t a hash e₁ => by
    have h := F.lawT w (A.ρOf t) e₁
      (A.endArgs.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a).κ
    rw [runs_last A F] at h
    exact h
  lawB := fun w p o t a hash e₂ => by
    have h := F.lawB w
      (A.endArgs.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a).r e₂
      (A.endArgs.xOf Z p o)
      (A.endArgs.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a).n
      (A.endArgs.drawOf Z ((homeT b Z).Pub.det (_root_.Run.famOne hash)) (A.ρOf t) a).κ
    rw [runs_last A F] at h
    exact h
  carried := fun w ρ p o a d g => det_home b Z (fillB b Z) (A.Hs Z).strats (A.capT Z) (A.capL Z)
    (A.capB Z) g d
    (backB b Z (settingsOfRead pp) w, A.endArgs.pads Z ρ, saltsAt ((homeT b Z).part d) (A.sb ρ))
    (xAt b Z (A.x₀ Z) p o) (A.endArgs.drawOf Z d ρ a)
  number := F.number

/-- **CompleteOn, from LastFits, of the system with the library's verify() and a prover side given
by parameters** (the head's limit 2), with b and gen as parameters, under hgen. -/
theorem completeOn_last_of (gen : (Z : PublicFiles) → Rand → Digest → Digest → Fin (b Z + 1))
    (hgen : ∀ ρ c I, (gen Z ρ c I).val = (A.ra Z ρ).val + ((riDigits Z).n + 1) *
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt c (A.sb ρ))).val)
    (F : LastFits A Z pp α) :
    CompleteOn (systemOfRecord (atSecondHashFunction (member A.endArgs.args gen)) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp)) α :=
  completeOn_end_of A.endArgs gen hgen (endFits_of_last A F)

end FlashProve

namespace FlashProve
open VerifierAndGoals VerifiableInference

/-- **CompleteOn, from LastFits, of the system with the library's verify() and a prover side given
by parameters** (the head's limit 2): the main theorem, at committerCoinCountLessOne and namedGen. -/
theorem completeOn_last {Rand : Type} {B N : ℕ} (A : LastArgs committerCoinCountLessOne Rand B N) {Z : PublicFiles}
    {pp : Inst.Model.ScalesAndPolicy} {α : ENNReal} (F : LastFits A Z pp α) :
    CompleteOn
      (systemOfRecord (atSecondHashFunction (member A.endArgs.args (namedGen A.ra A.sb))) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp)) α :=
  completeOn_end A.endArgs (endFits_of_last A F)

end FlashProve

#print axioms FlashProve.good_last
#print axioms FlashProve.runs_last
#print axioms FlashProve.endFits_of_last
#print axioms FlashProve.completeOn_last_of
#print axioms FlashProve.completeOn_last
