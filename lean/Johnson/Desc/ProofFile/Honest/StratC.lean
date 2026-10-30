-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/StratC.lean: the two strategies of the honest prover of
Honest/Walk.lean, which asks the description's own step on what it has sent, and the library's
`Iop.BatchHonestProver` filled with them. They are the counterparts of `strat0`, `requestStrategy` (Honest/Strat.lean)
and `honestB` (Honest/Record.lean), built from the same pieces. A `ChainProgress` is the state of a chain
between two rounds, with the verifier's state beside the prover's. Definitions only; no theorem.

  1  `ChainProgress.halt`, `ChainProgress.push`, `tellC`, `progressAfterChallenge`, `chainStartOrHalted`   a round of the walk for a speaker, which
     cannot return an error
  2  `requestStrategyOverSeparateChain`, `sharedStrategyOverSharedChain`, `speakLEndC`, `advanceOverRounds`   a chain's speakers: they carry a `ChainProgress`
  3  `sharedChainStart`, `sharedPartStrategyTrackingVerifier`, `requestStrategyTrackingVerifier`   the shared part's strategy and a slot's
  4  `honestBatchProverOfFile`   the library's `Iop.BatchHonestProver`, filled

One definition. A round's message and what follows its challenge are `ChainProgress.say` and `ChainProgress.heard`,
which `runC` calls. So the strategies ask the verifier's step where `runC` asks it, on the same
values. This is causal: a sub-protocol's step is asked when its last challenge has been heard,
before the next sub-protocol's first message, on the tables sent so far.
What a speaker does where `runC` returns an error (a stop, a fault, a column of a table that is not
available). It cannot return an error: from there on it sends each round's fixed substitute, as
after a rejection by the verifier. The substitute is `subTold`'s, put into the round's typed message
by `msgOf`. It is not the library's `Round.dOrc` and `Round.dPlain`, which `requestStrategy` sends; these are
sent only where there is no `Step` for a round of the data.
The front round, the joining round and the seam send `KeyAndJoiningRoundMessages`'s values at every list of challenges,
whatever error the prover has met and whatever the verifier has rejected: they are rounds of no
sub-protocol, and draw no challenge.
The shared part is given no instance, and the description's first state of the shared chain is
computed from the instance's public part. So the shared part takes that state from one more
parameter, `sh`, a function of the key. That `sh` at the instance's key is the description's own
first state has to be proved by whoever supplies it. The slot plays the shared chain again for
its end, from the same parameter.
Two strands. A rejection in the first chain does not reach the shared part's strategy. It reaches
the slot's third chain, as one in the shared chain does (`door₃`).
The columns go the same way as in `runC`: chains 1 and 2 start with no column opened (`some []`),
chain 3 with chain 1's and then chain 2's. `strat0` and `requestStrategy` hand no columns (`none`).

The sets. `honestBatchProverOfFile`'s three sets are `honestB`'s: from the stops alone, with no coin and no step of
the verifier's.

Limits.
  * Those of Honest/Strat.lean and Honest/Record.lean.
  * That the strategies' transcript shows `runC`'s views is not proved here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk
import Johnson.Desc.ProofFile.Honest.Record

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Block OpenedColumn)
open OnBytes.Maker (RDT WholeD uLT roundT chainsOf)
open Iop (Shape RoundSplits SStrat LStrat)
open _root_.Run.PQ (CK)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 W Y R2 R3 : Type}

/-! ## 1 A round, for a speaker -/

/-- Nothing more is played, and the verifier is asked no more. -/
def ChainProgress.halt (z : ChainProgress S Cl W Y) : ChainProgress S Cl W Y := { z with mid := none, ver := none }

/-- A round added to the walk without anything being asked: for where even a halted walk's
`ChainProgress.heard` returns an error (a column of a table that is not available). From there on the walk's
reads and columns are not kept up; no later message reads them, since a halted walk sends
substitutes. -/
def ChainProgress.push (z : ChainProgress S Cl W Y) (s : Step W Y) (x : Told) (d : Fmt.Drawn) : ChainProgress S Cl W Y :=
  let p : Played := ⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩
  { z.halt with laid := z.laid ++ [p], own := z.own ++ [p] }

/-- **What a round sends**: `ChainProgress.say`; the round's fixed substitute if that returns an error;
`none` if there is no `Step`. -/
def tellC (z : ChainProgress S Cl W Y) (s : Option (Step W Y)) : Option Told :=
  s.map fun s => ((z.say s).toOption).getD (subTold s.decl s.oracles)

/-- **After the round's challenge**: `ChainProgress.heard`, on what `tellC` has sent. If `ChainProgress.say` or
`ChainProgress.heard` returns an error, the walk halts, and the round is added to it all the same. With no
`Step` the walk halts and no round is added. -/
def progressAfterChallenge (L : Lay) (z : ChainProgress S Cl W Y) (s : Option (Step W Y)) (d : Fmt.Drawn) : ChainProgress S Cl W Y :=
  match s with
  | none => z.halt
  | some s =>
    match z.say s with
    | .error _ =>
      ((z.halt.heard L s (subTold s.decl s.oracles) d).toOption).getD
        (z.push s (subTold s.decl s.oracles) d)
    | .ok x =>
      match z.heard L s x d with
      | .ok z' => z'
      | .error _ => ((z.halt.heard L s x d).toOption).getD (z.push s x d)

/-- A chain's start, for a speaker: `ChainProgress.start`; if that returns an error, a walk that has halted.
`front`: the columns that earlier chains have opened, as in `ChainProgress.start`, which lays them into the
state `m`. With `m` or `v` at `none` they are laid into nothing: in `requestStrategyTrackingVerifier` that is the case for
the last chain wherever the walk of an earlier chain has halted (read off the definitions
`ChainProgress.halt` and `requestStrategyTrackingVerifier`; no lemma states it). -/
def chainStartOrHalted (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    (front : List OpenedColumn) : ChainProgress S Cl W Y :=
  ((ChainProgress.start L bs m v front).toOption).getD ⟨none, none, none, [], [], [], bs, []⟩

/-! ## 2 A chain -/

section
variable (C : CK) {rest : Shape} {A : RoundSplits rest}

/-- The slot's strategy over a local chain after which more rounds come. As `speakL`, with a walk
where that has the prover's run alone. `k`: builds the strategy for the rounds after this chain,
from the walk at the chain's end and the `Step`s that are left. -/
def requestStrategyOverSeparateChain (L : Lay) : (ds : List RDT) → List (Step W Y) → ChainProgress S Cl W Y →
    (List (Step W Y) → ChainProgress S Cl W Y → LStrat rest A) →
    LStrat (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A)
  | [], ss, z, k => k ss z
  | d :: ds, ss, z, k =>
    (msgOf C d (tellC z ss.head?), fun (c : (roundT C d).up.Chal) =>
      requestStrategyOverSeparateChain L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) k)

/-- The shared part's strategy over a shared chain. As `speakS`. -/
def sharedStrategyOverSharedChain (L : Lay) : (ds : List RDT) → List (Step W Y) → ChainProgress S Cl W Y → SStrat rest A →
    SStrat (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A)
  | [], _, _, k => k
  | d :: ds, ss, z, k =>
    (msgOf C d (tellC z ss.head?), fun (c : (roundT C d).up.Chal) =>
      sharedStrategyOverSharedChain L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) k)

end

/-- The slot's strategy over the last chain. As `speakLEnd`. -/
def speakLEndC (C : CK) (L : Lay) : (ds : List RDT) → List (Step W Y) → ChainProgress S Cl W Y →
    LStrat (uLT C ds) (Iop.RoundSplits.allLocal (uLT C ds))
  | [], _, _ => ()
  | d :: ds, ss, z =>
    (msgOf C d (tellC z ss.head?), fun (c : (roundT C d).up.Chal) =>
      speakLEndC C L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)))

/-- A whole chain walked by a speaker's own steps: for the rounds that a slot does not send itself.
Where the two lists differ in length it stops at the shorter and does not halt; `walk`
(Honest/Walk.lean) and `play` (Honest/Frame.lean) return an error there. -/
def advanceOverRounds (L : Lay) : List (Step W Y) → List Fmt.Drawn → ChainProgress S Cl W Y → ChainProgress S Cl W Y
  | s :: ss, d :: ds, z => advanceOverRounds L ss ds (progressAfterChallenge L z (some s) d)
  | _, _, z => z

/-! ## 3 The two strategies -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)

/-- The shared chain's walk at its start, from the index, the stored tables' pads and encoding
randomness, the key and the shared chain's own coins; with the `Step`s for it. No instance is among
its arguments. -/
def sharedChainStart (w₀ : W₀) (rc : Rc) (ky : Ky) (c₀ : Purse B.shared) :
    List (Step (Common W₀ Rc Ky) X₀) × ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀ :=
  let ss := (readyShared F B H w₀ rc ky c₀).toOption
  (ss.getD [], chainStartOrHalted ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
    (ss.map fun _ => startShared H ⟨w₀, rc, ky⟩) (some (sh ky)) [])

/-- **The shared part's strategy.** As `strat0`; chain 2 by the walk. -/
def sharedPartStrategyTrackingVerifier (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) :
    SStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  let a := sharedChainStart F B H sh w.1 w.2.1 (J.keyOf w.1 w.2.1 w.2.2) c₀
  ((), fun (_ : Unit) =>
    hushS C D.ds₁
      ((((), J.join w.1 w.2.1 w.2.2) : Unit × TJ), fun (_ : Unit) =>
        sharedStrategyOverSharedChain C ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩ D.ds₂ a.1 a.2
          ((), fun (_ : Unit) => hushSEnd C D.ds₃)))

/-- **A slot's strategy.** As `requestStrategy`; chains 1 and 3 by the walk; the sealing round and chain 2 are
walked for their ends. -/
def requestStrategyTrackingVerifier (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second) :
    LStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  let stored := H.storedWords w.1 w.2.1
  let R := (ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption
  let a := sharedChainStart F B H sh w.1 w.2.1 (J.keyOf w.1 w.2.1 w.2.2) c₀
  let L₁ : Lay := ⟨0, 0, stored, treeOwn⟩
  ((((), J.front w.1 w.2.1 w.2.2 x) : Unit × TF), fun (_ : Unit) =>
    requestStrategyOverSeparateChain C L₁ D.ds₁ ((R.map (·.first)).getD [])
      (chainStartOrHalted L₁ F.first.blocksInOrder (R.map fun R => R.start₁ H) (some (F.start₁ (F.pub x))) [])
      fun left y₁ =>
      let y := advanceOverRounds L₁ left [⟨[], [], [], none⟩] y₁
      let z₁ := if sealQuiet y.laid then y else y.halt
      ((), fun (_ : Unit) =>
        hushL C D.ds₂ [] fun ds₂ =>
          let z₂ := advanceOverRounds ⟨1, 0, stored, treeOwn⟩ a.1 ds₂ a.2
          let L₃ : Lay := ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩
          ((((), J.seam w.1 w.2.1 w.2.2 x) : Unit × T3),
            fun (_ : Unit) => speakLEndC C L₃ D.ds₃ ((R.map (·.second)).getD [])
              (chainStartOrHalted L₃ F.second.blocksInOrder
                (R.bind fun R => z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
                (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)))))

end

/-! ## 4 The filled structure -/

/-- **The honest side of the file's protocol, with the prover that asks the description's own
step**, as the library's `Iop.BatchHonestProver`. As `honestB`, except for the two strategies. `sh`: the
shared chain's first state, from the key. -/
noncomputable def honestBatchProverOfFile (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX).Str) :
    Iop.BatchHonestProver (batchOf C D tF tJ t3 F silent) (W₀ × Rc × Sd) where
  Coin0 := Purse B.shared × R2
  Coin := (Purse B.first × Purse B.second) × R3
  ext := ext
  strat0 := fun w c => sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H (J c.2 default) sh w c.1
  strat := fun w c₀ x c => requestStrategyTrackingVerifier C D tF tJ t3 F B H (J c₀.2 c.2) sh w c₀.1 x c.1
  Bad := {ρ | badB F H (drawsLo C D tF tJ t3 ρ) = true}
  Hid := fun w x => {ρ | hidB F H w.1 w.2.1 x (drawsLo C D tF tJ t3 ρ) = true}
  stop0 := fun ρ => stop0B F H (drawsSh C D tF tJ t3 ρ)

end ProofFile.Honest

#print axioms ProofFile.Honest.ChainProgress.halt
#print axioms ProofFile.Honest.ChainProgress.push
#print axioms ProofFile.Honest.tellC
#print axioms ProofFile.Honest.progressAfterChallenge
#print axioms ProofFile.Honest.chainStartOrHalted
#print axioms ProofFile.Honest.requestStrategyOverSeparateChain
#print axioms ProofFile.Honest.sharedStrategyOverSharedChain
#print axioms ProofFile.Honest.speakLEndC
#print axioms ProofFile.Honest.advanceOverRounds
#print axioms ProofFile.Honest.sharedChainStart
#print axioms ProofFile.Honest.sharedPartStrategyTrackingVerifier
#print axioms ProofFile.Honest.requestStrategyTrackingVerifier
#print axioms ProofFile.Honest.honestBatchProverOfFile
