-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Record.lean: the library's structure for an honest side of a batch
protocol (`Iop.BatchHonestProver`, Iop/Batch.lean), filled from a prover of Honest/Frame.lean, for a general
description: over the protocol of the file's reduction (`FileDescription.toIOR`,
Johnson/Desc/BlockSlot.lean) with its annotation. The result is `honestB`. Definitions only;
no theorem.

Field by field.
  Wt       the index, the stored tables' pads and encoding randomness, the seed
  Coin0    the coins of the shared chain's parts, and a type parameter R2
  Coin     the coins of the first and the second chain's parts, and a type parameter R3
  ext      a parameter: the stored table in full
  strat0, requestStrategy   the two strategies of Honest/Strat.lean
  stop0    the shared chain's stops   }  each is `chainStopAt` (Honest/Rule.lean), at the challenges
  Bad      the first stops            }  that the library's typed verifier messages show: no stop is
  Hid      the second stops           }  written a second time, and no coin is read

  1  `loTake`, `loSkip`, `loEnd`, `shTake`, `shSkip`, `drawsLo`, `drawsSh`   the local and the
     shared verifier messages of the whole shape, as Honest/Frame.lean's lists of challenges
  2  `stop0B`, `badB`, `hidB`   the three sets' tests, executable
  3  `batchOf`, `honestB`   the protocol with its annotation; the filled structure

R2, R3. The second and the third chain's run values are sent in the joining round and in the seam.
In a compiled run they come from the compiler's randomness, so in `honestB` they are among the coins
and are no fixed values. So `honestB` takes the `KeyAndJoiningRoundMessages` as a function of two arguments: J r2 r3. The
shared part's strategy is given r2 alone: it uses J r2 at a fixed r3, and reads from it the key and
the joining round's part. That these two do not depend on r3 is up to the caller: nothing here
checks it (`KeyAndJoiningRoundMessages.ofFour` meets it). If the key depended on r3, the shared part would play chain 2 at
one key and the slot would play it again at another: what `Prover.meet` reads would be the end of
another chain 2 than the one that was sent, and no test rejects that.

Limits.
  * Nothing is proved about `honestB` here: neither the library's `BatchHonestProver.Acc` nor its
    `BatchHonestProver.HVZK` (Iop/Batch.lean), and no bound on the probability of any of its three sets of
    challenges.
  * Nothing compares `ext` with `Prover.stored`.
  * Nothing compares the key that `KeyAndJoiningRoundMessages.keyOf` computes with `Prover.key`.
  * D is a parameter.
  * A first stop in the first or the second chain reads these two chains' challenges alone, as in
    `run`.
  * The three sets together are the silent set (`silentAt`, Honest/Rule.lean) where the request has
    a trace. Where it has none `silentAt` is `none`, and stop0 and Bad, which read no instance, can
    still hold.
  * One by one they are not its classes. `silentAt` names the first stop that fires. Bad holds every
    list at which a first stop fires somewhere in the two chains, also after a second stop: so Bad
    and Hid can overlap.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Strat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (RDT WholeD uLT roundT chainsOf)
open Iop (Shape RoundSplits RhoLo RhoSh)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 The verifier's messages as lists of challenges -/

section
variable (C : CK) {rest : Shape} {A : RoundSplits rest}

/-- A local chain's challenges among the local verifier messages; and what follows. -/
def loTake : (ds : List RDT) →
    RhoLo (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A) →
    List Fmt.Drawn × RhoLo rest A
  | [], ρ => ([], ρ)
  | d :: ds, (c, ρ) => ((drOf C d c :: (loTake ds ρ).1), (loTake ds ρ).2)

/-- A shared chain has none there. -/
def loSkip : (ds : List RDT) →
    RhoLo (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A) →
    RhoLo rest A
  | [], ρ => ρ
  | _ :: ds, (_, ρ) => loSkip ds ρ

/-- A shared chain's challenges among the shared verifier messages; and what follows. -/
def shTake : (ds : List RDT) →
    RhoSh (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A) →
    List Fmt.Drawn × RhoSh rest A
  | [], ρ => ([], ρ)
  | d :: ds, (c, ρ) => ((drOf C d c :: (shTake ds ρ).1), (shTake ds ρ).2)

/-- A local chain has none there. -/
def shSkip : (ds : List RDT) →
    RhoSh (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A) → RhoSh rest A
  | [], ρ => ρ
  | _ :: ds, (_, ρ) => shSkip ds ρ

end

/-- The last chain's challenges. -/
def loEnd (C : CK) : (ds : List RDT) → RhoLo (uLT C ds) (Iop.RoundSplits.allLocal (uLT C ds)) →
    List Fmt.Drawn
  | [], _ => []
  | d :: ds, (c, ρ) => drOf C d c :: loEnd C ds ρ

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

/-- **The first and the second chain's challenges**, from the local verifier messages of the whole
shape. The sealing round's empty challenge is appended to the first chain's, as `run` has it. -/
def drawsLo (ρ : RhoLo (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) :
    List Fmt.Drawn × List Fmt.Drawn :=
  let a := loTake C D.ds₁ ρ.2
  let b := loSkip C D.ds₂ a.2.2
  (a.1 ++ [⟨[], [], [], none⟩], loEnd C D.ds₃ b.2)

/-- **The shared chain's challenges**, from the shared verifier messages. -/
def drawsSh (ρ : RhoSh (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) : List Fmt.Drawn :=
  (shTake C D.ds₂ (shSkip C D.ds₁ ρ.2).2).1

end

/-! ## 2 The three sets' tests -/

section
variable (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)

/-- The shared chain stops: from its own challenges alone. -/
def stop0B (ds : List Fmt.Drawn) : Bool :=
  (chainStopAt (none : Option Empty) F.shared.blocksInOrder H.shared [] ds).isSome

/-- A first stop fires in the first or the second chain: from these chains' challenges alone. No
input is supplied, so no second stop is asked. -/
def badB (ds : List Fmt.Drawn × List Fmt.Drawn) : Bool :=
  (chainStopAt (none : Option (Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first [] ds.1).isSome ||
    (chainStopAt (none : Option (Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second ds.1 ds.2).isSome

/-- In the first chain, or in the second, the first stop that fires is a second stop, at the input.
False if the request has no trace. -/
def hidB (w₀ : W₀) (rc : Rc) (x : Xi) (ds : List Fmt.Drawn × List Fmt.Drawn) : Bool :=
  (H.trace w₀ x).any fun tr =>
    let w : Local W₀ Rc Xi Tr := ⟨w₀, rc, x, tr⟩
    chainStopAt (Face.own.sees w) F.first.blocksInOrder H.first [] ds.1 == some .hid ||
      chainStopAt (Face.own.sees w) F.second.blocksInOrder H.second ds.1 ds.2 == some .hid

end

/-! ## 3 The filled structure -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool)

/-- The protocol of the file's reduction, with its annotation. -/
def batchOf : Iop.BatchInteractiveOracleProof Xi (Iop.oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX) :=
  ⟨(F.toIOR C D tF tJ t3 silent).toInteractiveOracleProof, OnBytes.Maker.annOf C D tF tJ t3 silent F.run⟩

/-- **The honest side of the file's protocol**, as the library's `Iop.BatchHonestProver`. -/
noncomputable def honestB (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2] [Nonempty R2]
    [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX).Str) :
    Iop.BatchHonestProver (batchOf C D tF tJ t3 F silent) (W₀ × Rc × Sd) where
  Coin0 := Purse B.shared × R2
  Coin := (Purse B.first × Purse B.second) × R3
  ext := ext
  strat0 := fun w c => strat0 C D tF tJ t3 F B H (J c.2 default) w c.1
  strat := fun w c₀ x c => requestStrategy C D tF tJ t3 F B H (J c₀.2 c.2) w c₀.1 x c.1
  Bad := {ρ | badB F H (drawsLo C D tF tJ t3 ρ) = true}
  Hid := fun w x => {ρ | hidB F H w.1 w.2.1 x (drawsLo C D tF tJ t3 ρ) = true}
  stop0 := fun ρ => stop0B F H (drawsSh C D tF tJ t3 ρ)

end

end ProofFile.Honest
