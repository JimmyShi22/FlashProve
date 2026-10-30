-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/BatchDoor.lean: the generic protocol, as the Batch protocol of an interface, meets, under the
hypotheses of its statements, formal side conditions of the library's compilation theorems (the
record `Met`); the conditions with content are not met.

Run/M1Door.lean proves the same with the protocol as the interface's Test. Here the protocol of
Run/PlanQS.lean is the interface's Batch (`LbS`, `Wb`), which is where the run functions are
defined. The twelve conditions of the record `Met` are met, for every choice of challenge types C
(for each round the type of the verifier's message, and the map from such a message to the format's
record of what was drawn; `CK` in the code), list of rounds and decision, from the laws of Batch's
own wiring and if its external oracle's wiring is `we0`. The library's theorem `bcsSoundBatchG`
applies at the relation "everything", and its conclusion is empty there too. The record of
conditions is `Met L W` of Run/M1Door.lean. The proofs are in Run/BatchDoorProofs.lean.

1. What the file contains. Statements (Run.BatchDoor.Spec.*).

2. What is checked when the file compiles. Only the types.

3. Theorems stated.
   `joint_true`: state functions that are constantly 1 obey the library's law on verifier messages
     of a batch with all errors 0: any shape, any annotation, any number of slots.
   `lb_sound`: (Lb B).Sound (everything) 0, for every batch B. It is true and empty. At the relation
     "everything" (`All`, Run/M1Door.lean: every instance is in the relation) every string decodes
     too, so no statement lies outside Batch's language. There the state function that is constantly
     1 serves, and nothing is asked of any round.
   `okgWb`: the whole wiring Wb K wB obeys the laws if Batch's wiring wB does and its external
     oracle's wiring is the one without a position.
   `metB`: Met (LbS C ds dec) (Wb K wB), for every wiring wB of the batch "the protocol, local
     rounds only" with these two properties.
   `metB_N`, `metB_M`: at the programs' tiny and full parameters of the first toy (the descriptions
     N, M of Run/M1RunTieTheirs.lean), with challenges as hash blocks, at the wiring with pruned
     openings.
   `metBF_T`, `metBF_R`, `metBF_F`: at the descriptions of Run/M1RunTiePF.lean, at the wiring with
     whole paths.

4. What it is worth, and what is not claimed.
   It shows that moving the protocol from Test to Batch costs nothing for these conditions.
   No statement on soundness follows. The library's clause on an accepted Batch string is "the
   external string does not decode, or the instance is in the relation". At "everything" this is
   true of everything. The toy has no index and an empty statement, so its language is trivial at
   every relation on (index, instance). Content lies in the knowledge form alone: the theorem with a
   witness (`bcsSoundBatchK`, CompileK/KnowSoundSpec.lean; known here by its head, as reported from
   a second reading), whose hypothesis is round-by-round knowledge soundness for a named relation,
   with the map that reads a witness off the prover's own oracle messages. That is not shown here. A
   search of the folders Run and Fmt for that hypothesis's name (`BatchProtocol.SoundK`, Hiop/Interface.lean)
   found it in one place: the head of Run/M1Door.lean (there: PropsK.soundK, SoundKG), as not met.
   It is proved nowhere in Run/ or Fmt/.
   That what a run function evaluates behind the reader is the run of `Compile.Batch.vBS` at (LbS,
   Wb ..) is proved at closed descriptions in Run/M1RunTie.lean and its companion files (vbs_*,
   vbsP_*, vbsPF_*).
   Completeness is not met: the honest sides are placeholders. Hiding (the field `hidden` of
   `BatchProtocol.Props`, Iop/Batch.lean) is not shown of this interface, in this file or elsewhere in Run/.
   Nothing is said about bytes.

Terms: lean/GLOSSARY.md.
-/
import Run.BatchS
import Run.M1RunTieTheirs
import Run.M1RunTiePF

set_option autoImplicit false

namespace Run.BatchDoor
open Iop Rom Compile Compile.Batch Prob Run.PQ Run.M1Door
open scoped ENNReal

namespace Spec

def joint_true : Prop :=
  ∀ (N : ℕ) (s : Shape) (A : RoundSplits s) (Sf : Fin N → Option (PTr s → Bool)),
    (∀ j S, Sf j = some S → ∀ τ, S τ = true) → JointLaw N s A (zErr s) Sf

def lb_sound : Prop := ∀ B : BatchInteractiveOracleProof Unit E0, (Lb B).Sound All 0

def okgWb : Prop :=
  ∀ (B : BatchInteractiveOracleProof Unit E0) (K : ℕ) (wB : ProtocolQueryLayout 256 K B), wB.OKG → wB.ext = we0 → (Wb K wB).OKG

/-- States what is met with the generic construction's protocol as Batch:
`Met (LbS C ds dec) (Wb K wB)`, if `wB.OKG` and `wB.ext = we0`. -/
def metB : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool) (K : ℕ)
      (wB : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (PSof C ds dec).up.loc)),
    wB.OKG → wB.ext = we0 → Met (LbS C ds dec) (Wb K wB)

def metB_N : Prop :=
  Met (LbS (ckP M1RunTieTheirs.SN.plan.field) (rds M1RunTieTheirs.SN) M1RunTieTheirs.dN)
    (Wb (kOf M1RunTieTheirs.SN + 1) M1RunTieTheirs.WN.T)
def metB_M : Prop :=
  Met (LbS (ckP M1RunTieTheirs.SM.plan.field) (rds M1RunTieTheirs.SM) M1RunTieTheirs.dM)
    (Wb (kOf M1RunTieTheirs.SM + 1) M1RunTieTheirs.WM.T)
def metBF_T : Prop :=
  Met (LbS (ckP M1RunTiePF.ST.plan.field) (rds M1RunTiePF.ST) M1RunTiePF.dT)
    (Wb (kOf M1RunTiePF.ST + 1) M1RunTiePF.WT.T)
def metBF_R : Prop :=
  Met (LbS (ckP M1RunTiePF.SR.plan.field) (rds M1RunTiePF.SR) M1RunTiePF.dR)
    (Wb (kOf M1RunTiePF.SR + 1) M1RunTiePF.WR.T)
def metBF_F : Prop :=
  Met (LbS (ckP M1RunTiePF.SF.plan.field) (rds M1RunTiePF.SF) M1RunTiePF.dF)
    (Wb (kOf M1RunTiePF.SF + 1) M1RunTiePF.WF.T)

end Spec

end Run.BatchDoor
