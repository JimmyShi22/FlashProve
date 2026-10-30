-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullFace.lean: the interface `LtS`, with challenges as hash blocks, is as a term the
interface that the library's own construction gives.

An interface (`BatchProtocol`, Iop/Batch.lean) is the library's record of three protocols, called Test, Link
and Batch, with an encoding and a decoding of an index and with honest sides; the compiler's
theorems are stated of an interface. Challenges as hash blocks (`ckP`) and as sampled values (`ck`),
and a wiring, are explained in the head of Run/PlanPull.lean.

The types of all typed queries, strings and wirings depend on the interface. Take a sentence of the
form "the term that is evaluated is the term at which `schemeWk` stands"
(CompileK/GrindMain.lean: at (D.LWk w, D.WWk w), as read there). For such a sentence the interface
has to be that term. Run/PlanPullProto.lean has this for the Test's protocol; this file has it for
the whole record. The library's construction (`BatchProtocol.drawsGrind`, Iop/GrindPull.lean) starts from the
interface with challenges as sampled values, without work. It makes the verifier messages from
blocks and then adds the tests of work. So `LtS (ckP f) ds dec` is `D.LWk w` for every data D of the
compilation and work w with the samplers `drOf f ds` and the bits `g0Of f ds` (`face_data`), if
there are such. None is written down in this file. No statement has a cast: both sides are terms of
one type. That type is `BatchProtocol Unit Unit`, but in `dummy_step` it is `Honest P Wt` and in `dummyB_step`
it is `BatchHonestProver P Wt`. There P is the protocol, or the batch, so made. The proofs are in
Run/PlanPullFaceProofs.lean. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

`LtS` is the interface whose Test is the protocol of Run/PlanQS.lean. The run functions do not stand
at it. They stand at `LbS`, whose Batch is the same protocol (`(PSof C ds dec).up.loc`, local rounds
alone) and whose wiring's field B is the same `wqS` or `wqSF` (in the theorems vbs_*, vbsP_*,
vbsPF_* of Run/M1RunTie.lean and its companion files, Run/M2Tie.lean and Run/PlanQSToy.lean; `Wb`,
Run/PlanQS.lean; `batch_same`, Run/BatchS.lean). What is said here of `LtS` and of its Test holds as
it stands: these are facts about terms.

1. What the file contains.
   `dummyH`, `dummyB` and `Lo3` are in Run/PlanQS.lean (the interface `LbS` is made of them); `Lof`
   and `L0` are defined here.
   `dummyH Q ext`, `dummyB Q ext`: the placeholder honest side of a protocol, of a batch: one coin;
     the given external oracles; every round's fixed substitute; nothing withheld.
   `Lo3 T Lk B`: the interface without an index (an encoded index of length 0; every string decodes)
     with three given protocols as Test, Link, Batch (one slot) and placeholders as honest sides.
   `Lof T`: Link and Batch have no rounds.

2. What is checked when the file compiles. Only the types.

3. Theorems stated.
   `lts_lof` (by definition), `lo3_step` (generic in all three places), `planPull_face`,
   `face_data`: read their statements below.
   `dummy_step`, `dummyB_step`: the placeholder, pulled back along samplers and given tests (with
     the fixed nonce), is the placeholder of the protocol so made: for any protocol, any batch with
     any annotation.

Notation:
  `PSof C ds dec`: the skeleton of the protocol (Run/PlanQS.lean);
  `.up`: the batch protocol of the skeleton (`PS.up`, Run/TwinDefs.lean);
  `.loc`: the local verifier of one slot (`BatchInteractiveOracleProof`, Iop/Batch.lean);
  `Qv C ds dec`: the protocol without work, at a choice `C` of challenge types;
  `drOf f ds`: the block samplers, one for each round;
  `g0Of f ds`: the bits of work, on the shape of `Qv` (all three in Run/PlanPullProto.lean);
  `pL`, `pB`: protocols without a round, `Lof`'s Link and Batch (Run/PlanQPage.lean).

4. What is not claimed.
   That the wiring is `D.WWk w`: Run/PlanPullJoin.lean [not in this library] (at three descriptions, for the wiring with
   whole paths: `join_T`, `join_R`, `join_F`). No such D is written down here (Run/PlanPullData.lean [not in this library]
   has one).
   Nothing on the interface's properties. `L0`'s honest sides are placeholders, so there is no
   completeness; its Test's language is "everything" (Run/M1Door.lean). So even with D, w and the
   wiring tied, a theorem at this interface would say nothing with content. Hiding (the field
   `hidden` of `BatchProtocol.Props`, Iop/Batch.lean) is not shown of `L0`, in this file or elsewhere in Run/.
   The interface with challenges as sampled values and with work (`LtS (ck f) ds dec`) is not spoken
   of, but for `lts_lof`, which is for every choice `C` of challenge types, and the generic
   `lo3_step`, `dummy_step`, `dummyB_step`.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanPullProto
import Iop.GrindPull
import CompileK.GrindMain

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch Run.PQ

/-- a given Test; Link and Batch without a round -/
@[reducible] def Lof (T : InteractiveOracleProof Unit E0) : BatchProtocol Unit Unit := Lo3 T pL (BatchInteractiveOracleProof.ofProto pB)

/-- The interface with challenges as sampled values, without work. -/
@[reducible] def L0 (f : _root_.Fmt.Fld) (ds : List RD) (dec : View → Bool) : BatchProtocol Unit Unit :=
  Lof (Qv (ck f) ds dec)

namespace Spec

def lts_lof : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool), LtS C ds dec = Lof (PSof C ds dec).up.loc

def dummy_step : Prop :=
  ∀ (X Wt : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (ext : Wt → E.Str)
      (σ : Samplers Q.shape) (g : GBits (Q.pull σ).shape),
    ((dummyH Q ext).pull σ).grind g (GNon.nil ℕ _) = dummyH ((Q.pull σ).grind ℕ g) ext

def dummyB_step : Prop :=
  ∀ (X Wt : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (ext : Wt → E.Str)
      (σ : Samplers Q.loc.shape) (g : GBits (Q.pull σ).loc.shape),
    ((dummyB Q ext).pull σ).grind g (GNon.nil ℕ _) = dummyB ((Q.pull σ).grind ℕ g) ext

/-- States: on an interface of placeholders (`Lo3`), `BatchProtocol.drawsGrind` (verifier messages from
blocks, then tests) is `Lo3` of the three protocols, each pulled back along its samplers and given
its tests. -/
def lo3_step : Prop :=
  ∀ (T : InteractiveOracleProof Unit (oneExternalString 0 Unit)) (Lk : InteractiveOracleProof Unit (twoExternalStrings 0 Unit))
      (B : BatchInteractiveOracleProof Unit (oneExternalString 0 Unit)) (dr : (Lo3 T Lk B).Draws 256) (gT : GBits T.shape)
      (gL : GBits Lk.shape) (gB : GBits B.loc.shape),
    (Lo3 T Lk B).drawsGrind ℕ dr gT gL gB =
      Lo3 ((T.pull (Samplers.ofDraws _ dr.T)).grind ℕ (gT.pull (Samplers.ofDraws _ dr.T)))
        ((Lk.pull (Samplers.ofDraws _ dr.Lk)).grind ℕ (gL.pull (Samplers.ofDraws _ dr.Lk)))
        ((B.pull (Samplers.ofDraws _ dr.B)).grind ℕ (gB.pull (Samplers.ofDraws _ dr.B)))

/-- States: the interface `LtS`, with challenges as hash blocks, is the library's term: `L0` with
its verifier messages made from blocks and then given its tests (`BatchProtocol.drawsGrind`). -/
def planPull_face : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List RD) (dec : View → Bool), LtS (ckP f) ds dec =
    (L0 f ds dec).drawsGrind ℕ (⟨drOf f ds, (), ()⟩ : (L0 f ds dec).Draws 256) (g0Of f ds) () ()

/-- States: `LtS (ckP f) ds dec` is `D.LWk w`, the interface of the compilation with proof of work,
for any data D with `D.dr = ⟨drOf f ds, (), ()⟩` and work w with `w.gT = g0Of f ds`. -/
def face_data : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List RD) (dec : View → Bool)
      (D : Compile.Batch.DataK (L0 f ds dec) 256) (w : Compile.Batch.Work ℕ (L0 f ds dec)),
    D.dr = (⟨drOf f ds, (), ()⟩ : (L0 f ds dec).Draws 256) →
    w.gT = g0Of f ds → LtS (ckP f) ds dec = D.LWk w

end Spec

end Run
