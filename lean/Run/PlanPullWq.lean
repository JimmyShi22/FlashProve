-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullWq.lean: the protocol that the generic construction runs with challenges as hash blocks,
with its wiring with whole paths, is, as a pair of terms, the library's own: the compiler's generic
wiring of a Test (`ProtocolQueryLayout.ofLocalD`, Iop/BatchWireDraw.lean) at the protocol without work, then the
library's step for the tests (`ProtocolQueryLayout.grindLocal`, Iop/GrindWire.lean). This holds for every field,
number of blocks, list of rounds and decision. The generic construction: Run/PlanQ*.lean: makes,
from a description, the typed protocol, its wiring and the run functions. Challenges as hash blocks:
a round's verifier message is 256-bit blocks; reads and decision apply the sampling rule (`ckP`,
Run/PlanPull.lean). The library's step for the tests: makes, from a wiring without proof-of-work
tests, the wiring with them: Iop/GrindWire.lean.

Definitions and one statement (`Spec.planPull_wq`); the proof is in Run/PlanPullWqProofs.lean. The
words are explained in the heads of Run/PlanPull.lean, Run/PlanPullWire.lean. An interface (`BatchProtocol`,
Iop/Batch.lean) is the library's record of three protocols, called Test, Link and Batch, with an
encoding and a decoding of an index.

Why a pair: a wiring's type depends on its protocol (on its shape and its annotation). The two
protocols are equal (Run/PlanPullProto.lean) but not by definition; so "the two wirings are equal"
cannot be written without a cast. The pair (protocol with annotation, wiring) has one type on both
sides: no cast.

By the library's text, as read (`QueryLayout.ofDraws`, Iop/BatchWireDraw.lean): the generic wiring of an
interface L has
  T := ProtocolQueryLayout.ofLocalD lam dr.K L.offline pT dr.T ax.posT (WireE.one L.wordLength L.Symbol z) no.T (Nat.clog 2 L.wordLength):
the right side of `Spec.planPull_wq` has that form at L.offline := `Qv ..`, L.wordLength := 0, L.Symbol := Unit,
with K for dr.K.

Main names:
  `Spec.planPull_wq`: for every f, K, ds, dec, an equation of pairs. The first components are the
    protocol with its annotation (all rounds local).

Notation:
  `K + 1`: one block more, in the wiring with the tests (Iop/GrindWire.lean);
  `Qv C ds dec`: the protocol without work, at a choice `C` of challenge types;
  `drOf f ds`: the block samplers, one for each round;
  `g0Of f ds`: the bits of work, on the shape of `Qv` (all three in Run/PlanPullProto.lean);
  `.pull`, `.grind` on `Qv ..`: the protocol pulled back along the samplers, the protocol with tests
    (Iop/Pull.lean, Iop/Grind.lean);
  `ptOfv f ds`: the records that each round's oracle message is given by its symbols
    (`Shape.IsPoint`, Iop/Shape.lean);
  `npOfv f ds`: for each round a numbering of its oracle positions (`Shape.NumPos`, Iop/Num.lean);
  `PQ.Dn`: the honest search's record (Run/PlanQWire.lean).

Limits: this file does not say that K is dr.K (the greatest number of blocks of a round): `data_K`,
Run/PlanPullData.lean [not in this library]. The interface; its Link and Batch; the prover's wiring; a `DataK`, a `Work`:
none is written down here (Run/PlanPullFace.lean, Run/PlanPullData.lean [not in this library] have them). The wiring with
pruned openings (the form in which openings stand in the files) is not of this form. This file says
nothing on any number.
The run functions of the generic construction stand at the interface `PQ.LbS` (Run/PlanQS.lean), not
at the one for which this file was written: this protocol is `PQ.LbS`'s Batch, this wiring the field
B of its wiring (in the theorems vbsPF_* of Run/M1RunTiePF.lean and Run/M2Tie.lean; `Wb`,
Run/PlanQS.lean). An interface whose Test is this protocol is `PQ.LtS` (Run/PlanQS.lean).
The library's terms on the right of the statement are those of an interface's Test (local forms);
its generic forms for Batch (`BatchInteractiveOracleProof.grind`, `ProtocolQueryLayout.ofDraws`, `ProtocolQueryLayout.grind`) are other terms
at a round with work: no equation with them is stated.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanPullProto
import Run.PlanPullWireT

set_option autoImplicit false

namespace Run
open Prob Iop

/-- the round in front: its (empty) oracle message is given by its symbols -/
def pt0 (C : PQ.CK) : ((PQ.s0 C).up).IsPoint :=
  ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩

/-- the numbering of no position -/
def np0 : Empty ≃ Fin (Fintype.card Empty) :=
  ⟨fun p => p.elim, fun i => absurd i.isLt (by simp),
    fun p => p.elim, fun i => absurd i.isLt (by simp)⟩

def ptL (f : _root_.Fmt.Fld) : (ds : List PQ.RD) → (PQ.shapeL (ck f) ds).IsPoint
  | [] => ()
  | d :: ds => (PQ.ptOf (ck f) d, ptL f ds)

def npL (f : _root_.Fmt.Fld) : (ds : List PQ.RD) → (PQ.shapeL (ck f) ds).NumPos (ptL f ds)
  | [] => ()
  | d :: ds => (npOf d.tree, npL f ds)

def ptOfv (f : _root_.Fmt.Fld) (ds : List PQ.RD) :
    Shape.IsPoint ((PQ.s0 (ck f)).up :: PQ.shapeL (ck f) ds) :=
  (pt0 (ck f), ptL f ds)

def npOfv (f : _root_.Fmt.Fld) (ds : List PQ.RD) :
    Shape.NumPos ((PQ.s0 (ck f)).up :: PQ.shapeL (ck f) ds) (ptOfv f ds) := (np0, npL f ds)

def Spec.planPull_wq : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) (dec : PQ.View → Bool),
    (⟨(PQ.PSof (ckP f) ds dec).up, PQ.wqSF (ckP f) K (chalP f K) ds dec⟩ :
        Σ Q : BatchInteractiveOracleProof Unit PQ.E0, ProtocolQueryLayout 256 (K + 1) Q) =
      ⟨BatchInteractiveOracleProof.ofProto
          (((Qv (ck f) ds dec).pull (Samplers.ofDraws _ (drOf f ds))).grind
            ℕ ((g0Of f ds).pull (Samplers.ofDraws _ (drOf f ds)))),
        (ProtocolQueryLayout.ofLocalD 256 K (Qv (ck f) ds dec) (ptOfv f ds) (drOf f ds) (npOfv f ds)
            (WireE.one 0 Unit ()) (PQ.nOpen ds) (Nat.clog 2 0)).grindLocal
          PQ.Dn ((g0Of f ds).pull (Samplers.ofDraws _ (drOf f ds)))⟩

end Run
