-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunTiePF.lean: at the first toy and the programs' own parameters, what is run with challenges
as hash blocks and whole paths is the function that the scheme's verifier runs on a proof string.

The first toy is a product test. "The programs" are the C++ implementation that comes with this
Lean code. Three descriptions are meant: the tiny parameters; the tiny parameters under the name at
which the files with the programs' own random bytes are tested (`KnownR`); the full parameters.
They are the very terms of the tests in Run/PlanQSFPM1T.lean, Run/PlanQSFPM1R.lean and
Run/PlanQSFPM1F.lean: `Fmt.M1.KnownT`, `KnownR`, `KnownF`. This file is a companion of
Run/M1RunTieP.lean, whose wirings have pruned openings.

An interface is the library's record of three protocols, called Test, Link and Batch, with an
encoding and a decoding of an index; the compiler's theorems speak of the verifiers at these three.
With challenges as hash blocks a round's verifier message is its own hash blocks, and the view
applies the sampler. Whole paths: each opened leaf has an authentication path of its own (in the
code: without the flag for pruned sets, `prJ`). Pruned openings: the opened leaves of a tree share
one set of sibling digests.

1. What the file contains.
   `WT`, `WR`, `WF`: a wiring of a whole interface (`LtS`, whose Test protocol is the toy). Test's
     wiring is `wqSF` of Run/PlanQSF.lean (whole paths) at `ckP`, `chalP` of Run/PlanPull.lean
     (challenges as hash blocks). Link and Batch have no round.

2. What is checked when the file compiles. Nothing beyond the proofs. One side condition on each
closed description (no round asks for more than 64 bits of work) is decided by the kernel.

3. Theorems (statements Run.M1RunTiePF.Spec.*).
   `vbsPF_T`, `vbsPF_R`, `vbsPF_F`: for every cm and π: VPFP S dec cm π = (vBS (Wb W.K W.T)
     (256 + 8 · the salt's bytes) 256 cm () π).det (famP ..). Here `Compile.Batch.vBS` is the
     function that the scheme's verifier runs on the proof string of one slot of a batch, at the
     interface `LbS` (Run/PlanQS.lean; the tag "onl"), whose Batch protocol is the toy. No cast is
     needed: at a closed list of rounds the two annotations are the same by definition.
   `okgPF_T`, `okgPF_R`, `okgPF_F`: W.T.OKG, the conditions on that one protocol's wiring: places
     and depths, exactly uniform verifier messages, the records of the tests. Run/PlanPull.lean
     proves them (`planPull_okg`, under the hypotheses of its statement) for the wiring with pruned
     openings; Run/PlanQSFLaws.lean carries them over, since no condition names the flag for pruned
     sets. They are stated at the interface `LtS`, where the wiring is Test's. The same record is
     the field B of the wiring Wb at which the runs stand.

4. What is not claimed.
   W.OKG as a whole, and the interface's other conditions (local, sound, hiding), are not shown in
   this file. When it was written they were shown nowhere. The formal conditions of the record `Met`
   (Run/M1Door.lean) on the whole interface and on its wiring are met at these descriptions
   (Run/BatchDoor.lean: `metBF_T`, `metBF_R`, `metBF_F`; at the interface `LtS`: Run/M1Door.lean:
   `metF_T`, `metF_R`, `metF_F`). The two conditions on soundness (`sound`, `low` of `Met`,
   Run/M1Door.lean) hold there only at the relation "everything", where they are empty.
   Round-by-round knowledge soundness for a relation with content is shown nowhere in Run/ or Fmt/.
   No statement on soundness follows. "The scheme's verifier" and "sound" may not be said of these
   runs. Completeness is not met: the honest sides are placeholders (Run/BatchDoor.lean). Hiding
   (the field `hidden` of `BatchProtocol.Props`, Iop/Batch.lean) is not shown of these interfaces (`LbS`,
   `LtS`), in this file or elsewhere in Run/.
   The encoded index has length 0, so what a theorem would say of an accepted string is empty.
   It is not shown that this wiring is one of those in the compiler's top theorems, but for this:
     at `LtS`, interface and wiring as a pair are those of the library's compilation with work at
       data that are written down (Run/PlanPullJoin.lean [not in this library]: `join_T`, `join_R`, `join_F`; nothing
       with content follows: its head, 4);
   of `Wb` at `LbS`, at which the runs stand, it is not shown. In these theorems depths come from a
   cardinality and places from the library's numbering; beyond Run/PlanPullWire.lean
   (`planPull_depth`, `planPull_wire`), Run/PlanPullWireT.lean, Run/PlanPullWq.lean,
   Run/PlanPullData.lean [not in this library], Run/PlanPullFace.lean and Run/PlanPullJoin.lean [not in this library] the two have not been
   compared.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSFP
import Run.PlanQSFLaws
import Run.M1RunTieP
import Fmt.M1PlanKnownR
import Fmt.M1PlanKnownF

set_option autoImplicit false

namespace Run.M1RunTiePF
open Iop Rom Compile Compile.Batch Run.PQ

/-- the laws of the wiring without the flag for pruned sets, with challenges as hash blocks (`ckP`),
from a test on the description that the kernel evaluates (`h`: no round asks for more than 64 bits
of work) -/
theorem okgFOf (S : _root_.Fmt.Spec) (dec : View → Bool)
    (h : (rds S).all (fun d => decide (d.entry.work ≤ 64)) = true) :
    (wqSF (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) (rds S) dec).OKG :=
  wqSF_okg _ _ _ _ _ (M1RunTieP.okgOf S dec h)

/-! ## The programs' tiny parameters -/

abbrev ST : _root_.Fmt.Spec := _root_.Fmt.M1.KnownT.spec
abbrev dT : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownT.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks; Test's
wiring without the flag for pruned sets -/
def WT : QueryLayout 256 (LtS (ckP ST.plan.field) (rds ST) dT) where
  K := kOf ST + 1
  T := wqSF (ckP ST.plan.field) (kOf ST) (chalP ST.plan.field (kOf ST)) (rds ST) dT
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsPF_T : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP ST.plan.field) (rds ST) dT).up), VPFP ST dT cm π =
    (vBS (Wb WT.K WT.T) (256 + 8 * ST.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP ST.plan.field) (rds ST) dT) _root_.Fmt.oracle
        (PDS ST (ckP ST.plan.field) dT) (kOf ST + 1))

theorem vbsPF_T : Spec.vbsPF_T := fun cm π => vpfp_eq ST dT cm π

theorem work_T : (rds ST).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgPF_T : Prop := WT.T.OKG

theorem okgPF_T : Spec.okgPF_T := okgFOf ST dT work_T

/-! ## The tiny parameters, under the name `KnownR` -/

abbrev SR : _root_.Fmt.Spec := _root_.Fmt.M1.KnownR.spec
abbrev dR : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownR.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks; Test's
wiring without the flag for pruned sets -/
def WR : QueryLayout 256 (LtS (ckP SR.plan.field) (rds SR) dR) where
  K := kOf SR + 1
  T := wqSF (ckP SR.plan.field) (kOf SR) (chalP SR.plan.field (kOf SR)) (rds SR) dR
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsPF_R : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SR.plan.field) (rds SR) dR).up), VPFP SR dR cm π =
    (vBS (Wb WR.K WR.T) (256 + 8 * SR.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SR.plan.field) (rds SR) dR) _root_.Fmt.oracle
        (PDS SR (ckP SR.plan.field) dR) (kOf SR + 1))

theorem vbsPF_R : Spec.vbsPF_R := fun cm π => vpfp_eq SR dR cm π

theorem work_R : (rds SR).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgPF_R : Prop := WR.T.OKG

theorem okgPF_R : Spec.okgPF_R := okgFOf SR dR work_R

/-! ## The full parameters -/

abbrev SF : _root_.Fmt.Spec := _root_.Fmt.M1.KnownF.spec
abbrev dF : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownF.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks; Test's
wiring without the flag for pruned sets -/
def WF : QueryLayout 256 (LtS (ckP SF.plan.field) (rds SF) dF) where
  K := kOf SF + 1
  T := wqSF (ckP SF.plan.field) (kOf SF) (chalP SF.plan.field (kOf SF)) (rds SF) dF
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsPF_F : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SF.plan.field) (rds SF) dF).up), VPFP SF dF cm π =
    (vBS (Wb WF.K WF.T) (256 + 8 * SF.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SF.plan.field) (rds SF) dF) _root_.Fmt.oracle
        (PDS SF (ckP SF.plan.field) dF) (kOf SF + 1))

theorem vbsPF_F : Spec.vbsPF_F := fun cm π => vpfp_eq SF dF cm π

theorem work_F : (rds SF).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgPF_F : Prop := WF.T.OKG

theorem okgPF_F : Spec.okgPF_F := okgFOf SF dF work_F

end Run.M1RunTiePF
