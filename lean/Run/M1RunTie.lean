-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunTie.lean: at six descriptions of the first toy, what is evaluated behind the reader is the
function that the scheme's verifier applies to a proof's string. (Behind the reader: the reader
first, then the verifier on what it hands out.)

The first toy is a product test. The programs (the C++ implementation that comes with this Lean
code) write proof files for it. Run/PlanQS.lean turns a description of the proof's rounds into a
protocol of the library, a wiring (the data that say how deep the trees are, where a position
stands among a tree's leaves, and how blocks of a hash answer give a verifier message), and a
verifier `VP` that can be evaluated. It proves, for every description: VP S dec cm π =
(Compile.Batch.verifyOneProtocol .. (PSof ..).up (wqS ..) .. [cm] () π).det (famP ..). This file goes one
step further at six closed descriptions: that term is `Compile.Batch.vBS`, the function that the
scheme's verifier runs on a proof's string for a slot of a batch, at an interface whose Batch is
the toy's protocol. (`OComp.det`, Rom/Cache.lean: the run's result under the oracle functions,
every coin toss yielding 0.) (`famP`: the typed oracle functions that a function on the format's
strings, here `Fmt.oracle`, induces; Run/CodingFnThin.lean.)

Why only at closed descriptions. Compile.Batch.vBS W .. is by definition `verifyOneProtocol` at the
interface's Batch and at the wiring's field B. For a variable list of rounds, the annotation that
Run/PlanQS.lean uses and the library's are equal only by induction (Run/PlanQSLaws.lean:
`psof_up`), so the two terms have different types. At a closed description they are the same by
definition: the equations below typecheck without a cast, and Lean accepts Run/PlanQS.lean's `vp_eq`
as their proof.

Two interfaces. The equations are stated at the interface `LbS`, whose Batch is the protocol
(Run/PlanQS.lean; the tag "onl"). The wirings W* below are stated at `LtS`, whose Test is the same
protocol; their field T is the field B of the wiring Wb W.K W.T at `LbS` (Run/BatchS.lean:
`batch_same`). No law of a wiring is stated of these W* (why: the head of Run/M1RunTieP.lean).

1. What the file contains. Six descriptions with a wiring for each.
   A: this library's own small sizes, K = 4 (Fmt/M1PlanKnown.lean): 22 rounds.
   B: this library's own small sizes, K = 3 (Fmt/M1PlanKnownB.lean): 21 rounds.
   T: the programs' tiny parameters (Fmt/M1PlanKnownT.lean): 22 rounds.
   F: the programs' full parameters (Fmt/M1Theirs.lean, where the parameter bytes are tested byte
     for byte): 30 rounds.
   R, K: the very terms at which other tests in this library run: `Fmt.M1.KnownR.spec` and
     `Fmt.M1.KnownF.spec`.
   W*: the wiring of LtS ..: Test's wiring is wqS ..; Link and Batch have no rounds.

2. What is checked when the file compiles. Five tests (#guard): the numbers of rounds (22, 21, 22,
30; 22, 30); the sizes' K at A, B, T; the parameter bytes of F and K are the programs' full
parameters, those of R and T their tiny parameters; all six descriptions are within the limits
(`ok`).

3. Theorems.
   `vbs_A`, `vbs_B`, `vbs_T`, `vbs_F`, `vbs_R`, `vbs_K`: for all cm, π: VP S dec cm π = (vBS
     (Wb W.K W.T) (256 + 8 · the salt's bytes) 256 cm () π).det (famP ..), with dec := Fmt.M1.dec
     at the sizes.

4. What may be said, and what is not claimed.
   Of a file that `runLaxS` or `runStrictS` accepts at one of these descriptions one may say: "its
   typed string is accepted by the function that the scheme's verifier runs on a proof's string for
   a slot, at an interface whose Batch is this protocol, with the format's hash behind the typed
   oracles".
   One may not say "by the scheme's verifier": that also judges a key's Test string and a Link
   string (Run/BatchS.lean says what it is when these two are constants).
   No statement on soundness follows. No law of the interface is shown here. The interface has no
   index (an encoded index of length 0), so what the library's theorems say about the language of
   an accepted string is empty (Run/BatchDoor.lean).
   No file is judged here: Run/M1Run.lean and the files with tests.
   It is not claimed that the decision is the one that the programs compute. It is one reading of
   the programs' description of the toy.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSLaws
import Run.M1Run
import Fmt.M1PlanKnownT
import Fmt.M1PlanKnownR
import Fmt.M1PlanKnownF

set_option autoImplicit false

namespace Run.M1RunTie
open Iop Rom Compile Compile.Batch Run.PQ

/-! ## This library's own small size, K = 4 -/

abbrev SA : _root_.Fmt.Spec := _root_.Fmt.M1.Known.spec
abbrev dA : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.Known.par

/-- the wiring of the interface whose Test is this protocol -/
def WA : QueryLayout 256 (LtS (ck SA.plan.field) (rds SA) dA) where
  K := kOf SA + 1
  T := wqS (ck SA.plan.field) (kOf SA) (chalOf SA.plan.field (kOf SA)) (rds SA) dA
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_A : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SA.plan.field) (rds SA) dA).up), VP SA dA cm π =
    (vBS (Wb WA.K WA.T) (256 + 8 * SA.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SA.plan.field) (rds SA) dA) _root_.Fmt.oracle
        (PDS SA (ck SA.plan.field) dA) (kOf SA + 1))

theorem vbs_A : Spec.vbs_A := fun cm π => vp_eq SA dA cm π

/-! ## This library's own small size, K = 3 -/

abbrev SB : _root_.Fmt.Spec := _root_.Fmt.M1.KnownB.spec
abbrev dB : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownB.par

/-- the wiring of the interface whose Test is this protocol -/
def WB : QueryLayout 256 (LtS (ck SB.plan.field) (rds SB) dB) where
  K := kOf SB + 1
  T := wqS (ck SB.plan.field) (kOf SB) (chalOf SB.plan.field (kOf SB)) (rds SB) dB
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_B : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SB.plan.field) (rds SB) dB).up), VP SB dB cm π =
    (vBS (Wb WB.K WB.T) (256 + 8 * SB.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SB.plan.field) (rds SB) dB) _root_.Fmt.oracle
        (PDS SB (ck SB.plan.field) dB) (kOf SB + 1))

theorem vbs_B : Spec.vbs_B := fun cm π => vp_eq SB dB cm π

/-! ## The programs' tiny parameters -/

abbrev ST : _root_.Fmt.Spec := _root_.Fmt.M1.KnownT.spec
abbrev dT : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownT.par

/-- the wiring of the interface whose Test is this protocol -/
def WT : QueryLayout 256 (LtS (ck ST.plan.field) (rds ST) dT) where
  K := kOf ST + 1
  T := wqS (ck ST.plan.field) (kOf ST) (chalOf ST.plan.field (kOf ST)) (rds ST) dT
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_T : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck ST.plan.field) (rds ST) dT).up), VP ST dT cm π =
    (vBS (Wb WT.K WT.T) (256 + 8 * ST.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck ST.plan.field) (rds ST) dT) _root_.Fmt.oracle
        (PDS ST (ck ST.plan.field) dT) (kOf ST + 1))

theorem vbs_T : Spec.vbs_T := fun cm π => vp_eq ST dT cm π

/-! ## The programs' full parameters (`toyPar`: the sizes of the first toy, a product test, at
these parameters: Fmt/M1Plan.lean; tests (#guard) of Fmt/M1Theirs.lean hold them against the
programs' parameter bytes; `SF` is the defining term of `Fmt.M1.Theirs.specFull`,
Fmt/M1TheirsSpec.lean) -/

abbrev SF : _root_.Fmt.Spec :=
  _root_.Fmt.M1.specOf _root_.Fmt.M1.toyPar (_root_.Fmt.configDigest [_root_.Fmt.M1.Theirs.pubFull])
    (_root_.Fmt.M1.itemsOf _root_.Fmt.M1.toyPar)
abbrev dF : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.toyPar

/-- the wiring of the interface whose Test is this protocol -/
def WF : QueryLayout 256 (LtS (ck SF.plan.field) (rds SF) dF) where
  K := kOf SF + 1
  T := wqS (ck SF.plan.field) (kOf SF) (chalOf SF.plan.field (kOf SF)) (rds SF) dF
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_F : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SF.plan.field) (rds SF) dF).up), VP SF dF cm π =
    (vBS (Wb WF.K WF.T) (256 + 8 * SF.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SF.plan.field) (rds SF) dF) _root_.Fmt.oracle
        (PDS SF (ck SF.plan.field) dF) (kOf SF + 1))

theorem vbs_F : Spec.vbs_F := fun cm π => vp_eq SF dF cm π

/-! ## The programs' tiny parameters, with their own random bytes in the files: the description at
which other tests in this library run -/

abbrev SR : _root_.Fmt.Spec := _root_.Fmt.M1.KnownR.spec
abbrev dR : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownR.par

/-- the wiring of the interface whose Test is this protocol -/
def WR : QueryLayout 256 (LtS (ck SR.plan.field) (rds SR) dR) where
  K := kOf SR + 1
  T := wqS (ck SR.plan.field) (kOf SR) (chalOf SR.plan.field (kOf SR)) (rds SR) dR
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_R : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SR.plan.field) (rds SR) dR).up), VP SR dR cm π =
    (vBS (Wb WR.K WR.T) (256 + 8 * SR.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SR.plan.field) (rds SR) dR) _root_.Fmt.oracle
        (PDS SR (ck SR.plan.field) dR) (kOf SR + 1))

theorem vbs_R : Spec.vbs_R := fun cm π => vp_eq SR dR cm π

/-! ## The programs' full parameters: the description at which other tests in this library run -/

abbrev SK : _root_.Fmt.Spec := _root_.Fmt.M1.KnownF.spec
abbrev dK : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownF.par

/-- the wiring of the interface whose Test is this protocol -/
def WK : QueryLayout 256 (LtS (ck SK.plan.field) (rds SK) dK) where
  K := kOf SK + 1
  T := wqS (ck SK.plan.field) (kOf SK) (chalOf SK.plan.field (kOf SK)) (rds SK) dK
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_K : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SK.plan.field) (rds SK) dK).up), VP SK dK cm π =
    (vBS (Wb WK.K WK.T) (256 + 8 * SK.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SK.plan.field) (rds SK) dK) _root_.Fmt.oracle
        (PDS SK (ck SK.plan.field) dK) (kOf SK + 1))

theorem vbs_K : Spec.vbs_K := fun cm π => vp_eq SK dK cm π

/-! ## The sizes that the head names -/

#guard (rds SA).length = 22 && (rds SB).length = 21 && (rds ST).length = 22 && (rds SF).length = 30
#guard _root_.Fmt.M1.Known.par.K = 4 && _root_.Fmt.M1.KnownB.par.K = 3 && _root_.Fmt.M1.KnownT.par.K = 4
#guard SF.params = _root_.Fmt.M1.Theirs.full
#guard ok SA && ok SB && ok ST && ok SF && ok SR && ok SK
#guard (rds SR).length = 22 && (rds SK).length = 30 && SK.params = _root_.Fmt.M1.Theirs.full && SR.params = _root_.Fmt.M1.Theirs.tiny && ST.params = _root_.Fmt.M1.Theirs.tiny

end Run.M1RunTie
