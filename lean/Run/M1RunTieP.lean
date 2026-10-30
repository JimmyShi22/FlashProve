-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunTieP.lean: the equations of Run/M1RunTie.lean with challenges as hash blocks, where the
wiring also meets the library's conditions on a wiring.

Run/M1RunTie.lean has its equations in a form in which a round's verifier message is the drawn
values: the wiring applies each round's sampler. There the library's law "verifier messages are
exactly uniform" fails at every round that draws a field element. In the form used here
(Run/PlanPull.lean: `ckP`, `chalP`) a round's verifier message is its own hash blocks, and the view
applies the sampler. Then the law holds.

Two interfaces, as in Run/M1RunTie.lean. The run functions are at the interface `LbS`, whose Batch
is the protocol; the wirings W* and their laws are stated at `LtS`, whose Test is the same
protocol; W.T is the field B of Wb W.K W.T.

1. What the file contains.
   A, B, T, F, R, K: the six descriptions of Run/M1RunTie.lean: this library's own small sizes
     (K = 4, K = 3); the programs' tiny parameters (22 rounds) and full parameters (30 rounds). R
     and K are the very terms at which other tests run (`Fmt.M1.KnownR.spec`, `KnownF.spec`).
   W*: the wiring of LtS (ckP ..) ..: Test's wiring is wqS (ckP ..) (kOf S) (chalP ..) ..; Link and
     Batch have no rounds.

2. What is checked when the file compiles. Two tests (#guard): at A and at T the honest file is
accepted by `runLaxSP` and by `runStrictSP`. For each description the kernel evaluates "every round
asks for at most 64 bits of work".

3. Theorems. Many statements of this library are written twice: a definition in the namespace `Spec`
   states a proposition, and a theorem of the same name outside that namespace proves it
   (lean/GLOSSARY.md).
   `vbsP_A` to `vbsP_K`: for all cm, π: VPP S dec cm π = (vBS (Wb W.K W.T) (256 + 8 · the salt's
     bytes) 256 cm () π).det (famP ..). No cast; the proof is `vpp_eq` of Run/PlanQSP.lean.
   `okgP_A` to `okgP_K`: W.T.OKG: the library's laws of a wiring whose rounds may have tests of
     work: places and depths, exactly uniform verifier messages, the records of the tests. By
     `planPull_okg` of Run/PlanPull.lean; every round's number of blocks is at most kOf S.

4. What is not claimed, or stands elsewhere.
   The laws of the whole wiring (W.OKG) and the interface's conditions of form (local, coherent,
   read symbol by symbol): Run/M1Door.lean. The protocol's own properties (an honest prover that is
   accepted, hiding, soundness for a named relation) are not shown there either; its head names
   them.
   No statement on soundness follows. With an encoded index of length 0, what a theorem says about
   the language of an accepted string is empty.
   That the two forms give one verdict on every file:
     for the two run functions behind the lenient reader (the reader that leaves work and openings
       to the verifier; what the lenient reader still asks the hash, what it refuses and what it
       does not test: part 1 of the head of Run/ParseLax.lean) it is a theorem of another file
       (Run/PageIsRunProofs.lean: `run_two`: ok S and smallB S file give
       runLaxS S dec file = runLaxSP S dec file);
     for the run functions behind the strict reader it is only tested.
   It is not claimed that the decision is the one that the programs compute.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSP
import Run.PlanPullM1
import Run.M1RunTie

set_option autoImplicit false

namespace Run.M1RunTieP
open Iop Rom Compile Compile.Batch Run.PQ

/-- the laws of the wiring with challenges as hash blocks (`ckP`), from a test on the description
that the kernel evaluates (`h`: every round asks for at most 64 bits of work) -/
theorem okgOf (S : _root_.Fmt.Spec) (dec : View → Bool)
    (h : (rds S).all (fun d => decide (d.entry.work ≤ 64)) = true) :
    (wqS (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) (rds S) dec).OKG :=
  planPull_okg S.plan.field (kOf S) (rds S) dec
    (le_kMax (fun e k => (bsRound S.plan.field e k).b) (rds S))
    fun d hd => of_decide_eq_true (List.all_eq_true.1 h d hd)

/-! ## This library's own small size, K = 4 -/

abbrev SA : _root_.Fmt.Spec := _root_.Fmt.M1.Known.spec
abbrev dA : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.Known.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks -/
def WA : QueryLayout 256 (LtS (ckP SA.plan.field) (rds SA) dA) where
  K := kOf SA + 1
  T := wqS (ckP SA.plan.field) (kOf SA) (chalP SA.plan.field (kOf SA)) (rds SA) dA
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsP_A : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SA.plan.field) (rds SA) dA).up), VPP SA dA cm π =
    (vBS (Wb WA.K WA.T) (256 + 8 * SA.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SA.plan.field) (rds SA) dA) _root_.Fmt.oracle
        (PDS SA (ckP SA.plan.field) dA) (kOf SA + 1))

theorem vbsP_A : Spec.vbsP_A := fun cm π => vpp_eq SA dA cm π

theorem work_A : (rds SA).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgP_A : Prop := WA.T.OKG

theorem okgP_A : Spec.okgP_A := okgOf SA dA work_A

/-! ## This library's own small size, K = 3 -/

abbrev SB : _root_.Fmt.Spec := _root_.Fmt.M1.KnownB.spec
abbrev dB : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownB.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks -/
def WB : QueryLayout 256 (LtS (ckP SB.plan.field) (rds SB) dB) where
  K := kOf SB + 1
  T := wqS (ckP SB.plan.field) (kOf SB) (chalP SB.plan.field (kOf SB)) (rds SB) dB
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsP_B : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SB.plan.field) (rds SB) dB).up), VPP SB dB cm π =
    (vBS (Wb WB.K WB.T) (256 + 8 * SB.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SB.plan.field) (rds SB) dB) _root_.Fmt.oracle
        (PDS SB (ckP SB.plan.field) dB) (kOf SB + 1))

theorem vbsP_B : Spec.vbsP_B := fun cm π => vpp_eq SB dB cm π

theorem work_B : (rds SB).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgP_B : Prop := WB.T.OKG

theorem okgP_B : Spec.okgP_B := okgOf SB dB work_B

/-! ## The programs' tiny parameters -/

abbrev ST : _root_.Fmt.Spec := _root_.Fmt.M1.KnownT.spec
abbrev dT : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownT.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks -/
def WT : QueryLayout 256 (LtS (ckP ST.plan.field) (rds ST) dT) where
  K := kOf ST + 1
  T := wqS (ckP ST.plan.field) (kOf ST) (chalP ST.plan.field (kOf ST)) (rds ST) dT
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsP_T : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP ST.plan.field) (rds ST) dT).up), VPP ST dT cm π =
    (vBS (Wb WT.K WT.T) (256 + 8 * ST.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP ST.plan.field) (rds ST) dT) _root_.Fmt.oracle
        (PDS ST (ckP ST.plan.field) dT) (kOf ST + 1))

theorem vbsP_T : Spec.vbsP_T := fun cm π => vpp_eq ST dT cm π

theorem work_T : (rds ST).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgP_T : Prop := WT.T.OKG

theorem okgP_T : Spec.okgP_T := okgOf ST dT work_T

/-! ## The programs' full parameters (`toyPar`: the sizes of the first toy, a product test, at
these parameters: Fmt/M1Plan.lean; tests (#guard) of Fmt/M1Theirs.lean hold them against the
programs' parameter bytes; `SF` is the defining term of `Fmt.M1.Theirs.specFull`,
Fmt/M1TheirsSpec.lean) -/

abbrev SF : _root_.Fmt.Spec :=
  _root_.Fmt.M1.specOf _root_.Fmt.M1.toyPar (_root_.Fmt.configDigest [_root_.Fmt.M1.Theirs.pubFull])
    (_root_.Fmt.M1.itemsOf _root_.Fmt.M1.toyPar)
abbrev dF : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.toyPar

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks -/
def WF : QueryLayout 256 (LtS (ckP SF.plan.field) (rds SF) dF) where
  K := kOf SF + 1
  T := wqS (ckP SF.plan.field) (kOf SF) (chalP SF.plan.field (kOf SF)) (rds SF) dF
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsP_F : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SF.plan.field) (rds SF) dF).up), VPP SF dF cm π =
    (vBS (Wb WF.K WF.T) (256 + 8 * SF.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SF.plan.field) (rds SF) dF) _root_.Fmt.oracle
        (PDS SF (ckP SF.plan.field) dF) (kOf SF + 1))

theorem vbsP_F : Spec.vbsP_F := fun cm π => vpp_eq SF dF cm π

theorem work_F : (rds SF).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgP_F : Prop := WF.T.OKG

theorem okgP_F : Spec.okgP_F := okgOf SF dF work_F

/-! ## The programs' tiny parameters, with their own random bytes in the files: the description at
which other tests run -/

abbrev SR : _root_.Fmt.Spec := _root_.Fmt.M1.KnownR.spec
abbrev dR : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownR.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks -/
def WR : QueryLayout 256 (LtS (ckP SR.plan.field) (rds SR) dR) where
  K := kOf SR + 1
  T := wqS (ckP SR.plan.field) (kOf SR) (chalP SR.plan.field (kOf SR)) (rds SR) dR
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsP_R : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SR.plan.field) (rds SR) dR).up), VPP SR dR cm π =
    (vBS (Wb WR.K WR.T) (256 + 8 * SR.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SR.plan.field) (rds SR) dR) _root_.Fmt.oracle
        (PDS SR (ckP SR.plan.field) dR) (kOf SR + 1))

theorem vbsP_R : Spec.vbsP_R := fun cm π => vpp_eq SR dR cm π

theorem work_R : (rds SR).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgP_R : Prop := WR.T.OKG

theorem okgP_R : Spec.okgP_R := okgOf SR dR work_R

/-! ## The programs' full parameters: the description at which other tests run -/

abbrev SK : _root_.Fmt.Spec := _root_.Fmt.M1.KnownF.spec
abbrev dK : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.KnownF.par

/-- the wiring of the interface whose Test is this protocol, with challenges as hash blocks -/
def WK : QueryLayout 256 (LtS (ckP SK.plan.field) (rds SK) dK) where
  K := kOf SK + 1
  T := wqS (ckP SK.plan.field) (kOf SK) (chalP SK.plan.field (kOf SK)) (rds SK) dK
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsP_K : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SK.plan.field) (rds SK) dK).up), VPP SK dK cm π =
    (vBS (Wb WK.K WK.T) (256 + 8 * SK.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SK.plan.field) (rds SK) dK) _root_.Fmt.oracle
        (PDS SK (ckP SK.plan.field) dK) (kOf SK + 1))

theorem vbsP_K : Spec.vbsP_K := fun cm π => vpp_eq SK dK cm π

theorem work_K : (rds SK).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.okgP_K : Prop := WK.T.OKG

theorem okgP_K : Spec.okgP_K := okgOf SK dK work_K

#guard runLaxSP SA dA _root_.Fmt.M1.Files.honest == .accepted && runStrictSP SA dA _root_.Fmt.M1.Files.honest == .accepted
#guard runLaxSP ST dT _root_.Fmt.M1.FilesT.honest == .accepted && runStrictSP ST dT _root_.Fmt.M1.FilesT.honest == .accepted

end Run.M1RunTieP
