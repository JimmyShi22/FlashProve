-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunTieTheirs.lean: proves two facts of other files again, at the very names at which the
programs' own files are judged in Run/M1Engine*.lean. First, at these names what is evaluated on a
proof's string equals the run of `Compile.Batch.vBS` (the equations of Run/M1RunTie.lean and
Run/M1RunTieP.lean). Second, at these names and with challenges as hash blocks, the record `Met` of
formal side conditions on interface and wiring holds (the conditions of Run/M1Door.lean).
`Compile.Batch.vBS` is the function that the scheme's verifier runs on the proof string of one slot
(Compile/Batch/Verifier.lean).

The tests of Run/M1Engine*.lean on the programs' files of the first toy run at
`Fmt.M1.Theirs.specTiny` / `sizesTiny` and `Fmt.M1.Theirs.specFull` / `sizesFull`. "Theirs": the
programs' own parameters, tiny and full. Run/M1RunTie.lean, Run/M1RunTieP.lean and Run/M1Door.lean
state the same facts at other spellings of the same two descriptions.
(Fmt/M1TheirsSpec.lean: `known_T`, `known_R`, `known_F`: the spec and par of `KnownT`, `KnownR`,
`KnownF` are these; specFull's defining term is the description F of Run/M1RunTie.lean. Not among
them: specFrom of the parameter bytes, which is compared with these there by tests, field by field,
without a theorem.) Here nothing has to be carried over: the terms are, letter for letter, those of
the tests of Run/M1Engine*.lean.

Two interfaces, as in Run/M1RunTie.lean. The run functions stand at the interface `LbS`, whose
Batch is the protocol; the wirings V* and W*, and the laws of W* (`met_N`, `met_M`), are stated at
`LtS`, whose Test is the same protocol; V.T is the field B of Wb V.K V.T, and W.T of Wb W.K W.T.

1. What the file contains. Four wirings.
   N: the tiny parameters: S := Theirs.specTiny, dec := Fmt.M1.dec Theirs.sizesTiny (22 rounds).
   M: the full parameters: S := Theirs.specFull, dec := Fmt.M1.dec Theirs.sizesFull (30 rounds).

2. What is checked when the file compiles. Two tests (#guard): the parameter bytes of N and M are
the programs' tiny and full parameters; 22 and 30 rounds; both descriptions are within the limits.
For each description the kernel evaluates "every round asks for at most 64 bits of work" (`work_N`,
`work_M`).

3. Theorems. Many statements of this library are written twice: a definition in the namespace `Spec`
states a proposition, and a theorem of the same name outside that namespace proves it
(lean/GLOSSARY.md).
   `vbs_N`, `vbs_M`: for all cm, π: VP S dec cm π = (vBS (Wb V.K V.T) ..).det (famP ..). Challenges
     as sampled values (`runStrictS`, `runLaxS`).
   `vbsP_N`, `vbsP_M`: for all cm, π: VPP S dec cm π = (vBS (Wb W.K W.T) ..).det (famP ..).
     Challenges as hash blocks (`runStrictSP`, `runLaxSP`).
   `met_N`, `met_M`: the record `Met` of Run/M1Door.lean at W: the whole wiring obeys the library's
     laws; wired, reads, local, coherent, read symbol by symbol. Its fields `sound` and `low` are
     true and empty, as that file's head explains.

4. What may be said, and what is not claimed. For a file that these functions accept, see part 4 of
the head of Run/M1RunTie.lean and of the head of Run/M1Door.lean. No statement on soundness
follows. No file is judged here. It is not claimed that the decision is the one that the programs
compute: it is one reading of the programs' description of the toy, compared with their files by
tests elsewhere.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.M1Door
import Fmt.M1TheirsSpec

set_option autoImplicit false

namespace Run.M1RunTieTheirs
open Iop Rom Compile Compile.Batch Run.PQ

/-! ## The tiny parameters -/

abbrev SN : _root_.Fmt.Spec := _root_.Fmt.M1.Theirs.specTiny
abbrev dN : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.Theirs.sizesTiny

/-- the wiring with challenges as sampled values -/
def VN : QueryLayout 256 (LtS (ck SN.plan.field) (rds SN) dN) where
  K := kOf SN + 1
  T := wqS (ck SN.plan.field) (kOf SN) (chalOf SN.plan.field (kOf SN)) (rds SN) dN
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

/-- the wiring with challenges as hash blocks -/
def WN : QueryLayout 256 (LtS (ckP SN.plan.field) (rds SN) dN) where
  K := kOf SN + 1
  T := wqS (ckP SN.plan.field) (kOf SN) (chalP SN.plan.field (kOf SN)) (rds SN) dN
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_N : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SN.plan.field) (rds SN) dN).up), VP SN dN cm π =
    (vBS (Wb VN.K VN.T) (256 + 8 * SN.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SN.plan.field) (rds SN) dN) _root_.Fmt.oracle
        (PDS SN (ck SN.plan.field) dN) (kOf SN + 1))

theorem vbs_N : Spec.vbs_N := fun cm π => vp_eq SN dN cm π

def Spec.vbsP_N : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SN.plan.field) (rds SN) dN).up), VPP SN dN cm π =
    (vBS (Wb WN.K WN.T) (256 + 8 * SN.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SN.plan.field) (rds SN) dN) _root_.Fmt.oracle
        (PDS SN (ckP SN.plan.field) dN) (kOf SN + 1))

theorem vbsP_N : Spec.vbsP_N := fun cm π => vpp_eq SN dN cm π

theorem work_N : (rds SN).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.met_N : Prop := M1Door.Met _ WN

theorem met_N : Spec.met_N :=
  M1Door.metOf _ _ _ WN (M1Door.okgW _ _ _ _ WN.T (M1RunTieP.okgOf SN dN work_N) rfl)

/-! ## The full parameters -/

abbrev SM : _root_.Fmt.Spec := _root_.Fmt.M1.Theirs.specFull
abbrev dM : View → Bool := _root_.Fmt.M1.dec _root_.Fmt.M1.Theirs.sizesFull

/-- the wiring with challenges as sampled values -/
def VM : QueryLayout 256 (LtS (ck SM.plan.field) (rds SM) dM) where
  K := kOf SM + 1
  T := wqS (ck SM.plan.field) (kOf SM) (chalOf SM.plan.field (kOf SM)) (rds SM) dM
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

/-- the wiring with challenges as hash blocks -/
def WM : QueryLayout 256 (LtS (ckP SM.plan.field) (rds SM) dM) where
  K := kOf SM + 1
  T := wqS (ckP SM.plan.field) (kOf SM) (chalP SM.plan.field (kOf SM)) (rds SM) dM
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_M : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ck SM.plan.field) (rds SM) dM).up), VP SM dM cm π =
    (vBS (Wb VM.K VM.T) (256 + 8 * SM.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ck SM.plan.field) (rds SM) dM) _root_.Fmt.oracle
        (PDS SM (ck SM.plan.field) dM) (kOf SM + 1))

theorem vbs_M : Spec.vbs_M := fun cm π => vp_eq SM dM cm π

def Spec.vbsP_M : Prop :=
  ∀ (cm : Dig 256) (π : OneProtocolProof 256 (PSof (ckP SM.plan.field) (rds SM) dM).up), VPP SM dM cm π =
    (vBS (Wb WM.K WM.T) (256 + 8 * SM.plan.salt) 256 cm () π).det
      (famP (fun _ => LbS (ckP SM.plan.field) (rds SM) dM) _root_.Fmt.oracle
        (PDS SM (ckP SM.plan.field) dM) (kOf SM + 1))

theorem vbsP_M : Spec.vbsP_M := fun cm π => vpp_eq SM dM cm π

theorem work_M : (rds SM).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

def Spec.met_M : Prop := M1Door.Met _ WM

theorem met_M : Spec.met_M :=
  M1Door.metOf _ _ _ WM (M1Door.okgW _ _ _ _ WM.T (M1RunTieP.okgOf SM dM work_M) rfl)

#guard SN.params = _root_.Fmt.M1.Theirs.tiny && SM.params = _root_.Fmt.M1.Theirs.full
#guard (rds SN).length = 22 && (rds SM).length = 30 && ok SN && ok SM

end Run.M1RunTieTheirs
