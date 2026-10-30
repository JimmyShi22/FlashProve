-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M2Tie.lean: the second toy (a chain of three links) in the generic construction: at its two
descriptions, what is evaluated behind the reader is the run of the library's `Compile.Batch.vBS`;
and, with challenges as hash blocks, the wiring meets the library's conditions on a wiring. (Behind
the reader: the reader first, then the verifier on what it hands out.) Definitions, eleven
statements with their proofs, two tests. Many statements of this library are written twice: a
definition in the namespace `Spec` states a proposition, and a theorem of the same name outside that
namespace proves it (lean/GLOSSARY.md).

The programs (the C++ implementation that comes with this Lean code) write proof files for this toy
at tiny parameters (58 rounds) and at full parameters (76 rounds). The generic construction
(Run/PlanQ*.lean) makes, from a description, the typed protocol, its wiring (the data that say how
deep the Merkle trees are, where a position stands among a tree's leaves, and how hash output
becomes challenges) and the run functions. This file states at these two descriptions what
Run/M1RunTie.lean, Run/M1RunTieP.lean, Run/M1RunTiePF.lean and Run/M1Door.lean state for the first
toy, except for `Met` at the wiring with whole paths (`metF_T`, `metF_R`, `metF_F`,
Run/M1Door.lean): see part 3. Every statement but `names` is for every decision, every digest of the
public files and every further items of the parameters, so nothing here moves when the parameters'
bytes or the decision's text do.

Sources. The statements follow those of the four files named above; the proofs are applications of
their generic parts and of `vp_eq`, `vpp_eq`, `vpfp_eq`. The descriptions are Fmt/M2Plan.lean's
(specOf at tinyPar, toyPar).

The two interfaces. An interface (`BatchProtocol`, Iop/Batch.lean) is the library's record of three protocols,
called Test, Link and Batch, with an encoding and a decoding of an index. The equations below are
stated at one interface, the wirings V*, W*, U* at another: the toy's protocol is the Batch of the
first and the Test of the second. The run functions stand at the interface `LbS`, whose Batch is the
toy's protocol (Run/PlanQS.lean; the tag "onl"; `Compile.Batch.vBS`). The equations below are about
`vBS`. The wirings V*, W*, U* and the laws of W*, U* are stated at the interface `LtS`, whose Test
is the same protocol. The field T of these wirings is the field B of the run functions' wiring
(Run/PlanQS.lean: `Wb`).

1. What the file contains.
     `ST`, `SF cfg others`: The two descriptions.
     `VT`, `VF`: The wiring with challenges as sampled values (a round's verifier message is the
       values that the format draws, field elements and positions among them; "ck" in the code).
     `WT`, `WF`: The wiring with challenges as hash blocks (a round's verifier message is its
       256-bit blocks; reads and decision apply the sampling rule; "ckP" in the code).
     `UT`, `UF`: The same with whole paths (each opened leaf has an authentication path of its own)
       in the place of pruned openings (the opened leaves of a tree share one set of sibling
       digests, as in the files).

2. What is checked when the file compiles. Two tests (#guard): the descriptions have 58 and 76
rounds and lie within the limits of the generic construction (`PQ.ok`) and of the encoding of the
queries into a single oracle (`OKQ`), at a made-up digest of the public files.

3. Theorems.
     `vbs_T`, `vbs_F`: `VP S dec cm π = (vBS (Wb V.K V.T) ..).det (famP ..)`: challenges as sampled
       values: the verifier inside `runStrictS`, `runLaxS`.
     `vbsP_T`, `vbsP_F`: `VPP S dec cm π = (vBS (Wb W.K W.T) ..).det (famP ..)`: challenges as hash
       blocks: `runStrictSP`, `runLaxSP`.
     `met_T`, `met_F`: `Run.M1Door.Met _ W`: the twelve conditions of Run/M1Door.lean's record: the
       laws of the whole wiring; wired, reads, local, coherent, read symbol by symbol; and the
       fields "sound" and "low", which are true and empty, as that file's head says.
     `vbsPF_T`, `vbsPF_F`: `VPFP S dec cm π = (vBS (Wb U.K U.T) ..).det (famP ..)`: hash blocks and
       whole paths: the verifier inside `runFullSP`. (`run1WPF` is the like run function over a
       single oracle; no equation here is on it.)
     `okgPF_T`, `okgPF_F`: `U.T.OKG`: that wiring obeys the library's laws of a wiring. (The whole
       record `Met` is not stated at U. At W it comes by two theorems of Run/M1Door.lean, both at
       `LtS`: `okgW`, from `T.OKG` and `T.ext = we0` to the `OKG` of the wiring with that `T` and
       W's `Lk`, `B`, `depth`, `depthReq`; and `metOf`, from that `OKG` to `Met`. There is no
       equation here for sampled values with whole paths: `runFullS`.)
     `names`: `ST`, `SF` at the programs' digest of the public files and items are
       `Fmt.M2.Theirs.specTiny`, `specFull` (by `rfl`): the names at which the test files
       Run/M2EngineT1.lean to Run/M2EngineF12.lean run.

4. What is not claimed. No statement on soundness follows. All that the heads of Run/PlanQS.lean,
Run/M1RunTieP.lean, Run/M1Door.lean do not claim is not claimed here: `vBS` is one of the functions
that a scheme's verifier runs, not that verifier; with an encoded index of length 0, what a theorem
says about the language of an accepted string is empty. No soundness statement is made in Run/ or
Fmt/ for the toy's protocol. The library has building blocks of such protocols with such statements,
each under its own hypotheses (`psc_know`, Cb/Ld/LdPsc.lean; `ld_sum_know`, Cb/Ld/LdSumKnow.lean;
`ldSwitch_know`, Cb/Ld/LdSwitch.lean; `ldBase_know`, Cb/Ld/LdBaseProofs.lean); nothing in Run/ or
Fmt/ connects the two. The fields "sound" and "low" of `met_T`, `met_F` (part 3), and the same
conditions in their generic forms (`lts_sound`, `metOf`, Run/M1Door.lean; `lb_sound`, `metB`,
Run/BatchDoor.lean; `metOf` and `metB` under their hypotheses on the wiring), are true and empty.
Nothing is run here: no file, no decision. That the descriptions are the programs' is tested, not
proved: the tests of Fmt/M2Plan.lean hold its tables against the programs' description of the toy;
those of Fmt/M2Theirs.lean hold the parameters' bytes of `Theirs.specTiny`, `specFull` against the
programs' archive. A test (#guard) is an evaluation made while the file compiles; the compile fails
if the result moves; it leaves no theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.M1Door
import Run.M1RunTiePF
import Fmt.M2Plan
import Fmt.M2Theirs
import Run.PageQ

set_option autoImplicit false
set_option maxRecDepth 4000

namespace Run.M2Tie
open Iop Rom Compile Compile.Batch Run.PQ

/-- The rounds' data have the description's entries: the test "at most 64 bits of work in every
round" gives the same value on `rdsFrom S n rs` as on `rs`, for every `n` and `rs`. -/
theorem rdsFrom_work (S : _root_.Fmt.Spec) :
    ∀ (n : ℕ) (rs : List _root_.Fmt.Round),
      (rdsFrom S n rs).all (fun d => decide (d.entry.work ≤ 64)) =
        rs.all (fun r => decide (r.entry.work ≤ 64))
  | _, [] => rfl
  | n, r :: rs => by simp only [rdsFrom, List.all_cons, rdsFrom_work S _ rs]

/-! ## Tiny parameters -/

section
variable (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool)

abbrev ST : _root_.Fmt.Spec := _root_.Fmt.M2.specOf _root_.Fmt.M2.tinyPar cfg others

/-- the wiring with challenges as sampled values (`ck`) -/
def VT : QueryLayout 256 (LtS (ck (ST cfg others).plan.field) (rds (ST cfg others)) dec) where
  K := kOf (ST cfg others) + 1
  T := wqS (ck (ST cfg others).plan.field) (kOf (ST cfg others))
    (chalOf (ST cfg others).plan.field (kOf (ST cfg others))) (rds (ST cfg others)) dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

/-- the wiring with challenges as hash blocks (`ckP`) -/
def WT : QueryLayout 256 (LtS (ckP (ST cfg others).plan.field) (rds (ST cfg others)) dec) where
  K := kOf (ST cfg others) + 1
  T := wqS (ckP (ST cfg others).plan.field) (kOf (ST cfg others))
    (chalP (ST cfg others).plan.field (kOf (ST cfg others))) (rds (ST cfg others)) dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

end

def Spec.vbs_T : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck (ST cfg others).plan.field) (rds (ST cfg others)) dec).up),
    VP (ST cfg others) dec cm π =
      (vBS (Wb (VT cfg others dec).K (VT cfg others dec).T)
          (256 + 8 * (ST cfg others).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ck (ST cfg others).plan.field) (rds (ST cfg others)) dec)
          _root_.Fmt.oracle (PDS (ST cfg others) (ck (ST cfg others).plan.field) dec)
          (kOf (ST cfg others) + 1))

theorem vbs_T : Spec.vbs_T := fun cfg others dec cm π => vp_eq (ST cfg others) dec cm π

def Spec.vbsP_T : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ckP (ST cfg others).plan.field) (rds (ST cfg others)) dec).up),
    VPP (ST cfg others) dec cm π =
      (vBS (Wb (WT cfg others dec).K (WT cfg others dec).T)
          (256 + 8 * (ST cfg others).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ckP (ST cfg others).plan.field) (rds (ST cfg others)) dec)
          _root_.Fmt.oracle (PDS (ST cfg others) (ckP (ST cfg others).plan.field) dec)
          (kOf (ST cfg others) + 1))

theorem vbsP_T : Spec.vbsP_T := fun cfg others dec cm π => vpp_eq (ST cfg others) dec cm π

theorem work_T (cfg : ByteArray) (others : List (String × ByteArray)) :
    (rds (ST cfg others)).all (fun d => decide (d.entry.work ≤ 64)) = true := by
  unfold rds
  rw [rdsFrom_work]
  show (_root_.Fmt.M2.roundsOf _root_.Fmt.M2.tinyPar).all (fun r => decide (r.entry.work ≤ 64)) =
    true
  decide +kernel

def Spec.met_T : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool),
    M1Door.Met _ (WT cfg others dec)

theorem met_T : Spec.met_T := fun cfg others dec =>
  M1Door.metOf _ _ _ (WT cfg others dec)
    (M1Door.okgW _ _ _ _ (WT cfg others dec).T
      (M1RunTieP.okgOf (ST cfg others) dec (work_T cfg others)) rfl)

#guard (rds (ST (_root_.Fmt.pattern 32) [])).length = 58 && ok (ST (_root_.Fmt.pattern 32) []) && OKQ (ST (_root_.Fmt.pattern 32) [])

/-! ## Full parameters -/

section
variable (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool)

abbrev SF : _root_.Fmt.Spec := _root_.Fmt.M2.specOf _root_.Fmt.M2.toyPar cfg others

/-- the wiring with challenges as sampled values (`ck`) -/
def VF : QueryLayout 256 (LtS (ck (SF cfg others).plan.field) (rds (SF cfg others)) dec) where
  K := kOf (SF cfg others) + 1
  T := wqS (ck (SF cfg others).plan.field) (kOf (SF cfg others))
    (chalOf (SF cfg others).plan.field (kOf (SF cfg others))) (rds (SF cfg others)) dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

/-- the wiring with challenges as hash blocks (`ckP`) -/
def WF : QueryLayout 256 (LtS (ckP (SF cfg others).plan.field) (rds (SF cfg others)) dec) where
  K := kOf (SF cfg others) + 1
  T := wqS (ckP (SF cfg others).plan.field) (kOf (SF cfg others))
    (chalP (SF cfg others).plan.field (kOf (SF cfg others))) (rds (SF cfg others)) dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

end

def Spec.vbs_F : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck (SF cfg others).plan.field) (rds (SF cfg others)) dec).up),
    VP (SF cfg others) dec cm π =
      (vBS (Wb (VF cfg others dec).K (VF cfg others dec).T)
          (256 + 8 * (SF cfg others).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ck (SF cfg others).plan.field) (rds (SF cfg others)) dec)
          _root_.Fmt.oracle (PDS (SF cfg others) (ck (SF cfg others).plan.field) dec)
          (kOf (SF cfg others) + 1))

theorem vbs_F : Spec.vbs_F := fun cfg others dec cm π => vp_eq (SF cfg others) dec cm π

def Spec.vbsP_F : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ckP (SF cfg others).plan.field) (rds (SF cfg others)) dec).up),
    VPP (SF cfg others) dec cm π =
      (vBS (Wb (WF cfg others dec).K (WF cfg others dec).T)
          (256 + 8 * (SF cfg others).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ckP (SF cfg others).plan.field) (rds (SF cfg others)) dec)
          _root_.Fmt.oracle (PDS (SF cfg others) (ckP (SF cfg others).plan.field) dec)
          (kOf (SF cfg others) + 1))

theorem vbsP_F : Spec.vbsP_F := fun cfg others dec cm π => vpp_eq (SF cfg others) dec cm π

theorem work_F (cfg : ByteArray) (others : List (String × ByteArray)) :
    (rds (SF cfg others)).all (fun d => decide (d.entry.work ≤ 64)) = true := by
  unfold rds
  rw [rdsFrom_work]
  show (_root_.Fmt.M2.roundsOf _root_.Fmt.M2.toyPar).all (fun r => decide (r.entry.work ≤ 64)) =
    true
  decide +kernel

def Spec.met_F : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool),
    M1Door.Met _ (WF cfg others dec)

theorem met_F : Spec.met_F := fun cfg others dec =>
  M1Door.metOf _ _ _ (WF cfg others dec)
    (M1Door.okgW _ _ _ _ (WF cfg others dec).T
      (M1RunTieP.okgOf (SF cfg others) dec (work_F cfg others)) rfl)

#guard (rds (SF (_root_.Fmt.pattern 32) [])).length = 76 && ok (SF (_root_.Fmt.pattern 32) []) && OKQ (SF (_root_.Fmt.pattern 32) [])

/-! ## The wiring without the flag for pruned sets: the run functions with whole paths -/

/-- the wiring without the flag for pruned sets, with challenges as hash blocks (`ckP`) -/
def UT (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) :
    QueryLayout 256 (LtS (ckP (ST cfg others).plan.field) (rds (ST cfg others)) dec) where
  K := kOf (ST cfg others) + 1
  T := wqSF (ckP (ST cfg others).plan.field) (kOf (ST cfg others))
    (chalP (ST cfg others).plan.field (kOf (ST cfg others))) (rds (ST cfg others)) dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsPF_T : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ckP (ST cfg others).plan.field) (rds (ST cfg others)) dec).up),
    VPFP (ST cfg others) dec cm π =
      (vBS (Wb (UT cfg others dec).K (UT cfg others dec).T)
          (256 + 8 * (ST cfg others).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ckP (ST cfg others).plan.field) (rds (ST cfg others)) dec)
          _root_.Fmt.oracle (PDS (ST cfg others) (ckP (ST cfg others).plan.field) dec)
          (kOf (ST cfg others) + 1))

theorem vbsPF_T : Spec.vbsPF_T := fun cfg others dec cm π => vpfp_eq (ST cfg others) dec cm π

def Spec.okgPF_T : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool),
    (UT cfg others dec).T.OKG

theorem okgPF_T : Spec.okgPF_T := fun cfg others dec =>
  M1RunTiePF.okgFOf (ST cfg others) dec (work_T cfg others)

/-- the wiring without the flag for pruned sets, with challenges as hash blocks (`ckP`) -/
def UF (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) :
    QueryLayout 256 (LtS (ckP (SF cfg others).plan.field) (rds (SF cfg others)) dec) where
  K := kOf (SF cfg others) + 1
  T := wqSF (ckP (SF cfg others).plan.field) (kOf (SF cfg others))
    (chalP (SF cfg others).plan.field (kOf (SF cfg others))) (rds (SF cfg others)) dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbsPF_F : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ckP (SF cfg others).plan.field) (rds (SF cfg others)) dec).up),
    VPFP (SF cfg others) dec cm π =
      (vBS (Wb (UF cfg others dec).K (UF cfg others dec).T)
          (256 + 8 * (SF cfg others).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ckP (SF cfg others).plan.field) (rds (SF cfg others)) dec)
          _root_.Fmt.oracle (PDS (SF cfg others) (ckP (SF cfg others).plan.field) dec)
          (kOf (SF cfg others) + 1))

theorem vbsPF_F : Spec.vbsPF_F := fun cfg others dec cm π => vpfp_eq (SF cfg others) dec cm π

def Spec.okgPF_F : Prop :=
  ∀ (cfg : ByteArray) (others : List (String × ByteArray)) (dec : View → Bool),
    (UF cfg others dec).T.OKG

theorem okgPF_F : Spec.okgPF_F := fun cfg others dec =>
  M1RunTiePF.okgFOf (SF cfg others) dec (work_F cfg others)

/-! ## The descriptions at which the test files run -/

/-- the descriptions at which the test files Run/M2Engine*.lean run are these descriptions, at the
programs' configuration and items -/
def Spec.names : Prop :=
  ST (_root_.Fmt.configDigest [_root_.Fmt.M2.Theirs.pubTiny])
      (_root_.Fmt.M2.itemsOf _root_.Fmt.M2.tinyPar) =
    _root_.Fmt.M2.Theirs.specTiny ∧
  SF (_root_.Fmt.configDigest [_root_.Fmt.M2.Theirs.pubFull])
      (_root_.Fmt.M2.itemsOf _root_.Fmt.M2.toyPar) =
    _root_.Fmt.M2.Theirs.specFull

theorem names : Spec.names := ⟨rfl, rfl⟩

end Run.M2Tie
