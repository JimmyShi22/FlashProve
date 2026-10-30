-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyThin.lean: a small toy of this library's own (`Run.Toy1`, Run/ToyQ.lean; on bytes: Fmt.Toy1):
the typed oracle functions that the encoding of the queries reads out of the single oracle, in the
form made for the evaluator, with their tie.

Definitions that compute, theorems, tests.
Why: Run/ToyCode.lean has the encoding of the queries at the toy (`pageT`, `mT`). Tried, with a
trace in a round's instance: evaluating it builds the list of all verifier messages (at this toy
4,096: harmless; at a round that draws a field element: hopeless). Here the same data once more,
every piece made without the interface as a value.

Main names:
  `symT`, `pbT`, `serPT`: serialisers of a symbol with its position and of a plain part, for the
    three protocols, written out at the toy's types (no recursion on a shape).
  `firstTP`: the first chain query's partial code in the form written for the evaluator (`pFirstP`,
    Run/CodingThin.lean).
  `pageTP : PageC Lt 2`: it is another encoding than `mT`: the points that the format writes have
    the same strings; the points behind the byte 2 have other strings there.
  `gT : Fam (spec 256 2 Lt) := famC LfT pageTP oBy`: the typed oracle functions.
  `gT_eq`: the tie: `gT` = `readBlocks (theImpl pageTP) oBits`: the typed oracle functions of the
    first exit to a single oracle (all blocks asked), at an encoding with its inverse and both laws.
  `toy_fitP`: `PageFit pageTP PD` (Run/CodingAgree.lean): what its partial codes write are the
    strings of the functions of Run/CodingFn.lean.

Tests (#guard). At a node, a leaf, the first query (the block of the chain value), rounds 1 and 2:
the strings are `mT`'s (Run/ToyCodeGuards.lean holds `mT`'s strings at the same queries, at another
configuration's digest, against the format's spelling). At a node, a leaf, round 1, and the chain
value of the first query: the answers are those that `mT` reads out. Round 0's two message blocks:
behind the byte 2.

Limits: what was tried outside this file (a copy of the tree with a trace in round 1's instance):
`gT` at a node, a leaf, round 1, round 0 with its two message blocks: the list is not built. A fact
about this compiler, no theorem.
This file says nothing on a run of the verifier at `gT`: the evaluable form of the compiled verifier
(Run/ThinDefs.lean) wants the protocol as a skeleton, which this toy, written out directly, does not
have.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyFit
import Run.CodingThin
import Run.SerThin
import Run.ToyCodeGuards

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch

/-- The interface behind a function of Unit. -/
def LfT : Unit → BatchProtocol Unit E3 := fun _ => Lt

def symEq : SymAny (shapeOf Lt .test) ≃ Fin 16 × E3 where
  toFun := fun y => match y with
    | ⟨.inr (.inl x), e⟩ => (x, e)
    | ⟨.inl p, _⟩ => p.elim
    | ⟨.inr (.inr (.inl p)), _⟩ => p.elim
    | ⟨.inr (.inr (.inr p)), _⟩ => p.elim
  invFun := mkL
  left_inv := fun y => by
    obtain ⟨p, e⟩ := y
    rcases p with p | (x | (p | p))
    · exact p.elim
    · rfl
    · exact p.elim
    · exact p.elim
  right_inv := fun _ => rfl

/-- A symbol with its position. -/
def symT : ∀ t : Tag, Ser (SymAny (shapeOf (LfT ()) t))
  | .test => Ser.ofEquiv symEq (Ser.prod (Ser.fin 16) serE3)
  | .link => serNoPos _
  | .onl => serNoPos _

/-- A plain part of some round. -/
def pbT : ∀ t : Tag, Ser (PlainPart (shapeOf (LfT ()) t) (annOf (LfT ()) t))
  | .test =>
    Ser.sum (Ser.sum Ser.unit Ser.unit)
      (Ser.sum (Ser.sum Ser.unit (Ser.prod Ser.unit Ser.nat))
        (Ser.sum (Ser.sum Ser.unit serE3) Ser.empty))
  | .link => Ser.empty
  | .onl => Ser.empty

def serPT : SerP LfT := ⟨serE3, Ser.unit, symT, pbT⟩

def backTP : StrCode (AllPts 256 2 Lt) := backP LfT serPT 2

def firstTP : PCode (FbIn 256 Lt .test) :=
  pFirstP LfT p0T isP0T isP0T_iff 7 stmT unstmT unstm_stm stm_unstm

/-- The data, every piece made without the interface as a value. -/
def pageTP : PageC Lt 2 where
  cfg := cfgT
  hcfg := cfgT_size
  chain := chainT
  chainTag := chainT_tag
  first := firstTP
  firstTag := firstT_tag
  firstHd := firstT_hd
  saltBits := 320
  leafP := leafPT
  leafTag := leafPT_tag
  back := backTP

/-- The typed oracle functions read out of the single oracle, in the form made for the evaluator. -/
def gT : Fam (spec 256 2 Lt) := famC LfT pageTP oBy

theorem gT_eq : gT = readBlocks (theImpl pageTP) oBits := famC_oBits pageTP

theorem toy_fitP : PageFit pageTP PD :=
  PageFit.of pageTP PD (by decide) chainT_fit rfl 40 rfl leafPT_fit firstT_fit

end Run.Toy1

namespace Run.Toy1.G
open Iop Rom Compile Compile.Batch

def cP (o : Batch.OracleName) (q : Batch.domOf 256 Lt o) (j : Fin (blk 2 o)) : List Bool :=
  codeP LfT pageTP o q j
def mC : OracleCoding (spec 256 2 Lt) 256 := mOne
def hxd (d : Dig 256) : String := _root_.Fmt.hex (digToBytes d)

-- the strings are mT's at the configuration's digest
#guard cP .node (bts dl, bts dr) (0 : Fin 1) == mC.code .node (bts dl, bts dr) (0 : Fin 1)
#guard cP .leaf lq (0 : Fin 1) == mC.code .leaf lq (0 : Fin 1)
#guard cP (.fb .test) q0 (2 : Fin 3) == mC.code (.fb .test) q0 (2 : Fin 3)
#guard (List.finRange 3).all fun j => cP (.fb .test) q1 j == mC.code (.fb .test) q1 j
#guard (List.finRange 3).all fun j => cP (.fb .test) q2 j == mC.code (.fb .test) q2 j
-- round 0's message blocks: behind the byte 2
#guard (cP (.fb .test) q0 (0 : Fin 3)).take 8 == bitsOfByte 2 && (cP (.fb .test) q0 (1 : Fin 3)).take 8 == bitsOfByte 2
-- the answers are those that mT reads out
#guard hxd (gT .node (bts dl, bts dr)) == hxd (readBlocks mC oBits .node (bts dl, bts dr))
#guard hxd (gT .leaf lq) == hxd (readBlocks mC oBits .leaf lq)
#guard (let a : (Fin 2 → Dig 256) × Dig 256 := gT (.fb .test) q1; let b : (Fin 2 → Dig 256) × Dig 256 := readBlocks mC oBits (.fb .test) q1; hxd a.2 == hxd b.2 && hxd (a.1 0) == hxd (b.1 0) && hxd (a.1 1) == hxd (b.1 1))
#guard (let a : (Fin 2 → Dig 256) × Dig 256 := gT (.fb .test) q0; let b : (Fin 2 → Dig 256) × Dig 256 := readBlocks mC oBits (.fb .test) q0; hxd a.2 == hxd b.2)

end Run.Toy1.G
