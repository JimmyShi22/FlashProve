-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindOpt.lean: the compiler's terms with proof of work as an option.

Definitions, statements and proofs.
CompileK/Main.lean has no proof of work, CompileK/GrindMain.lean has it. The second at
lists of zeros is not the first: the wire with tests has one block more in every answer of the
Fiat-Shamir oracle, read by nobody if no round has a test, so that the two schemes live over
different families of oracles. Here the terms of CompileK/GrindMain.lean and their analogues
without work are one family, with a parameter o : Option (Work Nn L):
  none: no work: every term is the term of CompileK/Main.lean by definition (the lemmas .._none,
    all by rfl).
  some w: the terms of CompileK/GrindMain.lean at w, by definition (.._some). "Work switched on
    with 0 bits in every round" is the case some w with lists of zeros: another scheme, with one
    idle block: declared, not hidden.

Main names:
  `D.LO o`, `D.WO o`, `D.WPO o`, `D.numsO M κ₀ n c o`, `extractorO`, `simulatorO`,
    `codingO`: interface, wires, numbers, extractor, simulator, named coding.
  `FitO lam o`, `SoundO Rno wit c o`: the two further hypotheses of the statements with work
    (`FitWk`, `BatchProtocol.SoundKG`); at none both are True (then c is idle: the bound on the
    round-by-round errors is that of `BatchProtocol.PropsK`).






Limits: what the heads of CompileK/Main.lean and CompileK/GrindMain.lean list as not said is not
said here either. One limit of the second does not hold here: this file has "no work" as a case of
its own.
That the case
none is the terms of CompileK/Main.lean is true by construction and says nothing on work; what work
costs and buys is in the case some. This file does not say that the three bounds at lists of zeros
equal those of the wire without tests: CompileK/GrindCost.lean.

Terms: lean/GLOSSARY.md.
-/
import CompileK.GrindMain
import CompileK.Main
import CompileK.Glue
import CompileK.GenWitProofs
import CompileK.KnowPull
import CompileK.KnowLocal
import CompileK.KnowBinding
import CompileK.KnowBindingUp
import Top.Extraction
import ZKCP.ExtractionMaps
import Hiop.GrindK
import CompileK.GrindPullK
import Compile.Batch.FitGrind
import Iop.GrindRecut

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type} {L₀ : BatchProtocol I X} {lam : ℕ} {Nn : Type} [Inhabited Nn] (D : DataK L₀ lam)

/-- the interface that is compiled -/
def DataK.LO : Option (Work Nn L₀) → BatchProtocol I X
  | none => D.L
  | some w => D.LWk w

/-- its wires -/
def DataK.WO : (o : Option (Work Nn L₀)) → QueryLayout lam (D.LO o)
  | none => D.W
  | some w => D.WWk w

def DataK.WPO : (o : Option (Work Nn L₀)) → WireBP (D.LO o)
  | none => D.WP
  | some w => D.WPWk w

/-- the numbers after the blocks -/
def DataK.numsO (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) : Option (Work Nn L₀) → LH.Nums
  | none => D.nums M κ₀ n
  | some _ => D.numsWk M κ₀ n c

/-- The extractor. -/
def extractorO {Wn : Type} (wit : X → Orcs L₀.onlineBatch.loc.shape → Wn) (w0 : Wn) :
    (o : Option (Work Nn L₀)) →
    Gen.Extractor (spec lam (D.WO o).K (D.LO o)) I X Wn (IVKK lam (D.LO o)) (PrfK lam (D.LO o))
  | none => extractorK D wit w0
  | some w => extractorWk D w wit w0

/-- The simulator. -/
def simulatorO (Sm : Sims L₀) :
    (o : Option (Work Nn L₀)) →
    Gen.Simulator (spec lam (D.WO o).K (D.LO o)) Unit (IVKK lam (D.LO o)) X (PrfK lam (D.LO o))
  | none => simulatorK D Sm
  | some w => simulatorWk D w Sm

/-- A named coding. -/
def codingO (Se : SerLHB L₀) (sW : Ser Nn) :
    (o : Option (Work Nn L₀)) → OracleCoding (spec lam (D.WO o).K (D.LO o)) lam
  | none => codingK D Se
  | some w => codingWk D w Se sW

/-- at some w: the conditions on the work (`FitWk`); at none: True -/
def FitO (lam : ℕ) : Option (Work Nn L₀) → Prop
  | none => True
  | some w => FitWk lam w

/-- at some w: every round has error at most c, counting its work (`BatchProtocol.SoundKG`); at none: True -/
def SoundO {Wn : Type} (Rno : I → X → Wn → Prop) (wit : X → Orcs L₀.onlineBatch.loc.shape → Wn) (c : ℝ≥0∞) :
    Option (Work Nn L₀) → Prop
  | none => True
  | some w => L₀.SoundKG Rno wit w.gT w.gL w.gB c

/-! ## The terms at none and at some w, by definition

At none they are those of CompileK/Main.lean, at some w those of CompileK/GrindMain.lean. -/

theorem DataK.LO_none : D.LO (none : Option (Work Nn L₀)) = D.L := rfl
theorem DataK.WO_none : D.WO (none : Option (Work Nn L₀)) = D.W := rfl
theorem DataK.WPO_none : D.WPO (none : Option (Work Nn L₀)) = D.WP := rfl
omit [Inhabited Nn] in
theorem DataK.numsO_none (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) :
    D.numsO M κ₀ n c (none : Option (Work Nn L₀)) = D.nums M κ₀ n := rfl
theorem extractorO_none {Wn : Type} (wit : X → Orcs L₀.onlineBatch.loc.shape → Wn) (w0 : Wn) :
    extractorO D wit w0 (none : Option (Work Nn L₀)) = extractorK D wit w0 := rfl
theorem simulatorO_none (Sm : Sims L₀) :
    simulatorO D Sm (none : Option (Work Nn L₀)) = simulatorK D Sm := rfl
theorem codingO_none (Se : SerLHB L₀) (sW : Ser Nn) :
    codingO D Se sW (none : Option (Work Nn L₀)) = codingK D Se := rfl

theorem DataK.LO_some (w : Work Nn L₀) : D.LO (some w) = D.LWk w := rfl
theorem DataK.WO_some (w : Work Nn L₀) : D.WO (some w) = D.WWk w := rfl
theorem DataK.WPO_some (w : Work Nn L₀) : D.WPO (some w) = D.WPWk w := rfl
omit [Inhabited Nn] in
theorem DataK.numsO_some (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) (w : Work Nn L₀) :
    D.numsO M κ₀ n c (some w) = D.numsWk M κ₀ n c := rfl
theorem extractorO_some {Wn : Type} (wit : X → Orcs L₀.onlineBatch.loc.shape → Wn)
    (w0 : Wn) (w : Work Nn L₀) :
    extractorO D wit w0 (some w) = extractorWk D w wit w0 := rfl
theorem simulatorO_some (Sm : Sims L₀) (w : Work Nn L₀) :
    simulatorO D Sm (some w) = simulatorWk D w Sm := rfl
theorem codingO_some (Se : SerLHB L₀) (sW : Ser Nn) (w : Work Nn L₀) :
    codingO D Se sW (some w) = codingWk D w Se sW := rfl

end Compile.Batch
