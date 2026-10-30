-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Row.lean: the three chains of a file as three stages in a row
(CompileK/Joined/Row.lean, `Row`), over the rounds of OnBytes/Maker/Whole.lean's `chainsOf`.
Definitions alone; the laws are in OnBytes/Maker/RowLaws.lean.

OnBytes/Maker/Stage.lean has one chain as a reduction over its written rounds. Here each of the
three gets its silent round laid in front (`Stage.cons`): the front round, the joining round, the
seam, each with a test on what it sends. The first stage's implicit instance is the stored table
alone, so it is entered by a step without rounds that lays "no tree at hand" beside the table
(`IOR.pre`).

What the file contains.
  `WholeD.st₁`, `WholeD.st₂`, `WholeD.st₃`: the three stages' data, from the data of a whole file
    and the two lists of trees left: L₁ behind the first chain, L₂ behind the second. The trees'
    numbers over the whole file are counted as in Whole.lean.
  `noTrees`: the stored table, with no tree at hand beside it.
  `rowOf`: the row. okF, okJ, ok3: the tests on what the silent rounds send. run₁, run₂: from a
    stage's instance and its chain's view to the claims that it hands on. run₃: to the verdict.

What is not claimed. No law is stated here. That the row's verifier is `reductionOfWholeFile`'s.


-/
import OnBytes.Maker.Stage
import CompileK.Joined.Row
import Ior.Frame

set_option autoImplicit false

noncomputable section

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ _root_.Compile.Joined _root_.CompileK.Joined

/-- The first chain's data: no tree at hand. -/
def WholeD.st₁ (D : WholeD) (L₁ : List LeftT) : StageD := ⟨D.a, 0, [], D.ds₁, D.key₁, L₁⟩

/-- The second chain's. -/
def WholeD.st₂ (D : WholeD) (L₁ L₂ : List LeftT) : StageD := ⟨D.a, D.t₁, L₁, D.ds₂, D.key₂, L₂⟩

/-- The third chain's: no tree is left. -/
def WholeD.st₃ (D : WholeD) (L₂ : List LeftT) : StageD :=
  ⟨D.a, D.t₁ + D.t₂, L₂, D.ds₃, D.key₃, []⟩

/-- An implicit instance, with no tree at hand beside it. -/
def noTrees (E : ExtSpec) : ExtMap E (E.prod (EjOf [])) :=
  ExtMap.pair (ExtMap.id E) ⟨fun _ p => p.1.elim0, fun _ => ∅⟩

/-- **The three chains of a file in a row.** -/
def rowOf (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (L₁ L₂ : List LeftT) {Y X₁ X₂ : Type} (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (run₁ : Y → View → Option X₁) (run₂ : X₁ → View → Option X₂)
    (run₃ : X₂ → View → Bool) : Row (chainsOf C D tF tJ t3) Y (oneExternalString (2 ^ D.a) SgX) where
  X₁ := X₁
  E₁ := (D.st₁ L₁).Eo
  X₂ := X₂
  E₂ := (D.st₂ L₁ L₂).Eo
  S₁ := Stage.cons (plainRound TF tF) (fun p => p.elim) okF
    (Stage.ofIOR ((stageIOR C (D.st₁ L₁) run₁).pre some (noTrees _)))
  S₂ := Stage.cons (plainRound TJ tJ) (fun p => p.elim) okJ
    (Stage.ofIOR (stageIOR C (D.st₂ L₁ L₂) run₂))
  S₃ := Stage.cons (plainRound T3 t3) (fun p => p.elim) ok3
    (Stage.ofIOR (lastIOR C (D.st₃ L₂) run₃))

end OnBytes.Maker
