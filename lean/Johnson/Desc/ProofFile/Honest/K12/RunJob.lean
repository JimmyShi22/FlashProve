-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunJob.lean: `RunJob`, what a caller supplies for a proximity test
(`KindName.K12`) on words: the first stage's rows and tails as lists of words, and for each tree
that the first round of positions opens the list of rows that it holds. From that one value two
things are built: the input of `runBy` (`RunIn.ofRun`) and a `TestJob` for the reference definition
`testAll` (`RunJob.toTest`, Test.lean), so the two cannot differ in their data. `runJob_eq`
(RunJobLaw.lean) proves that `runBy` at the first gives what `testAll` gives at the second.
Definitions only. It imports Mathlib through Test.lean.

  `readPS`       lists of words decoded into the field, as a state over the field (`PS`,
                 Johnson/Prover/Link/BodyState.lean)
  `symOf`, `treeOf`   a chosen row's symbol, and a tree, computed over the field by `mainSym`,
                 `maskSym`, `freshSym` (Johnson/Prover/Link/SwitchCols.lean)
  `RunJob`, `RunJob.s₀`   what a caller supplies; its first stage
  `RunJob.rowsFit`   a check: the rows as given have the sizes that the first stage states
  `RunJob.toTest`   the `TestJob` with the same data
  `RunIn.ofRun`   the input of `runBy`; rows and trees are computed on words: the rows by
                 `normFirst` (RunRows.lean), the trees by `treeW` (ColW.lean), whatever `Seams` the
                 run is given

Limits.
- The rows may be any lists: both sides cut them, pad them with 0 and reduce them, tails too (see
  RunRows.lean's limits). `RunJob.rowsFit` is false where a list is cut or padded (not where words
  are only reduced). No definition asks it.
- No theorem relates `treeOf` to the library's column of a stage on words (`stageColW`,
  Johnson/Prover/Link/SwitchCols.lean).
- No `RunJob` here is built from a stored proof file.
- Only the rows and the first trees are computed on words. The state on entry to the test is the
  caller's function; the random values arrive as field elements (`TestCoins`, `Stretch`) and go
  through `sortedOf` (RunOf.lean).
- A tree that holds a row which is none of main, mask or fresh (a kept member's) cannot be expressed
  in `Sel`.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunOf
import Johnson.Desc.ProofFile.Honest.K12.RunRows
import Johnson.Desc.ProofFile.Honest.K12.ColW
import Johnson.Desc.ProofFile.Honest.K12.RunBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE lst)
open Johnson.Prover.Link (PS mainSym maskSym freshSym)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.Pub (sgOf)

variable {W X : Type}

/-- **Lists of words, decoded into the field.** Beyond a list's end it gives 0. The four fields of
the fresh table and of the last stage are 0. -/
def readPS (s : Stage) (p : PSt) : PS :=
  { tabM := fun i => lst (p.M.getD (i % 2 ^ s.k) []) (i / 2 ^ s.k)
    tabZ := fun i => lst (p.W.getD (i % 2 ^ s.h) []) (i / 2 ^ s.h)
    tM := fun b q => lst (p.Rh.getD b []) q, tZ := fun b q => lst (p.Sg.getD b []) q
    fM := fun _ _ => 0, fT := fun _ _ => 0, sM := fun _ => 0, sT := fun _ => 0 }

/-- A chosen row's symbol at a position, computed over the field and encoded. -/
def symOf (s : Stage) (P : PS) (x : ℕ) (r : Sel) : Fmt.M1.E :=
  match r.kind with
  | .main =>
    if r.row < 2 ^ s.k then ofE (mainSym (sgOf s) P.tabM P.tM x r.row) else Fmt.Fld.zeroE
  | .mask =>
    if r.row < 2 ^ s.h then ofE (maskSym (sgOf s) P.tabZ P.tZ x r.row) else Fmt.Fld.zeroE
  | .fresh =>
    if r.row < 2 ^ s.h then ofE (freshSym (sgOf s) P.fM P.fT x r.row) else Fmt.Fld.zeroE

/-- A tree, from the list of rows that it holds, computed over the field. -/
def treeOf (s : Stage) (T : ℕ × List Sel) (P : PS) : Tree :=
  (T.1, fun x => wordsAt (symOf s P x) T.2)

/-- **What a caller supplies, on words.** W: the prover's input. X: what the parts hand on. -/
structure RunJob (W X : Type) where
  /-- the test's parameters -/
  p : P12
  /-- the group's oracle messages, as in `TestJob` -/
  members : List (Addr × ℕ × Due)
  /-- who sent the first fold's fresh table, as in `TestJob` -/
  fresh : Option (Addr × ℕ)
  /-- the state on entry to the test, of the type of the verifier's state; the caller's function -/
  rec₀ : W → Front X → T12
  /-- the first stage's main rows, their tails, its mask rows, their tails, computed from the input,
  what precedes the test, and the members' random values by the member's number. The two fields for
  the fresh table are not read -/
  rows : W → Front X → (ℕ → Stretch) → PSt
  /-- the trees that the first round of positions opens, in the order of the declared openings: each
  tree's depth, and the rows that it holds in its column's order -/
  trees : List (ℕ × List Sel)

/-- The first stage; a stage of zeros where there is none. -/
def RunJob.s₀ (R : RunJob W X) : Stage := R.p.nums.stages.headD default

/-- The rows as the caller gives them have the sizes that the first stage states (`firstSized`,
RunBy.lean). Where it is false, both `RunIn.ofRun` and `RunJob.toTest` cut or pad them with 0, tails
too, without a warning. -/
def RunJob.rowsFit (R : RunJob W X) (w : W) (fr : Front X) (mem : ℕ → Stretch) : Bool :=
  firstSized R.s₀ (R.rows w fr mem)

/-- **The `TestJob` with the same data.** -/
def RunJob.toTest (R : RunJob W X) : TestJob W X :=
  { p := R.p, members := R.members, fresh := R.fresh, rec₀ := R.rec₀
    rows₀ := fun w fr mem => readPS R.s₀ (R.rows w fr mem)
    trees₀ := fun _ _ _ P => R.trees.map fun T => treeOf R.s₀ T P }

/-- **The input of `runBy`**, with rows and trees computed on words. It takes no `Seams`: the trees
are `treeW`'s (ColW.lean) at `Seams.lib` too. `treeW` equals `treeBy` (RunRows.lean) by the theorem
`treeW_eq` (ColWLaw.lean), for all arguments. -/
def RunIn.ofRun (R : RunJob W X) (w : W) (fr : Front X) (C : TestCoins) : RunIn :=
  { p := R.p, own := R.fresh.isNone, door := R.rec₀ w fr
    first := normFirst R.s₀ (R.rows w fr C.mem)
    trees := fun p₀ => R.trees.map fun T => treeW R.s₀ T p₀
    coin := sortedOf R.p.nums.stages C }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.readPS
#print axioms ProofFile.Honest.K12.Light.symOf
#print axioms ProofFile.Honest.K12.Light.treeOf
#print axioms ProofFile.Honest.K12.Light.RunJob
#print axioms ProofFile.Honest.K12.Light.RunJob.s₀
#print axioms ProofFile.Honest.K12.Light.RunJob.rowsFit
#print axioms ProofFile.Honest.K12.Light.RunJob.toTest
#print axioms ProofFile.Honest.K12.Light.RunIn.ofRun
