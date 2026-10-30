-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunRows.lean: an input of `runBy` (`RunIn`, Run.lean) on words:
the first stage's rows brought to the sizes that the stage states, and the column of a tree that the
first round of positions opens, computed from these rows. Definitions only. It imports Run.lean
alone; no Mathlib. `RunIn.ofRun` (RunJob.lean) calls `normFirst`. It does not call `symBy` or
`treeBy`: these are the originals that FastCol.lean and ColW.lean repeat, and it builds its trees by
`treeW` (ColW.lean; `treeW_eq`, ColWLaw.lean).

  `red`, `normList`, `normRows`, `normFirst`   an element reduced modulo the prime; a list cut or
                 padded with 0 to n entries, each reduced; the same for rows; the first stage's four
                 lists
  `Kind`, `Sel`   a row of the first stage: main, mask, or of the fresh table; its number; whether
                 its symbols are in the base field and take one word
  `symBy`        that row's symbol at a position; three words 0 for a row number out of range
  `wordsAt`      the chosen rows' symbols, one after the other, as words
  `treeBy`       a tree: its depth and column function, from the list of rows that it holds

Each has a theorem that it agrees with a definition over the field (RunJobLaw.lean): `normFirst`
gives the tabulated decoding of the same lists (`first_read`, no hypothesis); `symBy` and `treeBy`
agree with `symOf` and `treeOf` (RunJob.lean), which call `mainSym`, `maskSym` and `freshSym`
(Johnson/Prover/Link/SwitchCols.lean), where h ≤ k and `Tab` holds (`symBy_eq`, `treeBy_eq`).

Limits.
- `normFirst` pads short lists with 0 without a warning. Two of the four lists are tails, which hold
  random values: a tail given too short, or a row not given, gets 0 where a random value is due, and
  its symbols go out unmasked. After `normFirst` the sizes are always right, so the warning of
  `runBy` on sizes cannot appear. To check the lists as given, call `firstSized` (RunBy.lean) on
  them, or `RunJob.rowsFit` (RunJob.lean).
- Which rows a tree holds, in which order, and its depth are the caller's statement. Nothing
  compares them with what a sender has sent.
- A row marked as of the base field is written as its symbol's first word, whatever the other two
  hold.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage symE cp fitL)
open Fmt.M1.Own (PSt words)

/-! ## 1 The rows -/

/-- x with each word reduced modulo the prime. -/
def red (x : E) : E := Fld.two.addE x Fld.zeroE

/-- A list cut, or padded with 0, to n entries, each reduced. -/
def normList (n : Nat) (l : List E) : List E := (fitL Fld.zeroE n l).map red

/-- nr rows of n entries. -/
def normRows (nr n : Nat) (rows : List (List E)) : List (List E) :=
  (fitL [] nr rows).map (normList n)

/-- **The first stage's rows and tails, brought to the sizes that the stage states.** A short list
is padded with 0, also where it is a tail. The two fields for the fresh table are left empty:
`runBy` does not read them. -/
def normFirst (s : Stage) (p : PSt) : PSt :=
  { M := normRows (2 ^ s.k) s.C.l p.M, Rh := normRows (2 ^ s.k) s.C.r p.Rh
    W := normRows (2 ^ s.h) s.Z.l p.W, Sg := normRows (2 ^ s.h) s.Z.r p.Sg, P := [], Pi := [] }

/-! ## 2 The trees -/

/-- The three sorts of rows of a first stage. -/
inductive Kind where
  | main
  | mask
  | fresh
  deriving DecidableEq, Repr

/-- **A row of the first stage.** base: its symbols are written as one word. -/
structure Sel where
  kind : Kind
  row : Nat
  base : Bool := false
  deriving DecidableEq, Repr

/-- The row's symbol at a position. -/
def symBy (s : Stage) (p : PSt) (x : Nat) (r : Sel) : E :=
  match r.kind with
  | .main =>
    if r.row < 2 ^ s.k then symE s.C x (p.M.getD r.row []) (p.Rh.getD r.row []) else Fld.zeroE
  | .mask =>
    if r.row < 2 ^ s.h then symE s.Z (cp s.Z x) (p.W.getD r.row []) (p.Sg.getD r.row [])
    else Fld.zeroE
  | .fresh =>
    if r.row < 2 ^ s.h then symE s.Z (cp s.Z x) (p.P.getD r.row []) (p.Pi.getD r.row [])
    else Fld.zeroE

/-- The chosen rows' symbols, one after the other, as words. -/
def wordsAt (sym : Sel → E) (rows : List Sel) : List UInt64 :=
  rows.flatMap fun r => if r.base then [(sym r).1] else words (sym r)

/-- **A tree, built from T**: its depth, and the rows that it holds in the order in which a column
lists them. -/
def treeBy (s : Stage) (T : Nat × List Sel) (p : PSt) : Tree :=
  (T.1, fun x => wordsAt (symBy s p x) T.2)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.red
#print axioms ProofFile.Honest.K12.Light.normList
#print axioms ProofFile.Honest.K12.Light.normRows
#print axioms ProofFile.Honest.K12.Light.normFirst
#print axioms ProofFile.Honest.K12.Light.Kind
#print axioms ProofFile.Honest.K12.Light.Sel
#print axioms ProofFile.Honest.K12.Light.symBy
#print axioms ProofFile.Honest.K12.Light.wordsAt
#print axioms ProofFile.Honest.K12.Light.treeBy
