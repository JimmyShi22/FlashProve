-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WNarrowAtW.lean: one closed shape for the last chain's own test:
its one group, its three members, the mask, their three trees.

  narrowW          the shape
  frontFive_narrowW   the test frontFiveB says yes there, at the written parameters
  frontFive_wrongMask, frontFive_wrongNumber, frontFive_oneRow, frontFive_openedTree   four controls

Its numbers were read off one run of the full-size example. No theorem here ties them to a run: that
is asked, field by field, of the relation SameCore (WNarrow.lean) at A = [4, 197, 198, 199]. piWFull is
not the seated place's own term: the library carries the test along Alike. A message or tree called
blank is one that frontFive_same shows the test does not read.

Limits.
- A closed fact at the written parameters.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrow
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes
open VerifiableInference.Desc.Ground.Sh
open H2K.Member (piWFull codesFull)

/-- A message that no test reads. -/
def blankMsg : OrcSh := ⟨{}, false, 0, [], [], none, false⟩

/-- A tree that no test reads. -/
def blankTree : TreeSh := ⟨{}, 0, .given, [], false, 0⟩

/-- The index masks' message. -/
def indexMsg : OrcSh :=
  { shape := { code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 12,
               answers := 1 }
    sampled := true, rows := 1, pad := [(Part.mask, 255)], groups := [0], ledger := none,
    spent := false }

/-- W's message. -/
def wMsg : OrcSh :=
  { shape := { code := 11, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 12, answers := 1 }
    sampled := true, rows := 1, pad := [(Part.mask, 255)], groups := [0], ledger := none,
    spent := false }

/-- The mask's message. -/
def maskMsg : OrcSh :=
  { shape := { code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 2, maskCode := 12,
               answers := 0 }
    sampled := false, rows := 0, pad := [], groups := [], ledger := none, spent := false }

/-- Omega's message. -/
def omegaMsg : OrcSh :=
  { shape := { code := 11, mainRows := 12, mainDeg := 3, maskRows := 0, maskCode := 4294967295,
               answers := 1 }
    sampled := true, rows := 1, pad := [(Part.main, 4194299)], groups := [0], ledger := none,
    spent := false }

def indexTree : TreeSh :=
  { shape := { logN := 13, logNzk := 13, mainSymbols := #[0], maskSymbols := #[3] }, number := 1,
    src := .given, parts := [4], oneList := false, lists := 0 }

def wTree : TreeSh :=
  { shape := { logN := 22, logNzk := 13, mainSymbols := #[3, 0], maskSymbols := #[3, 6] },
    number := 82, src := .given, parts := [197, 198], oneList := true, lists := 0 }

def omegaTree : TreeSh :=
  { shape := { logN := 22, logNzk := 0, mainSymbols := #[36], maskSymbols := #[0] }, number := 1,
    src := .given, parts := [199], oneList := false, lists := 0 }

/-- The own group. -/
def ownGroup : GrpSh :=
  { code := 11, maskCode := 12, members := [4, 197, 199], kept := [false, false, false],
    kinds := [RowKind.plain, RowKind.plain], inRun := false }

/-- **The closed shape.** -/
def narrowW : CoreSh :=
  { st := { codes := codesFull
            oracles := List.replicate 4 blankMsg ++ [indexMsg] ++ List.replicate 192 blankMsg ++
              [wMsg, maskMsg, omegaMsg]
            groups := [ownGroup] }
    book := { trees := [blankTree, indexTree] ++ List.replicate 80 blankTree ++ [wTree, omegaTree]
              place := List.replicate 4 (0, 0) ++ [(1, 0)] ++ List.replicate 192 (0, 0) ++
                [(82, 0), (82, 1), (83, 0)] }
    roots := 0 }

/-- **The test says yes at the closed shape.** -/
theorem frontFive_narrowW :
    frontFiveB piWFull codesFull ⟨narrowW, 0, .nothing, some 198⟩ = true := by
  decide +kernel

/-- Control: not at the wrong mask. -/
theorem frontFive_wrongMask :
    frontFiveB piWFull codesFull ⟨narrowW, 0, .nothing, some 197⟩ = false := by
  decide +kernel

/-- Control: not where W's tree has the wrong number. -/
theorem frontFive_wrongNumber :
    frontFiveB piWFull codesFull ⟨{ narrowW with book := { narrowW.book with
      trees := [blankTree, indexTree] ++ List.replicate 80 blankTree ++
        [{ wTree with number := 81 }, omegaTree] } }, 0, .nothing, some 198⟩ = false := by
  decide +kernel

/-- Control: not with one row on the group. -/
theorem frontFive_oneRow :
    frontFiveB piWFull codesFull ⟨{ narrowW with st := { narrowW.st with
      groups := [{ ownGroup with kinds := [RowKind.plain] }] } }, 0, .nothing, some 198⟩ = false := by
  decide +kernel

/-- Control: not where the index masks' tree is opened at one list only and has been opened. -/
theorem frontFive_openedTree :
    frontFiveB piWFull codesFull ⟨{ narrowW with book := { narrowW.book with
      trees := [blankTree, { indexTree with oneList := true, lists := 1 }] ++
        List.replicate 80 blankTree ++ [wTree, omegaTree] } }, 0, .nothing, some 198⟩ = false := by
  decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.frontFive_narrowW
#print axioms ProofFile.Honest.K12.AtFile.frontFive_wrongMask
#print axioms ProofFile.Honest.K12.AtFile.frontFive_wrongNumber
#print axioms ProofFile.Honest.K12.AtFile.frontFive_oneRow
#print axioms ProofFile.Honest.K12.AtFile.frontFive_openedTree
