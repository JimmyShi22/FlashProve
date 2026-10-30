-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitDigits.lean: the honest side of the kind "lookup" (K3): the
array ZZ is no longer a letter: the two fillings (Honest/K3/WitFill.lean, Honest/K3/WitPlan.lean) of
the letters `Sources` (Honest/K3/Wit.lean) at the smallness test's own array of digits; and that the
digits' keys and bits are honest, conditional on two public hypotheses. Definitions with code, and
two theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: ZZ is not written in this file: it is `zzOf`
(Honest/K8/Digits.lean), a function of the smallness test's structure, a list that says where each
matrix of the link's list is read, the cells and the sampled matrix. That its entries lie in their
ranges at every sampled matrix is `digitsIn_zzOf` (Johnson/HonestTrace/DigitsAtTrace.lean), under
the two hypotheses `hF` and `hm` below.

What is defined and shown.
  `zzFull`, `theSources`: at the full size: each matrix is read at its owner's segment and label
    (`matsOf`, Johnson/HonestTrace/DigitsAtTrace.lean).
  `matsAt`, `matsAt_length`, `zzPlan`, `thePlanSources`: by the public part's own numbers: each
    matrix is read at the link itself under the plan's name, a borrowed one too.
  `digits_meets`: conditional: the digits' keys and bits are honest.

Hypotheses that remain, in `digits_meets`.
  `hF`: `Fo.ZPlan.FromPieces tl` (OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean): on public data.
  `hm`: `MzFits tl` (Johnson/HonestTrace/DigitsAtTrace.lean): on public data.

Imported: Johnson/Desc/ProofFile/Honest/K8/Digits.lean and Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Honest/K3/WitHead.lean calls `theSources` and `thePlanSources`; Honest/K3/WitOwner.lean
states an equation on `matsAt`.

Limits. The list of where the matrices are read must be the one at which the smallness test's own
part and the sender of ZZ are seated: each of the three takes it as its own argument, and nothing
here or there says that the three are one list: at another list the digits that are looked up are
not the digits that are sent. Shown in part: `row_is_sent` (Honest/K3/BzTie.lean) states both ties,
of the keys and of the bits, where the two fillings of the sent arrays name one state, one list and
one round; the list stays a letter there. A reader of cells is asked for a borrowed matrix under its
owner's segment and name (`zzOwn`, Honest/K3/WitOwner.lean, which is the one that is seated);
`zzPlan` asks at the borrower's link under the borrower's name. A list that is too short is filled
with cells 0 in silence (`cellsAtOf`, Honest/K8/Part.lean): `matsAt` has as many members as the
plan's list (`matsAt_length`); of `matsOf` that is not stated in this file. Shown in part:
`matsOf_length` (Johnson/HonestTrace/DigitsAtTrace.lean: 8, 9 or 5 members, under `PartsFit`) and
`matsOf_length_plan` (Johnson/HonestTrace/PlanLabelsOfMarks.lean: as many members as the plan's
list, under `PlanMarks` and `PartsFit`), both at the links below 25.
Without these hypotheses it is stated
in neither of those two files. Outside its window a combination's digits are in range and do not
give it back: `digits_meets` says that the lookup's relation holds of the digits that are sent, at
every sampled matrix; it says nothing on whether they are the combinations' digits: there the
smallness test's own part stops. The two lists of where a matrix is read differ at a borrowed
matrix; that owner and borrower hold the same entries is a clause of the trace's bundle `MeetsAll`
(Johnson/HonestTrace/Full.lean), and no equation between `zzFull` and `zzPlan` is stated. Shown in
part: `zzOwn_eq` (Honest/K3/Law/WitOwnerFull.lean): zzOwn X k C ts = zzFull X k C ts at the links
below 25, conditional on `PlanLabels X` and `PlanOwners X`: of the seated `zzOwn`, not of `zzPlan`.
The head's public data still depend on the instance through a letter.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitPlan
import Johnson.HonestTrace.DigitsAtTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (matsOf MzFits digitsIn_zzOf)
open ProofFile.Honest.K8 (zzOf)

/-- ZZ of the link's smallness test, at the full size. -/
def zzFull (X : OnBytes.Model.Verify.Public) (link : ℕ) (C : Cells) (ts : List Int) :
    ℕ → ℕ → Cb.Gl.F := zzOf (tlAt X link) (matsOf X link) C ts

/-- **The filling at the full size, ZZ filled.** -/
def theSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr' :=
  fullSources X cells weights pubH (zzFull X)

/-- Where the matrices of a link's list are read: at the link itself, under the plan's names, from
column 0 on. -/
def matsAt (X : OnBytes.Model.Verify.Public) (link : ℕ) : List (ℕ × String × ℕ) :=
  (tlOf X link).mats.toList.map fun M => (link, M.name, 0)

/-- It has as many members as the plan's list. -/
theorem matsAt_length (X : OnBytes.Model.Verify.Public) (link : ℕ) :
    (matsAt X link).length = (tlOf X link).mats.size := by
  simp [matsAt]

/-- ZZ of the link's smallness test, by the public part's own numbers. -/
def zzPlan (X : OnBytes.Model.Verify.Public) (link : ℕ) (C : Cells) (ts : List Int) :
    ℕ → ℕ → Cb.Gl.F := zzOf (tlOf X link) (matsAt X link) C ts

/-- **The filling by the public part's own numbers, ZZ filled.** -/
def thePlanSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr' :=
  planSources X cells weights pubH (zzPlan X)

/-- **The digits' keys and bits are honest**, at every list of where the matrices are read, all
cells and every sampled matrix. Conditional on `Fo.ZPlan.FromPieces tl` and `MzFits tl`, both on
public data. At any size. No instance of these hypotheses is exhibited in this file: the library
shows `FromPieces` at every smallness test's structure of what `Verify.publicOf`
(OnBytes/Model/VerifyPublic.lean) returns (`public_G_from`, `public_A_from`, `public_H_from`,
OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean); tests with code for both (`piecesFitB`, `mzFitsB`,
Honest/K3/WitFits.lean, with `piecesFitB_holds` and `mzFitsB_holds`) accept at the five links of a
synthetic public part (Honest/K3/WitFitsGuards.lean [not in this library]); `fromPieces_in_scope`
and `mzFits_in_scope` (Johnson/Goal/HonestTrace/DigitsAtTraceInScope.lean [not in this library])
state both hypotheses of the structures of public files in the goals' scope, at
the links below 25; this file does not import that one. This library lacks that file, so what
is said of it here can not be checked from this library. -/
theorem digits_meets {tl : OnBytes.Model.HTailF2} (hF : Fo.ZPlan.FromPieces tl) (hm : MzFits tl)
    (mats : List (ℕ × String × ℕ)) (C : Cells) (ts : List Int) :
    (lookZ tl (zzOf tl mats C ts)).Meets tl.f9 5 :=
  lookZ_meets hF (digitsIn_zzOf mats C ts hF hm)

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.matsAt_length
#print axioms ProofFile.Honest.K3.digits_meets
