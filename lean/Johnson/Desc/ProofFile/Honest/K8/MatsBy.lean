-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/MatsBy.lean: the honest side of the smallness test (K8): EACH
SEGMENT's LIST OF MATRICES, BY A KEY: the form of the second letter of the lot's honest side
(`smallLot`, Johnson/Desc/ProofFile/Honest/K8/Part.lean), AND WHAT HOLDS OF IT WHATEVER THE KEY. NO
MAKER OF THE OWNER's KEY IS WRITTEN HERE: the kind "lookup" has one (`K3.matsOwn`,
Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean); Johnson/Desc/ProofFile/Honest/K8/MatsMeet.lean
holds it against this form. THE LIST IS WALKED OFF THE VERY LIST OFF WHICH THE VERIFIER's BLOCK
TAKES THE PLACE's NUMBERS OF COLUMNS AND OF ROWS (`ProofFile.k8Par`, Johnson/Desc/ProofFile/Lot/K8.lean:
the list of matrices in the built segment's plan), entry by entry, through a key: under which
segment's number, which name and from which column on the witness's reader (`Cells`,
Honest/ForKinds.lean) is asked for an entry. The key is a letter here. Definitions with code, and
lemmas by unfolding; none of the library's goals.

  `matsBy key`   the list at a segment: the key at each entry of the segment's planned list, in its
                   order
  `hereKey`, `hereMats`   the key "this segment's number, the entry's own name, from column 0"; the
                   list by it
  `matsBy_length`   as many names as the place has matrices
  **`smallFits_matsBy`**   SO THE PUBLIC PREMISE AT THE SEAT (`smallFits`, Part.lean) HOLDS AT EVERY
                   SEGMENT, AT EVERY PUBLIC DATA AND GROUND, WHATEVER THE KEY: no premise
  `matsBy_get`   entry mu of the list is the key at entry mu of the planned list
  `cellsAtOf_matsBy`   what the half is handed as a matrix's cell: the reader's answer at the key of
                   that entry; 0 beyond the list
  `smallLotHere`   the lot's honest side at `hereMats`: no letter is left but the witness's reader
Limits. ON PUBLIC DATA ALONE. WHICH KEY IS RIGHT IS NOT SAID HERE: a matrix that a segment borrows
from an earlier one has two keys at the reader, the borrower's (`hereKey`) and its owner's;
Part.lean's head asks for the owner's; whether a reader answers alike at both is the reader's
matter. Nothing on what a half plays; nothing is valued here: no program has run these definitions
at public files. Nothing holds a key against a layout or a committed table.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes.Model (TMat)
open OnBytes.Model.Stages (LinkH)

/-- **A segment's list of matrices, by a key**: the key at each entry of the segment's planned
list, in its order. -/
def matsBy (key : Pub → Ground → Nat → TMat → Nat × String × Nat) (Z : Pub) (G : Ground)
    (X : LinkH) (l : Nat) : List (Nat × String × Nat) :=
  X.tl.mats.toList.map (key Z G l)

/-- This segment's number, the entry's own name, from column 0. -/
def hereKey (_ : Pub) (_ : Ground) (l : Nat) (M : TMat) : Nat × String × Nat := (l, M.name, 0)

/-- The list by `hereKey`. -/
def hereMats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat) := matsBy hereKey

/-- As many names as the place has matrices. -/
theorem matsBy_length (key : Pub → Ground → Nat → TMat → Nat × String × Nat) (Z : Pub)
    (G : Ground) (X : LinkH) (l : Nat) :
    (matsBy key Z G X l).length = (k8Par Z G X l).ks.length := by
  simp [matsBy, k8Par]

/-- **The public premise at the seat holds at every segment, whatever the key.** -/
theorem smallFits_matsBy (key : Pub → Ground → Nat → TMat → Nat × String × Nat) (Z : Pub)
    (G : Ground) (X : LinkH) (l : Nat) :
    smallFits (k8Par Z G X l, matsBy key Z G X l) = true := by
  simp [smallFits, matsBy, k8Par]

/-- Entry mu of the list. -/
theorem matsBy_get (key : Pub → Ground → Nat → TMat → Nat × String × Nat) (Z : Pub)
    (G : Ground) (X : LinkH) (l mu : Nat) :
    (matsBy key Z G X l)[mu]? = (X.tl.mats[mu]?).map (key Z G l) := by
  simp [matsBy]

/-- What the half is handed as a matrix's cell. -/
theorem cellsAtOf_matsBy (C : Cells) (key : Pub → Ground → Nat → TMat → Nat × String × Nat)
    (Z : Pub) (G : Ground) (X : LinkH) (l mu i c : Nat) :
    cellsAtOf C (matsBy key Z G X l) mu i c =
      match X.tl.mats[mu]? with
      | some M => signedOf (C.cell (key Z G l M).1 (key Z G l M).2.1 i ((key Z G l M).2.2 + c))
      | none => 0 := by
  unfold cellsAtOf
  rw [matsBy_get]
  cases X.tl.mats[mu]? <;> rfl

variable {W₀ Rc Xi Tr X : Type}

/-- The lot's honest side at `hereMats`: one instance of `smallLot` (Part.lean): what is said there
of that text holds of this one. A WRONG NAME IN mats: the cells are what the reader yields at a
string that is no label: the test then reads other cells, in silence. `hereMats` is the BORROWER's
key: see the Limits above. -/
def smallLotHere (cells : Tr → Cells) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  smallLot cells hereMats

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.matsBy_length
#print axioms ProofFile.Honest.K8.smallFits_matsBy
#print axioms ProofFile.Honest.K8.matsBy_get
#print axioms ProofFile.Honest.K8.cellsAtOf_matsBy
#print axioms ProofFile.Honest.K8.matsBy
#print axioms ProofFile.Honest.K8.hereKey
#print axioms ProofFile.Honest.K8.hereMats
#print axioms ProofFile.Honest.K8.smallLotHere
