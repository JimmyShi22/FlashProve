-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/TraceCellsAtTheTrace.lean: AT ALL PUBLIC FILES IN THE GOALS'
SCOPE AT WHICH publicOf RETURNS, AND EVERY REQUEST THAT IS SERVED: THE CELLS OF THE OUTPUT HEAD READ
OFF THE LIBRARY's FULL-SIZE TRACE WITH ITS TRUE PLANES (theTrace,
Johnson/HonestTrace/FullPlanes.lean) MEET what headCells_honest_in_scope
(Honest/K6/Law/TraceCellsInScope.lean) and headCells_says_in_scope
(Honest/K6/Law/TraceCellsSays.lean) say of the cells off trFull at any planes with the values 0 and
1: the normalization's 17 identities, HonestHead and the nine keys' fields; the sub-protocol's two
relations on cells, whole, and Says and SaysN over the integers. Two corollaries, proved by one call
each.

Why. theTrace is trFull at the planes plOf: the library's planesOf at the lists of the trace whose
planes are 0 (trBase); every value of these is 0 or 1 (planesOf_01). It is the trace of which the
library shows its bundle (meetsAll_theTrace, Johnson/Goal/HonestTrace/FullPlanesInScope.lean), and
the one that another file can name without a letter for the planes.

What it is not. NOTHING NEW: two instances of theorems that hold at all planes with the values 0 and
1. Inside the ranges that the head's relation names no cell is read in the planes' matrix of list
24; beyond them a feature walks on into the next numbers of that list (cellIn,
Johnson/Road/HeadPlace.lean), the planes' among them: so the cells off theTrace and those off trFull
at other planes need not be one function. CONDITIONAL on the three premises on the public files and
on ServesAt X i x. All limits of the two theorems that are called hold of these: at the full size;
one way alone; no news on the model; the first's equations are equations in the field; traceCells is
not what the honest side reads; a runnable model's trace is another text, tied to theTrace by no
theorem. Nothing on soundness, on completeness or on what a proof hides.
IT IMPORTS, THROUGH TraceCellsSays, MODULES UNDER Johnson/Goal/. It defines nothing.
CALLED: headCells_honest_in_scope; headCells_says_in_scope; planesOf_01
(Johnson/HonestTrace/FullPlanes.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCellsSays
import Johnson.HonestTrace.FullPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref Instance)
open OnBytes.HonestTrace (ServesAt theTrace planesOf_01)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref}

/-- **IN SCOPE, AT A SERVED REQUEST, THE CELLS OFF THE LIBRARY's TRACE WITH ITS TRUE PLANES ARE
HONEST.** CONDITIONAL: on the three premises on the public files and "served". -/
theorem headCells_honest_theTrace (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) (work : Nat) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
    letI : Policy := (parOf X.hS work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    (dataOf (traceCells X i (theTrace X i x))).Holds ∧
      HonestHead (traceCells X i (theTrace X i x)).toCells ∧
      NineKeys tabEX (traceCells X i (theTrace X i x)) :=
  headCells_honest_in_scope hZ hR h (fun k r c => planesOf_01 X x i.mat _ k r c) Sv work

/-- **THE SAME CELLS STAND IN BOTH RELATIONS, AND Says AND SaysN HOLD OF THEM OVER THE INTEGERS.**
CONDITIONAL: on the three premises on the public files and "served". One way alone; no news on the
model. -/
theorem headCells_says_theTrace (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) (work : Nat) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
    letI : Policy := (parOf X.hS work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    CellRelN (traceCells X i (theTrace X i x)) ∧
      CellRel (traceCells X i (theTrace X i x)).toCells tabEX ∧
      Says (traceCells X i (theTrace X i x)).toCells ∧
      SaysN (traceCells X i (theTrace X i x)) :=
  headCells_says_in_scope hZ hR h (fun k r c => planesOf_01 X x i.mat _ k r c) Sv work

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCells_honest_theTrace
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCells_says_theTrace
