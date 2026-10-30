-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/TraceCellsInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE
AT WHICH publicOf RETURNS, AND EVERY REQUEST THAT IS SERVED, THE CELLS OF THE OUTPUT HEAD READ OFF
THE LIBRARY's HONEST TRACE (Johnson/HonestTrace/Full.lean: trFull) MEET WHAT THE HONEST SIDE OF THE
SUB-PROTOCOL "the output head's own rounds" IS ASKED OF ITS CELLS: the normalization's 17 identities
at every position, HonestHead, and the nine keys' fields at the library's table EX. One statement,
by calls: every premise of headCells_honest (Honest/K6/Law/TraceCells.lean) is paid from the three
premises on the public files, "the planes have the values 0 and 1" and "the request is served".
IT IMPORTS MODULES UNDER Johnson/Goal/ DIRECTLY (HonestTrace/FullInScope, Meaning/HeadCondScope): it
names the goals' scope. It defines nothing. No definition of the honest side imports it.

What it is not. OF THE LIBRARY's HONEST TRACE trFull, AT THE FULL SIZE: a runnable model's trace is
another text, tied to it by no theorem. CONDITIONAL on the three premises on the public files (Z is
in the goals' scope; the goals' reader returns pp; publicOf returns X), on planes with the values 0
and 1, and on ServesAt X i x: that these hold together of some files, index and request is not shown
here. Parts of it stand at the stored full-size files: inputAroundTheStart_atStoredFiles
(AtFullSide/HonestTrace/EntersAtStoredFilesInput.lean) has the reader's return and ServesAt at some
index and request, at the public data of a return of the prover's maker; inScope_full
(Johnson/Goal/Files/ScopeExample.lean) has the scope. THE PREMISE ON THE PLANES IS MET AT THE
LIBRARY's TRUE PLANES TOO (planesOf_01, Johnson/HonestTrace/FullPlanes.lean): so the statement holds
of the library's theTrace, which is trFull at these planes: that is not stated here. traceCells is
not what the honest side reads: that its own reader agrees with it inside the ranges is not said
here. The identities and the two sums are 0 modulo the field's prime. No verifier's state, no round
and no run stands in it. Nothing on soundness, on completeness or on what a proof hides.
CALLED: headCells_honest; meetsAll_in_scope (Johnson/Goal/HonestTrace/FullInScope.lean); ok_in_scope
(Johnson/Goal/Meaning/HeadCondScope.lean); public_of_core (Johnson/Meaning/PublicCore.lean);
core_of_scope (Johnson/Goal/Meaning/ScopeCore.lean); tabEX_cast (Kinds/Law/CellsOfSaysEX.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCells
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.Desc.Kinds.Law.CellsOfSaysEX

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref AcceptancePolicy Mat Instance)
open OnBytes.HonestTrace (MeetsAll Tr trFull ServesAt meetsAll_in_scope)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **IN SCOPE, AT A SERVED REQUEST, THE CELLS OFF THE LIBRARY's HONEST TRACE ARE HONEST.** work: a
letter, which stands in the policy's term alone. -/
theorem headCells_honest_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {pl : ℕ → ℕ → ℕ → ℤ}
    (h01 : ∀ k r c, pl k r c = 0 ∨ pl k r c = 1) {i : Cm.Idx} {x : Instance ppref}
    (Sv : ServesAt X i x) (work : Nat) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
    letI : Policy := (parOf X.hS work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    (dataOf (traceCells X i (trFull X pl i x))).Holds ∧
      HonestHead (traceCells X i (trFull X pl i x)).toCells ∧
      NineKeys tabEX (traceCells X i (trFull X pl i x)) :=
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  headCells_honest (meetsAll_in_scope hZ hR h h01 Sv) B.full B.sh work
    (InScope.ok_in_scope hZ hR h work) Sv.2.1 tabEX fun u _ => tabEX_cast u

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCells_honest_in_scope
