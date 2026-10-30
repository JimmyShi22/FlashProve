-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/TraceCellsSays.lean: THE CELLS OF THE OUTPUT HEAD, READ OFF A
TRACE THAT MEETS THE BUNDLE MeetsAll (Johnson/HonestTrace/Full.lean), STAND IN THE SUB-PROTOCOL's
TWO RELATIONS ON CELLS, WHOLE (CellRelN, Kinds/HeadNormLaw.lean; CellRel, Kinds/HeadLaw.lean), AND
SO, BY THE LIBRARY's LEMMA 1 (lemma1_whole, Kinds/Law/NormProof.lean), WHAT THESE RELATIONS MEAN
HOLDS OF THEM OVER THE INTEGERS: Says (the policy's three clauses on the costs of the cells' own
logits) and SaysN (at every position the final normalization's integer root, reciprocal and clamped
products). Statements and proofs, by calls.

What it is not. NO NEWS ON THE MODEL: in scope "the policy holds of the program's logits, over the
integers" is a premise (it is a clause of ServesAt). What is shown is that the library's truth,
carried through the sub-protocol's sentences in the field, comes back to the integers IN THE
SUB-PROTOCOL's OWN WORDS (cost and gap of the cells). ONE WAY ALONE: from "served" to Says and
SaysN. That the cells' logits and costs are the program's (lgK, costOf) is not said here. OF A TRACE
THAT MEETS THE BUNDLE, AT THE FULL SIZE: the library shows the bundle of its honest trace trFull; a
runnable model's trace is another text, tied to it by no theorem. CONDITIONAL as headCells_honest
and headCells_honest_in_scope are; the premise on the planes is met at the library's true planes too
(planesOf_01, Johnson/HonestTrace/FullPlanes.lean), so the statement in scope holds of the library's
theTrace: that is not stated here. traceCells is not what the honest side reads. No verifier's
state, no round and no run stands in it. Nothing on soundness, on completeness or on what a proof
hides.
IT IMPORTS, THROUGH TraceCellsInScope, MODULES UNDER Johnson/Goal/. It defines nothing.

  relations_of_three      at any cells: small, the 17 identities, HonestHead and the nine keys'
                          fields GIVE the two relations, field for field but for bytes, which
                          follows from the digits; with Lemma 1, which asks five premises more:
                          Says, SaysN.
  traceCells_smallAll     every cell off the trace, at every feature and position, is below 2^18.
  traceCells_weights      the output matrix that the library reads in an index is at most 2^12.
  headCells_says          at a trace that meets the bundle.
  headCells_says_in_scope in scope, at a served request, at the library's honest trace.
CALLED: lemma1_whole, cellRel_iff, bytes_of_digits (Kinds/Law/NormProof.lean); rows_of_holds
(Kinds/Law/NormJoint.lean); steps_EX, tabEX_cast (Kinds/Law/CellsOfSaysEX.lean); planFacts
(Kinds/Law/NoWrap.lean); okStart_atX (Kinds/Law/HeadPartsAtX.lean); abs_H
(Inst/Model/All/NoWrap.lean); headCells_honest (Honest/K6/Law/TraceCells.lean); meetsAll_in_scope,
ok_in_scope, public_of_core, core_of_scope, as TraceCellsInScope.lean calls them.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCellsInScope
import Johnson.Desc.Kinds.Law.NormProof
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.CellsOfSaysEX
import Inst.Model.All.NoWrap

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref AcceptancePolicy Mat Instance)
open OnBytes.Road.Hd (FullH)
open OnBytes.HonestTrace (MeetsAll Tr trFull ServesAt meetsAll_in_scope)

/-- **SMALL, THE 17 IDENTITIES, HonestHead AND THE NINE KEYS' FIELDS GIVE THE TWO RELATIONS**, field
for field but for bytes, which follows from the digits. Lemma 1 then gives what the relations mean
over the integers: for that step hplan, hreq, hy, htab and hW are asked besides. -/
theorem relations_of_three [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat)
    (c : NCells) (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : Token.y < V)
    (htab : TableOk tab) (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (small : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18)
    (smallS : ∀ f t, (c.stream f t).natAbs < 2 ^ 18) (hH : (dataOf c).Holds)
    (hG : HonestHead c.toCells) (hN : NineKeys tab c) :
    CellRelN c ∧ CellRel c.toCells tab ∧ Says c.toCells ∧ SaysN c := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hN
  have RN : CellRelN c := ⟨small, smallS, rows_of_holds c hH, n6, n7, n8, n9⟩
  have RH : CellRelH c.toCells tab := ⟨n1, n2, n3, n4, n5, hG.guests, ⟨hG.mean, hG.count⟩⟩
  have L := lemma1_whole sT tab c hplan hreq hy htab hW RH RN
  exact ⟨RN, (cellRel_iff _ _).mpr ⟨RN.small, fun _ ht _ hj => bytes_of_digits RN ht hj, RH⟩,
    L.1, L.2⟩

variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Every cell off the trace, at every feature and position, is an entry of the trace: below 129,
so below 2^18. -/
theorem traceCells_smallAll (M : MeetsAll X i x T) :
    (∀ m f t, ((traceCells X i T).cell m f t).natAbs < 2 ^ 18) ∧
      ∀ f t, ((traceCells X i T).stream f t).natAbs < 2 ^ 18 := by
  have hb : ∀ a r c, (T 24 a r c).natAbs < 2 ^ 18 := fun a r c => by
    obtain ⟨h1, h2⟩ := abs_lt.mp (M.small 24 a r c)
    have h3 : (T 24 a r c).natAbs < 129 := by omega
    exact lt_trans h3 (by norm_num)
  refine ⟨fun m f t => ?_, fun f t => hb _ _ _⟩
  cases m <;> exact hb _ _ _

/-- The output matrix that the library reads in an index has entries of size at most 2^12. -/
theorem traceCells_weights (X : OnBytes.Model.Verify.Public) (i : Cm.Idx) (T : Tr) (k v : Nat) :
    ((traceCells X i T).Wh k v).natAbs ≤ 2 ^ 12 := by
  have h := Inst.Model.All.abs_H i.wf k v
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- **THE CELLS OFF A TRACE THAT MEETS THE BUNDLE STAND IN BOTH RELATIONS, AND WHAT THESE MEAN HOLDS
OVER THE INTEGERS.** work: a letter, which stands in the policy's term and in the premise on the
plan. -/
theorem headCells_says (M : MeetsAll X i x T) (hF : FullH X.hS) (h8 : X.hS.digSh = 8)
    (work : Nat) (hplan : (parOf X.hS work).ok = true) (h3 : Inst.Model.Head3 x) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
    letI : Policy := (parOf X.hS work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    CellRelN (traceCells X i T) ∧ CellRel (traceCells X i T).toCells tabEX ∧
      Says (traceCells X i T).toCells ∧ SaysN (traceCells X i T) := by
  letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
  letI : Policy := (parOf X.hS work).policy
  letI := reqX x
  letI : Token := ⟨x.y.val⟩
  obtain ⟨hH, hG, hN⟩ := headCells_honest M hF h8 work hplan h3 tabEX fun u _ => tabEX_cast u
  exact relations_of_three X.hS.tabS tabEX (traceCells X i T) hplan (okStart_atX X.hS work x hF h3)
    (by
      show x.y.val < X.hS.V
      rw [hF.V]
      exact x.y.isLt)
    (steps_EX (planFacts (sT := X.hS.tabS) hplan).hF).ok (traceCells_weights X i T)
    (traceCells_smallAll M).1 (traceCells_smallAll M).2 hH hG hN

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}

/-- **IN SCOPE, AT A SERVED REQUEST, AT THE LIBRARY's HONEST TRACE**: the cells off it stand in both
relations, and Says and SaysN hold of them over the integers. CONDITIONAL: on the three premises on
the public files, the planes' values 0 and 1, and "served". One way alone; no news on the model. -/
theorem headCells_says_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {pl : ℕ → ℕ → ℕ → ℤ}
    (h01 : ∀ k r c, pl k r c = 0 ∨ pl k r c = 1) (Sv : ServesAt X i x) (work : Nat) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
    letI : Policy := (parOf X.hS work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    CellRelN (traceCells X i (trFull X pl i x)) ∧
      CellRel (traceCells X i (trFull X pl i x)).toCells tabEX ∧
      Says (traceCells X i (trFull X pl i x)).toCells ∧
      SaysN (traceCells X i (trFull X pl i x)) :=
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  headCells_says (meetsAll_in_scope hZ hR h h01 Sv) B.full B.sh work
    (InScope.ok_in_scope hZ hR h work) Sv.2.1

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.relations_of_three
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.traceCells_smallAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.traceCells_weights
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCells_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCells_says_in_scope
