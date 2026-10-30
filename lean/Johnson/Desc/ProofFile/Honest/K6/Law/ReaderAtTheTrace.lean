-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ReaderAtTheTrace.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE
(hZ) THAT THE GOALS' READER READS (hR: VerifierAndGoals.readFiles returns) AND AT WHICH publicOf RETURNS X
(h), AT A SERVED REQUEST, WHERE THE HONEST SIDE COUNTS THE HEAD's SEGMENT AS NUMBER 24 AND ITS SHAPE
IS X's: THE LIBRARY's READER OF A TRACE BY LABELS (cellOf), AT THE LIBRARY's FULL-SIZE TRACE WITH
ITS TRUE PLANES (theTrace, Johnson/HonestTrace/FullPlanes.lean), MEETS THAT TRACE WHERE THE HEAD's
RELATION READS (ReaderMeets, Honest/K6/Law/SameCellsTraceAt.lean). AND THE SAME BEHIND THE LIBRARY's
TraceHinge (Johnson/HonestTrace/TraceHinge.lean): wherever a trace function that meets the hinge
answers ω at an index i and an input ξ, there are an instance x that is read off ξ and planes with
the values 0 and 1 such that i serves x and cellOf X ω meets trFull X pl i x.

What it is for. A premise on a prover's one input that has the form "there are an index, an instance
and planes: the planes are 0 or 1; the request is served; the reader meets trFull at these; ..." can
take these three clauses from here, in that order, where the input's trace comes from a function
that meets the hinge and the cells' reader is cellOf.

What it is not. NO PAYMENT OF THE HINGE: that a prover's trace function meets TraceHinge is a
premise. THE HINGE GOES ONE WAY: it does not say that a trace is there at any input, and the
function that never answers meets it: with its premise "the function answers ω" the last theorem may
hold of nothing at a given function. AT THE READER cellOf ALONE. The two equations on the honest
side's numbers (h0, h1) are premises. In planes_served_reader_at_theTrace "served" is a premise that
is handed on into the end: two clauses are proved there and the third is carried; in
planes_served_reader_of_hinge it comes out of the hinge. Nothing is said of the weights' reader, nor
of the request and the token that a prover reads off its input. The full size alone. Nothing new on
the model. Nothing on soundness, on completeness or on what a proof hides.
IT IMPORTS A MODULE UNDER Johnson/Goal/ BY NAME (HonestTrace/FullPlanesInScope). It defines nothing.

  theTrace_is_trFull                 theTrace is trFull at the planes plOf: by unfolding.
  plOf_01                            every value of these planes is 0 or 1.
  readerMeets_cellOf_theTrace        the reader meets the trace.
  planes_served_reader_at_theTrace   the three clauses, at a trace ω that is theTrace.
  planes_served_reader_of_hinge      the same behind the hinge.
CALLED: planesOf_01 (Johnson/HonestTrace/FullPlanes.lean); meetsAll_theTrace
(Johnson/Goal/HonestTrace/FullPlanesInScope.lean); headMats_cellOf_in_scope
(Honest/K6/Law/HeadMatsOfTrace.lean); readerMeets_of_all (Honest/K6/Law/SameCellsTraceAt.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.SameCellsTraceAt
import Johnson.Desc.ProofFile.Honest.K6.Law.HeadMatsOfTrace
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.HonestTrace.TraceHinge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6

open Inst.Model (ppref Instance)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr trFull theTrace plOf planesOf_01 cellOf ServesAt TraceHinge
  meetsAll_theTrace headMats_cellOf_in_scope)
open VerifiableInference.Desc.Kinds (Head.Sizes)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- theTrace is trFull at the planes plOf: by unfolding. -/
theorem theTrace_is_trFull (X : OnBytes.Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) :
    theTrace X i x = trFull X (plOf X i x) i x := rfl

/-- Every value of the planes plOf is 0 or 1. -/
theorem plOf_01 (X : OnBytes.Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (k r c : ℕ) :
    plOf X i x k r c = 0 ∨ plOf X i x k r c = 1 :=
  planesOf_01 X x i.mat _ k r c

/-- **THE LIBRARY's READER BY LABELS, AT theTrace, MEETS theTrace WHERE THE HEAD's RELATION READS.**
CONDITIONAL: on the three premises on the public files, "served", and two equations on the honest
side's numbers. -/
theorem readerMeets_cellOf_theTrace [Head.Sizes] (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx}
    {x : Instance ppref} (Sv : ServesAt X i x) (N : HeadWhere) (h0 : N.seg = 24)
    (h1 : N.shape = X.hS) :
    ReaderMeets X N ⟨cellOf X (theTrace X i x)⟩ (theTrace X i x) :=
  readerMeets_of_all X N _ _ fun n r k =>
    headMats_cellOf_in_scope hZ hR h (meetsAll_theTrace hZ hR h Sv) N h0 h1 n r k

/-- **PLANES 0 OR 1 · SERVED · THE READER MEETS trFull AT THESE PLANES**: at a trace ω that is
theTrace. CONDITIONAL as the lemma above. "Served" is a premise, handed on into the end. -/
theorem planes_served_reader_at_theTrace [Head.Sizes] (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx}
    {x : Instance ppref} (Sv : ServesAt X i x) (N : HeadWhere) (h0 : N.seg = 24)
    (h1 : N.shape = X.hS) {ω : Tr} (hω : ω = theTrace X i x) :
    ∃ pl : ℕ → ℕ → ℕ → ℤ, (∀ k r c, pl k r c = 0 ∨ pl k r c = 1) ∧ ServesAt X i x ∧
      ReaderMeets X N ⟨cellOf X ω⟩ (trFull X pl i x) := by
  subst hω
  exact ⟨plOf X i x, plOf_01 X i x, Sv, readerMeets_cellOf_theTrace hZ hR h Sv N h0 h1⟩

/-- **THE SAME BEHIND THE HINGE**: where a trace function that meets TraceHinge answers ω.
CONDITIONAL: on the three premises on the public files, the hinge, "the function answers ω", and
the two equations on the honest side's numbers. -/
theorem planes_served_reader_of_hinge [Head.Sizes] {Xi : Type} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    {trace : Cm.Idx → Xi → Option Tr} {instOf : Xi → Option (Instance ppref)}
    (H : TraceHinge X trace instOf) {i : Cm.Idx} {ξ : Xi} {ω : Tr} (ht : trace i ξ = some ω)
    (N : HeadWhere) (h0 : N.seg = 24) (h1 : N.shape = X.hS) :
    ∃ (x : Instance ppref) (pl : ℕ → ℕ → ℕ → ℤ), instOf ξ = some x ∧
      (∀ k r c, pl k r c = 0 ∨ pl k r c = 1) ∧ ServesAt X i x ∧
      ReaderMeets X N ⟨cellOf X ω⟩ (trFull X pl i x) := by
  obtain ⟨x, hx, Sv, hω⟩ := H i ξ ω ht
  obtain ⟨pl, h01, -, hM⟩ := planes_served_reader_at_theTrace hZ hR h Sv N h0 h1 hω
  exact ⟨x, pl, hx, h01, Sv, hM⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.theTrace_is_trFull
#print axioms ProofFile.Honest.K6.plOf_01
#print axioms ProofFile.Honest.K6.readerMeets_cellOf_theTrace
#print axioms ProofFile.Honest.K6.planes_served_reader_at_theTrace
#print axioms ProofFile.Honest.K6.planes_served_reader_of_hinge
