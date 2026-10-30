-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OkCoreAt.lean: FOR THE ITEM "totalB": WHAT K9's THREE CONSTANTS Ok (`okFillLay`,
`okFillAtt`, `okFillHead`, Honest/K9/TotalFill.lean) HOLD FOR THE SMALLNESS TEST: the library's `OkCore` (what
every sort's Ok holds), and so two premises of that test's laws at these constants. Statements and proofs: each unfolds
a definition and reads a field; no thread, no prover; no goal is stated.
  `okCore_lay`, `okCore_att`, `okCore_head`   each constant gives `OkCore nU tlD q` (through the field core of the
      library's `OkLayers`, `OkAtt`, `OkHead`)
  `static_lay`, `static_att`, `static_head`   so: where the library's reader `pi8` shows a structure tlb and the
      snapshot is v: `StaticOk tlb v.F` (the field static): the premise "the promise holds the static clauses" of K8's
      `k8Behind_ok`, at `pi8`
  `sized_lay`, `sized_att`, `sized_head`   and: the snapshot's ledger is `Sized` (off the fields there and four, with
      "what the digits' lookup returned is there" off `NumbersThree`, which stands in all three constants): the
      premise hSz of `termsBack_four`
THAT `static_…` IS THE FIRST PREMISE's VERY FORM LEAN HAS HELD (Honest/K9/K8BehindAt.lean calls the three inside
`k8Behind_ok`; `okStatic_of_core` at `okCore_…` gives the same). THAT `sized_…` IS hSz's IS A
READING: no Lean has joined these. No file of that test is imported here.
WHAT IS NOT CLAIMED. Any of the three constants at any q (their payer at the frame's thread:
Honest/K9/OkFrontAt.lean). No member. `static_…` are called by Honest/K9/K8BehindAt.lean; `okCore_…` and
`sized_of_core` here alone; `sized_…` by no line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll

variable {p4 : OnBytes.Desc.First.K4.Par} {A : Attention.Plan} {Wp : Verify.Public} {nU : Array ℕ} {tlD : HTailF2}
  {pC pD : First.Look.P}

theorem okCore_lay (q : Phi BetaAll × Option Pub9) (h : okFillLay p4 nU tlD pC pD q) : OkCore nU tlD q := h.1.core

theorem okCore_att (q : Phi BetaAll × Option Pub9) (h : okFillAtt A nU tlD pC pD q) : OkCore nU tlD q := h.1.core

theorem okCore_head (q : Phi BetaAll × Option Pub9) (h : okFillHead Wp nU tlD pC pD q) : OkCore nU tlD q := h.1.core

theorem static_lay (q : Phi BetaAll × Option Pub9) (tlb : HTailF2) (v : Pub9) (h : okFillLay p4 nU tlD pC pD q)
    (ht : (pi8 q.1).1 = some tlb) (hv : q.2 = some v) : StaticOk tlb v.F := (okCore_lay q h).static tlb v ht hv

theorem static_att (q : Phi BetaAll × Option Pub9) (tlb : HTailF2) (v : Pub9) (h : okFillAtt A nU tlD pC pD q)
    (ht : (pi8 q.1).1 = some tlb) (hv : q.2 = some v) : StaticOk tlb v.F := (okCore_att q h).static tlb v ht hv

theorem static_head (q : Phi BetaAll × Option Pub9) (tlb : HTailF2) (v : Pub9) (h : okFillHead Wp nU tlD pC pD q)
    (ht : (pi8 q.1).1 = some tlb) (hv : q.2 = some v) : StaticOk tlb v.F := (okCore_head q h).static tlb v ht hv

/-- From the core and "what the digits' lookup returned is there". -/
theorem sized_of_core {q : Phi BetaAll × Option Pub9} (C : OkCore nU tlD q) (N : NumbersThree q) (v : Pub9)
    (hv : q.2 = some v) : OnBytes.PscRun.Sized v.F := by
  obtain ⟨tlb, ht⟩ := Option.isSome_iff_exists.1 C.there
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (N.heard tlb ht)
  exact (C.four v tlb g hv ht hg).1

theorem sized_lay (q : Phi BetaAll × Option Pub9) (v : Pub9) (h : okFillLay p4 nU tlD pC pD q) (hv : q.2 = some v) :
    OnBytes.PscRun.Sized v.F := sized_of_core (okCore_lay q h) h.2.2 v hv

theorem sized_att (q : Phi BetaAll × Option Pub9) (v : Pub9) (h : okFillAtt A nU tlD pC pD q) (hv : q.2 = some v) :
    OnBytes.PscRun.Sized v.F := sized_of_core (okCore_att q h) h.2.1.2 v hv

theorem sized_head (q : Phi BetaAll × Option Pub9) (v : Pub9) (h : okFillHead Wp nU tlD pC pD q) (hv : q.2 = some v) :
    OnBytes.PscRun.Sized v.F := sized_of_core (okCore_head q h) h.2.1.2 v hv

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.okCore_lay
#print axioms ProofFile.Honest.K9.okCore_att
#print axioms ProofFile.Honest.K9.okCore_head
#print axioms ProofFile.Honest.K9.static_lay
#print axioms ProofFile.Honest.K9.static_att
#print axioms ProofFile.Honest.K9.static_head
#print axioms ProofFile.Honest.K9.sized_of_core
#print axioms ProofFile.Honest.K9.sized_lay
#print axioms ProofFile.Honest.K9.sized_att
#print axioms ProofFile.Honest.K9.sized_head
