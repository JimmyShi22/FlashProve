-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04CondPaidT.lean: THE FACT tidy OF THE FIELD wide OF K4's CONDITION (K4Cond,
Johnson/Road/K4/K04Cond.lean; one of the five of WideLeft, Johnson/Road/K4/K04CondPaidA.lean) BY ITS
AUTHORS' THEOREM tidy_at_open (Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean): called, pointwise, at the
relation "reached, with a condition Pp on the public part" (RchPub,
Johnson/Top/H0/Walk/ReachPub.lean), general in Pp and in the type Str.

  `tidy_at_pub`: at ANY border k, at every state reached there without a mark: the statement is
    tidy.
No new argument: one call.
Limits. PREMISES, NONE PAID HERE: an opening O: THAT THERE IS ONE IS SHOWN BY NO THEOREM · hD: the
maker returns the opening's own value · hF: that value's test on the plan accepts. NO MEMBER IS
SHOWN. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Desc.AtSeats.Fit.TidyAtOpen
import Johnson.Top.H0.Walk.ReachPub
import Johnson.Road.K4.K04Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (RchPub)

variable {pol ly KL : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The fact tidy at a reached state without a mark**, under O hD hF. -/
theorem tidy_at_pub (O : IM.Open OnBytes.secondHashFunction pol ly KL F Z Bs base c A B)
    (hD : ProofFile.onlineDescription OnBytes.secondHashFunction pol ly KL = .ok F) (hF : F.planOk = true)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) {k : ℕ} (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp k a) (hu : a.1.2.failed = none) :
    OnBytes.Means.tidy4B a.1.2.st = true :=
  Meaning.K2.tidy_at_open hD hF O k a.1 h.1 hu

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tidy_at_pub
