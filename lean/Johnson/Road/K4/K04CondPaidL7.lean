-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04CondPaidL7.lean: THE FIELD lay7 OF K4's CONDITION (K4Cond,
Johnson/Road/K4/K04Cond.lean) BY ITS NAME's AUTHORS' THEOREM lay7_reachedR
(Johnson/P1K8R/LayAtK4.lean): called, pointwise, at the relation "reached, with a condition Pp on
the public part" (RchPub, Johnson/Top/H0/Walk/ReachPub.lean), general in Pp and in the type Str.

  `l7_paid`: at every state reached at 28 g + 4: the test of "K8.lay7" at the segment's own number
    accepts. No fence "without a mark" is spent.
No new argument: one call.
Limits. PREMISES, NONE PAID HERE: the goals' scope and an opening (hS, hR, O): THAT THERE IS AN
OPENING IS SHOWN BY NO THEOREM · htl: the struck parts' tl is FillP1.tlAt Z. NO MEMBER IS SHOWN.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.P1K8R.LayAtK4
import Johnson.Desc.Sound.MgWide
import Johnson.Top.H0.Walk.ReachPub
import Johnson.Road.K4.K04Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready (lay7B)
open VerifiableInference.Desc.Sound (WideData)
open Johnson.Desc.First.Walk.Tied (RchPub)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The field lay7**, under hS hR O hg htl. -/
theorem l7_paid (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    (htl : E.dP.tl = VerifiableInference.Desc.First.FillP1.tlAt Z)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp (28 * g + 4) a) :
    ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true := by
  rw [htl]
  exact P1K8S.lay7_reachedR hS hR O hg a h.1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.l7_paid
