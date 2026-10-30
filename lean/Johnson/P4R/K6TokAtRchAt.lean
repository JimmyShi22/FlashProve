-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/K6TokAtRchAt.lean, BESIDE P4R/K6AtRchAt.lean: ONE MORE PREMISE OF THE LAW OF THE OUTPUT HEAD'S OWN ROUNDS "UNDER
Rch 341 a", AT Rch := RchAt (FD Z A B c): what is heard as the reply is an entry of the vocabulary: TokSmall Wp.hS.V a.1.2, IN THE
LAW'S OWN LETTER Wp. One call of a theorem along the fold (IM.tokSmallAt_border, IMR/TokAtReach.lean), with the tie
of the public parameters (P4.wp_is). No premise on the list of rounds.
Every letter under "there is": none. The witnesses inside RchAt are not the run's own: nothing is concluded of them.
What it does not say. "No mark" is not asked (it stands in the law's binder: idle). Nothing on soundness.
-/
import Johnson.P4R.K6AtRchAt
import Johnson.IMR.TokAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (TokSmall)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Str : Type}

/-- **What is heard as the reply is an entry of the vocabulary.** -/
theorem tokSmall_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Wp : OnBytes.Model.Verify.Public}
    (hX : OnBytes.Model.Verify.publicOf P.pol P.KL (some lay) = .ok Wp) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 341 a → a.1.2.failed = none →
      TokSmall Wp.hS.V a.1.2 := by
  intro a h _
  rw [(wp_is O hX).1]
  exact IM.tokSmallAt_border hS hR O (by decide) (reach_of_rchAt h)

end P4

#print axioms P4.tokSmall_rchAt
