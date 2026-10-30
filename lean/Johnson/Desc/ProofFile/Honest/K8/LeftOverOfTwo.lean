-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/LeftOverOfTwo.lean: THE SMALLNESS TEST: THE NAMED PREMISE
`LeftOverAtStand` (Johnson/Desc/ProofFile/Honest/K8/FrontOfReach.lean; group (6) of what the three
sentences of K8BehindTop.lean still owe), AT THE 24 SEGMENTS IN FRONT OF THE HEAD's, WHERE THE
THREAD's BLOCKS ARE THE FIRST CHAIN's OWN, IN THE GOALS' SCOPE, FROM `LeftBelowAtStand`
(LeftOverOfHeard.lean) ALONE: THE PUBLIC TEST IS NO PREMISE ANY MORE. One joining; none of the
library's goals.

  **`leftOverAtStand_of_two`** the scope · the files read · an opening of the description · the
                   description's test on its plan · l < 24 · the built segment number l ·
                   ChainThread T b c Z l · LeftBelowAtStand ⊢ LeftOverAtStand
By: `leftOverAtStand_of_below` (LeftOverOfHeard.lean), stand by stand: each stand's state in front
is reached (`reach_at_stand`), and there the public test says yes at the built segment's data
(`heldPub_at_batch`, Johnson/Desc/K8/Honest/HeldInScope.lean).
Limits. AN IMPLICATION STILL: `LeftBelowAtStand` (at every stand: the state in front shows tl, F and
funs; the words of the key point's coordinate zy_0 lie below the prime; the digits' array has the
name "ZZ"; a member of the link's list for each array) AND `ChainThread` ARE PAID BY NOBODY HERE.
NOTHING AT THE HEAD's SEGMENT. NO MEMBER: that the premises can hold together is not shown; where
there is no stand all is idle. IN SCOPE ALONE. No prover stands in it. Nothing is claimed on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LeftOverOfHeard
import Johnson.Desc.K8.Honest.HeldInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **WITHOUT THE PUBLIC TEST.** -/
theorem leftOverAtStand_of_two (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftBelowAtStand Lk p T b) :
    LeftOverAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨tl, Fk, funs, ht, -, -, -, -⟩ := hL κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt C.len hq C.stored
  rw [C.ft, C.bs, C.border] at r
  exact leftOverAtStand_of_below hS hR O hOk hl e3 C
    (heldPub_at_batch hS hR O hOk (by omega) e3 r ht) hL κ s m En ds y cols s' x z G hSt

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.leftOverAtStand_of_two
