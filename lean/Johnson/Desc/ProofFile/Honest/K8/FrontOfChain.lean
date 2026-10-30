-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/FrontOfChain.lean: THE SMALLNESS TEST: THE NAMED PREMISE
`FrontAtStandN` (Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean: at every stand of the batching:
the window of slots ends inside the ledger's number of slots; the lengths handed to the test are the
data's), AT THE LOT's OWN LENGTHS `ProofFile.k8NU Bs.G₀ Xl`, IS PAID AT THE 24 SEGMENTS IN FRONT OF THE
HEAD's, WHERE THE THREAD's BLOCKS ARE THE FIRST CHAIN's OWN, IN THE GOALS' SCOPE. One joining; none
of the library's goals.

  **`frontAtStandN_of_chain`** the scope · the files read · an opening of the description · the
                   description's test on its plan · l < 24 · the built segment number l ·
                   ChainThread T b c Z l ⊢ FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b, at every
                   Lk, p, φ and Ok
By: `reach_at_stand` (FrontOfReach.lean): each stand's state in front is reached · `slot_at_batch`
(Johnson/Desc/K8/Honest/SlotAtReach.lean) · `lengths_lot_at_batch` (LengthsAtPlans.lean) · the
library's K9.get_fork.
Limits. `ChainThread` (K8BehindTop.lean: six ties of the thread to the chain) IS PAID BY NOBODY
HERE. NOTHING AT THE HEAD's SEGMENT: the second fact is had there too, the first not. NO MEMBER:
where there is no stand all is idle. The promise Ok is not used. IN SCOPE ALONE. No prover stands in
it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.K8BehindTop
import Johnson.Desc.K8.Honest.SlotAtReach
import Johnson.Desc.K8.Honest.LengthsAtPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9L (Pub9)
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {α : Type} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option Pub9 → Prop}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE NAMED PREMISE `FrontAtStandN`, AT THE LOT's OWN LENGTHS, IS PAID.** -/
theorem frontAtStandN_of_chain (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) : FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  intro κ s m En ds y cols s' x z G hSt _ tlS a ht ha
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt C.len hq C.stored
  rw [C.ft, C.bs, C.border] at r
  have r9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (q, s) := by
    rw [if_neg (by omega)] at r
    exact r
  exact ⟨slot_at_batch hS hR O hOk hl r9 ht (Desc.K9.get_fork s a ha),
    lengths_lot_at_batch hS hR O (by omega) e3 r ht⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.frontAtStandN_of_chain
