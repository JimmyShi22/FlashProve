-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/SeatsAtEnd.lean:
hS: AT THE FIRST CHAIN'S REACHED LAST STATE THE BOOK SEATS EACH MESSAGE WHERE THE READER'S LIST HAS
IT: the binder hS of the law for the last chain's row (`own3_at_top`, Johnson/LLT25R/LastTop.lean),
in its letters. A JOINING OF TWO FILES' LEMMAS. One statement with its proof; no definition.

Main name (namespace `Meaning.K2`).
  **`hS_at_end`**: in scope, at an opening's own chain, where `F.planOk` accepts, under hB
    (`K12.Door.sendsAreB …`: a test on the plan, with code), hL (`laidAtCodes Z.first.codes
    Z.made.proof.1 = some L`) and hs (`seats = L.places`: a closed equation on the public files):
    inside any condition Oc, at Rc := `EndAt₁ (ProofFile.seatedAt secondHashFunction Z Np c)`
    (Johnson/Top/H0/Walk/ReachThree.lean) with any rider Pp on the public part, without a mark: for
    every f that `firstOfS` hands on: `LLT25.SeatsNumber seats f.book`.

By: `hS_of_five` (Johnson/Desc/Book/LastSeats.lean) at
`five_at_end_planOk` (Johnson/IMR/EndFivePaid.lean). Oc is not spent.
WHO PAYS THE THREE PREMISES ON THE PLAN. hL at L := the written list: `laid_in_scope`
(Johnson/HB/LLHARD/PlanInScope.lean), under a named test. hs at the composed meaning's seats: an
equation in scope (Johnson/Second/Seam/SeatsPlacesInScope.lean), over `seats_are_places` (by the
kernel). hB: named in Johnson/IMR/EndFivePaid.lean; no theorem shown here.
Limits. NO MEMBER. At o := `OnBytes.secondHashFunction`. get := the identity on what the first chain hands on.
Nothing on soundness or on hiding.

-/
import Johnson.IMR.EndFivePaid
import Johnson.LLT25R.LastReaders
import Johnson.Desc.Book.LastSeats
import Johnson.Desc.Plain.StartThreeAtPure
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Third (firstOfS)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

/-- **hS, IN ITS LETTERS.** -/
theorem hS_at_end {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L)
    (seats : List (ℕ × ℕ)) (hs : seats = L.places) (Np : H2U.Places4)
    (Pp : ProofFile.InstPub → Prop) (Oc : ProofFile.InstPub × S → Strs → Prop) :
    ∀ q y, Oc q y → (EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q ∧ Pp q.1) →
      q.2.failed = none → ∀ f, firstOfS q.2 = some f → LLT25.SeatsNumber seats f.book := by
  subst hs
  intro q y _ hq hm f hf
  exact Book.hS_of_five (fun a : ProofFile.InstPub × S => a)
    (fun q => EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q ∧ Pp q.1)
    (fun p => Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p)
    (fun _ h => h.1) L (five_at_end_planOk hS O hF hB hL) q hq hm f hf

#print axioms hS_at_end

end Meaning.K2
