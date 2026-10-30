-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SmpWalkOpen.lean: no soundness is claimed.
A foot to SmpWalk.lean: descPure_smpStay's chain stands behind «∃ Z A B c»; a joiner holds the opening IM.Open (Johnson/IMR/SeatOpen.lean), with its own letter c. Here the two are one.
  first_of_eq         two values of ProofFile.fileDescBy that are equal have one first chain
  **open_smpStay**    ProofFile.onlineDescription o pol lay KL = .ok F · IM.Open o pol lay KL F Z Bs base c A B ⇒ ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits (ByS SmpStay) b
  open_planOk         F.planOk = true · the opening ⇒ ∀ b ∈ c.blocksInOrder, b.planOk = true (flat_planOkT at O.desc)
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SmpWalk
import Johnson.Desc.AtSeats.Fit.TidyPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open Meaning.K2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Fits)
open VerifiableInference.Desc.K1 (SmpStay)

theorem first_of_eq {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z Z' : ProofFile.Pub}
    {A A' : ProofFile.SharedSeat} {B B' : ProofFile.SecondSeat} {c c' : Chain S ProofFile.Cl}
    (e : ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c =
      ProofFile.fileDescBy o mk Z' A' B' (fun s => s) (ProofFile.startS Z') c') : c = c' := by
  have k := congrArg (fun F : FileDescription ProofFile.Inst =>
    (⟨F.S₁, ⟨F.Cl, F.first⟩⟩ : Σ T : Type, Σ C : Type, Chain T C)) e
  have k' : (⟨S, ⟨ProofFile.Cl, c⟩⟩ : Σ T : Type, Σ C : Type, Chain T C) = ⟨S, ⟨ProofFile.Cl, c'⟩⟩ := k
  cases k'
  rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The walk, in the opening's own letters.** -/
theorem open_smpStay (hF : ProofFile.onlineDescription o pol lay KL = .ok F)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits (ByS SmpStay) b := by
  obtain ⟨Z', A', B', c', -, e, k⟩ := descPure_smpStay hF
  obtain rfl : c = c' := first_of_eq (O.desc.symm.trans e)
  exact k

theorem open_planOk (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∀ b ∈ c.blocksInOrder, b.planOk = true := flat_planOkT O.desc hp

end

end ToldDesc

#print axioms ToldDesc.first_of_eq
#print axioms ToldDesc.open_smpStay
#print axioms ToldDesc.open_planOk
