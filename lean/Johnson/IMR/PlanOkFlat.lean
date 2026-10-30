-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/PlanOkFlat.lean: A LIGHT FILE: it imports Johnson/IMR/SeatOpen.lean alone: WHERE THE
DESCRIPTION PASSES ITS OWN TESTS ON THE PLAN, EVERY SUB-PROTOCOL OF THE FIRST CHAIN's FLAT LIST
PASSES ITS OWN AND IS SHAPED: blocksOk c.blocksInOrder = true: the premise of bookAt_whole
(Johnson/IMR/BookAtWhole.lean) and of Johnson/IMR/SendsFinal.lean, from F.planOk = true.
(Its kin: Keeps.planOk_blocks, Johnson/Desc/PlanPasses.lean: «∀ b ∈ F.first.blocksInOrder, b.planOk = true»: without «shaped», and at F.first. planOk_at_open (declared nowhere in this library) goes by it.)
  blocksOk_of_planOk   Open … F … c … → F.planOk = true → blocksOk c.blocksInOrder = true. At every o.
No state is spoken of. No soundness.
-/
import Johnson.IMR.SeatOpen

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

theorem blocksOk_of_planOk {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : Open o pol lay KL F Z Bs base c A B)
    (hp : F.planOk = true) : VerifiableInference.Desc.blocksOk c.blocksInOrder = true := by
  rw [O.desc] at hp
  unfold FileDescription.planOk at hp
  rw [Bool.and_eq_true] at hp
  have hc := hp.1
  unfold FileDescription.planOkCore at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, a⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact a

end IM

#print axioms IM.blocksOk_of_planOk
