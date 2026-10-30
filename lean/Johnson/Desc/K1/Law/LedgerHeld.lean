-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LedgerHeld.lean: the block AS A PIECE OF A DESCRIPTION HOLDS IT: with the test
"every word is below the prime" in front (below, Johnson/Desc/Sound/ChainRule.lean), lifted to the
pair of what was handed to the chain and the chain's own record: is a sending where the block is.
So the law of a sending, and what is owed at the shared chain's second and fifth block (two_core,
five_core, Johnson/Desc/K14/Law/LedgerSends.lean), speak of the block that the maker's piece holds.

Main names: isSend_below; isSend_two_held, isSend_five_held.

What is not claimed. That a file's description seats these blocks at these places. Nothing on
soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.LedgerSend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (below)

/-- **With the test on the words in front a sending is a sending.** -/
theorem isSend_below {T Cl : Type} (P : Par) (stOf : T → Statement) (b : Block T Cl)
    (h : IsSend P stOf b) : IsSend P stOf (below b) := by
  intro s s' r₁ r₂ gs hy
  have hy' : b.decide s [r₁, r₂] gs = .ok s' := by
    unfold below at hy
    dsimp only at hy
    split at hy
    · exact hy
    · cases hy
  exact h s s' r₁ r₂ gs hy'

/-- **The shared chain's second block, as a piece holds it.** -/
theorem isSend_two_held (A : Type) (Q : Desc.K14.P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hbl : Desc.K14.blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (sentU : Array OracleNotice) (hU : Desc.K14.withU Q.S = some sentU) :
    IsSend (Desc.K14.parK1 Q 2 "o_u and the first mask" sentU)
      (fun t : A × Desc.K14.St => t.2.st) ((below b2).lift Prod.snd fun t s => (t.1, s)) := by
  obtain ⟨u, hu, h2, _⟩ := Desc.K14.Law.isSend_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl := Option.some.inj (hu.symm.trans hU)
  exact isSend_lift _ (fun s : Desc.K14.St => s.st) (below b2) Prod.snd (fun t s => (t.1, s))
    (fun _ _ => rfl) (isSend_below _ _ b2 h2)

/-- **The fifth.** -/
theorem isSend_five_held (A : Type) (Q : Desc.K14.P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hbl : Desc.K14.blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    IsSend (Desc.K14.parK1 Q 5 "o_omega and o_sp" (Desc.K14.withOmega Q.S))
      (fun t : A × Desc.K14.St => t.2.st) ((below b5).lift Prod.snd fun t s => (t.1, s)) := by
  obtain ⟨_, _, _, h5⟩ := Desc.K14.Law.isSend_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  exact isSend_lift _ (fun s : Desc.K14.St => s.st) (below b5) Prod.snd (fun t s => (t.1, s))
    (fun _ _ => rfl) (isSend_below _ _ b5 h5)


end VerifiableInference.Desc.K1
