-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeySendsAtMade.lean: (d2) OF «THE CARRYING OF THE PINS»: IN THE GOALS'
SCOPE, FROM THE TWO RETURNS hX AND hm ALONE: THE KEY FILE's THREE LISTS OF SENDINGS ARE THE WRITTEN
ONES: m.key = keySendsFull
(Johnson/G/SendsWritten.lean).

WHAT IS SAID.
  send_of_is        where a made list is held to be W by sendIs, and it is «.ok k»: k = W: by
                    PlanWritten.sameChain_eq (sameChain a b = true → a = b;
                    Johnson/Desc/Ok/PlanWritten/SendsTestLaws.lean).
  bind_ok_eq        a tool: Except's bind behind «.ok a».
  keySends_at_made  **the top.** Its premises: hZ · hX (at every o) · hm (at every digest). NOTHING
                    OF THE PROOF FILE: no test of its door, no «freeOf c = writtenMade».
HOW. IM.sendsFrom_key (IMR/KeySendsOne.lean) at what the planner has made; the pins
(IMR/KeyPinsAtMade.lean · KeyPlansAtMade.lean: sized.key = keyFull · sized.set = recordSet ·
made.key = the three written plans) turn its three equations into «keyMade‹i› = .ok m.key.‹i›»; the
three closed facts key0_send | key1_send | key2_send (IMR/KeySend0 | 1 | 2.lean: each alone in its
file, by Lean's kernel) with sameChain_eq give the equations.
IMR/KeySendsLaw.lean [not in this library]'s keySends_of_written, the same end under a closed premise hW on the whole of
sendsFrom at the written value, IS NOT CALLED: hW is not needed.
What is not claimed. THAT EITHER RETURN IS HAD AT ANY FILES. Nothing on the entry chain's or the
proof file's sendings. No soundness.

-/
import Johnson.IMR.KeyPlansAtMade
import Johnson.IMR.KeySend0
import Johnson.IMR.KeySend1
import Johnson.IMR.KeySend2
import Johnson.Desc.Ok.PlanWritten.SendsTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params
open Johnson.G
open VerifiableInference VerifiableInference.Number.ByRuns
open Lk6.AtPlan (keyFull)

theorem send_of_is {x : Except String ChainSends} {k W : ChainSends} (h : sendIs x W = true)
    (e : x = .ok k) : k = W := by
  rw [e] at h
  exact PlanWritten.sameChain_eq h

theorem bind_ok_eq {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a : Except String α).bind f = f a := rfl

/-- **(d2): in scope the key file's three lists of sendings are the written ones.** -/
theorem keySends_at_made {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {o : ℕ → ByteArray → ByteArray} {X₀ : Model.Verify.Public}
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀) {cfg : ByteArray}
    {m : OfPlan.Made} (hm : Desc.Key.madeAt X₀ Z.lay cfg = .ok m) : m.key = keySendsFull := by
  obtain ⟨-, -, ⟨e, hs⟩, -, hkey, -, -, -, -⟩ := keyPins_at_made hZ hX hm
  obtain ⟨hset, hpl, -, -, -, -⟩ := keyPlans_at_made hZ hX hm
  obtain ⟨w, s, a1, a2, a3, a4, a5⟩ := sendsFrom_key hs hpl
  rw [hkey] at a1 a2 a3 a4 a5
  rw [hset] at a2 a3 a5
  have e0 : keyMade0 = .ok m.key.1 := by
    unfold keyMade0
    rw [a1, bind_ok_eq]
    exact a3
  have e1 : keyMade1 = .ok m.key.2.1 := by
    unfold keyMade1
    rw [a2, bind_ok_eq]
    exact a4
  exact Prod.ext (send_of_is key0_send e0)
    (Prod.ext (send_of_is key1_send e1) (send_of_is key2_send a5))

end IM

#print axioms IM.send_of_is
#print axioms IM.bind_ok_eq
#print axioms IM.keySends_at_made
