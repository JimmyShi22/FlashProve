-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyPinsAtMade.lean: THE PINS AT Key.madeAt's OWN RETURN, A FIRST FILE: in the goals'
scope, from the two returns hX (publicOfO's, at every function o in the second hash function's
place) and hm (Key.madeAt's, at every digest): what the key file's description reads of m, as far
as it is tied to written values by laws. One place to call.
It belongs to «the carrying of the pins».

WHAT IS SAID.
  madeAt_sends     one unfolding of Key.madeAt (Johnson/Desc/Key/Road.lean): m.p.X is the X that was
                   handed in; chainsOf returned m.p.chains; and sendsFrom at what was made returned
                   the list of seven: m.key's three, the entry chain's e, m.proof's three.
  keyPins_at_made  **the pins**: these three, and: the key of m's scan is the full size's (the
                   ledger's hk: IMR/KeyBackOfRows.lean) · the planner's sizes of a key file are the
                   written keyFull · the three sendings' codes are keyFull's · the layout of the
                   weights is what wsLayOf returns at written values.
HOW. Calls: Johnson/RunOne/Law/KeyInScope.lean (readOf_publicOfO · key_in_scope ·
sendsFrom_key_codes · wsLay_at_policy) · key_of_steps
(Johnson/Goal/Numbers/KeyInScope.lean) with publicSteps_of_O · inScope_policy.
What is not claimed. THAT EITHER RETURN IS HAD AT ANY FILES. The entry chain's sendings e stand
under ∃: no value of them is said. NOT HERE, AND OWED: that made.key's three plans are the written
ones · the three sendings as written values · m.p.chains.key, which is read back from the parameter
bytes, its plan above all · what declKOf and toldOfMade return. No soundness.

-/
import Johnson.RunOne.Law.KeyInScope
import Johnson.Goal.Numbers.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines)
open Lk6.AtPlan
open VerifiableInference
open VerifiableInference.Desc (Key.madeAt)
open Johnson.G (ChainSends sendsFrom)
open Johnson.G.OfPlan (Made)

/-- One unfolding of Key.madeAt. -/
theorem madeAt_sends {X₀ : Public} {lay cfg : ByteArray} {m : Made}
    (hm : Desc.Key.madeAt X₀ lay cfg = .ok m) :
    m.p.X = X₀ ∧ chainsOf X₀ (some lay) cfg = .ok m.p.chains ∧
      ∃ e : ChainSends, sendsFrom m.p.chains.made =
        .ok [m.key.1, m.key.2.1, m.key.2.2, e, m.proof.1, m.proof.2.1, m.proof.2.2] := by
  unfold Desc.Key.madeAt at hm
  obtain ⟨ch, h1, hm⟩ := exc_bind hm
  obtain ⟨b, h2, hm⟩ := exc_bind hm
  obtain ⟨l, h3, hm⟩ := exc_bind hm
  split at hm
  · cases hm
    exact ⟨rfl, h1, _, h3⟩
  · cases hm

/-- **The pins at Key.madeAt's own return, in scope.** -/
theorem keyPins_at_made {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {o : ℕ → ByteArray → ByteArray} {X₀ : Public}
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀) {cfg : ByteArray} {m : Made}
    (hm : Desc.Key.madeAt X₀ Z.lay cfg = .ok m) :
    m.p.X = X₀ ∧ chainsOf X₀ (some Z.lay) cfg = .ok m.p.chains ∧
      (∃ e : ChainSends, sendsFrom m.p.chains.made =
        .ok [m.key.1, m.key.2.1, m.key.2.2, e, m.proof.1, m.proof.2.1, m.proof.2.2]) ∧
      PlanWritten.keyOf m = PlanWritten.fullKey ∧
      m.p.chains.made.sized.key = keyFull ∧
      m.key.1.codes = keyFull.codes ∧ m.key.2.1.codes = keyFull.codes ∧
      m.key.2.2.codes = keyFull.codes ∧
      wsLayOf wsFull true recordLines.blockLog = .ok m.p.X.layers.wsLay := by
  obtain ⟨eX, hc, e, hs⟩ := madeAt_sends hm
  have hP := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  obtain ⟨c1, c2, c3⟩ := Johnson.RunOne.Law.SourceIs.sendsFrom_key_codes hs
  obtain ⟨v, hv⟩ := inScope_policy hZ
  have hkey : PlanWritten.keyOf m = PlanWritten.fullKey := by
    unfold PlanWritten.keyOf
    rw [eX]
    rw [hv] at hX
    exact PlanWritten.key_of_steps (PlanWritten.publicSteps_of_O hX)
  have hw : wsLayOf wsFull true recordLines.blockLog = .ok m.p.X.layers.wsLay := by
    rw [eX]
    rw [hv] at hP
    exact Johnson.RunOne.Law.UnitsInScope.wsLay_at_policy hP
  exact ⟨eX, hc, ⟨e, hs⟩, hkey, hk, by rw [c1, hk], by rw [c2, hk], by rw [c3, hk], hw⟩

end IM

#print axioms IM.madeAt_sends
#print axioms IM.keyPins_at_made
