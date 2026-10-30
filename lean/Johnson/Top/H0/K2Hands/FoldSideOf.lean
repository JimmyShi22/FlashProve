-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FoldSideOf.lean: the code switch's law: THE TWO PREMISES ON THE MESSAGES'
SHAPES THAT THE CONDITION IN FRONT OF A CODE SWITCH TAKES AT TWO BORDERS, EACH FROM OTHER
FILES' CONCLUSIONS AT THAT BORDER's STATE, in their own letters. A law file; no running text
imports it.

t: the verifier's state at a border. MW: the listed shapes of the first chain's oracle messages, at
the written sendings (FrontsFull.lean).

  mw_of_sends      the planner's sendings are the written ones: so their listed shapes are MW.
  shapes_of_test   e: K12.Door.atFirstShapes M t = true and M = MW give, at every number below the
                   count of t's messages: the message's shape is MW's. (By
                   msgShape_at, Johnson/Desc/K12/Door/MsgShapes.lean.)
  olds_of_test     e0: AT THE BORDER IN FRONT OF LINK l's CLOSING (the cut 14 l + 12, l < 24): the
                   same test's yes, «the chain's blocks have the written cut», and «t holds just
                   what the blocks in front tell» give the equation at every kept old message of
                   the switch into group l + 1. (By ToldAtClosing.lean's olds_below_closing.)
WHO HAS THE PREMISES: the test's yes at a border: shapes_start (under its
SendDebts, ShapeDebts and the test sendsAreB) · the written sendings: MadeInScope.lean's
sends_in_scope (under the verifier's test on the plan) · the written cut: cut_of_row (from its
row's accept) · the count: counts_at_cut_paid (under the blocks' tests on
the plan), whose sum is toldBefore by rfl.
Limits. Nothing is paid here but the closed fact beneath (by the kernel, in ToldAtClosing.lean). The
full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.ToldAtClosing
import Johnson.Top.H0.K2Hands.FrontsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutFirstFull toldBefore)
open VerifiableInference.Desc.First.K2 (oldsAt)
open Johnson.G (proofSendsFull)

theorem mw_of_sends {x : Johnson.G.ChainSends × Johnson.G.ChainSends × Johnson.G.ChainSends}
    (h : x = proofSendsFull) : K12.Door.msgsOfChain x.1 = MW := by
  rw [h]
  rfl

/-- e: at every number below the count. -/
theorem shapes_of_test {M : List OracleShape} {t : S} (h : K12.Door.atFirstShapes M t = true)
    (hM : M = MW) :
    ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]? := by
  subst hM
  exact fun o ho => K12.Door.msgShape_at h o ho

/-- e0: at the kept old messages, in front of the closing. -/
theorem olds_of_test {T Cl : Type} {bs : List (Block T Cl)} {M : List OracleShape} {t : S} {l : ℕ}
    (hl : l < 24) (hc : PlanWritten.cutOf bs = cutFirstFull)
    (hn : t.st.oracles.size = toldBefore bs (14 * l + 12))
    (h : K12.Door.atFirstShapes M t = true) (hM : M = MW) :
    ∀ o ∈ oldsAt (l + 1), (t.st.oracles[o]?).map (·.shape) = MW[o]? := fun o ho =>
  shapes_of_test h hM o (by rw [hn]; exact olds_below_closing hc hl o ho)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.olds_of_test
#print axioms VerifiableInference.Desc.First.K2Hands.shapes_of_test
