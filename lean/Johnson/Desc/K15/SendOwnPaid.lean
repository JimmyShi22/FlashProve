-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/SendOwnPaid.lean: the one named premise of Johnson/Desc/K15/SendOwnLaw.lean
(SendPOfDecide) PAID BY IMPORT: the kind K1's files' own theorem sendP_of_decide
(Johnson/Desc/K1/Law/SendP3.lean, at its own path and bytes): where
K1's own block at a sending says yes, the plain ground's sending says yes at the same record. So:
WHERE THE SEATED LINK (the kind K1's own block at the sending) SAYS YES, THE TEXT THAT THE LAWS
SPEAK OF SAYS YES, AT THE SAME RECORD: without a premise.
  sendPOfDecide                     the premise, as a theorem: three lines
  descV_yes | descV_end | linkDescV_yes   the tie, closed
ONE WAY ALONE. It rests on SendP1 | SendP2 | SendP3 (Johnson/Desc/K1/Law/), over the
same plain ground as Johnson/Desc/K15/SendOwnLaw.lean reads. Nothing on soundness by itself,
on an honest prover or on hiding.
-/
import Johnson.Desc.K15.SendOwnLaw
import Johnson.Desc.K1.Law.SendP3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (OneChainFileDescription)

theorem sendPOfDecide : SendPOfDecide :=
  fun _ P owed d d' r₁ r₂ ids hB hl hfit hyes =>
    ⟨_, _, _, VerifiableInference.Desc.K1.sendP_of_decide P owed d d' r₁ r₂ ids hB hl hfit hyes⟩

/-- **The tie, closed**: at any parameters, plan and public test. -/
theorem descV_yes (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (x : TableKey × TableKey)
    (v : Fmt.View)
    (h : (linkDescriptionAt P plan ok).run x v = true) : (descOf P plan ok).run x v = true :=
  descV_run sendPOfDecide P plan ok x v h

theorem descV_end (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (x : TableKey × TableKey)
    (v : Fmt.View) (e : St)
    (h : (linkDescriptionAt P plan ok).runEnd x v = .ok e) : (descOf P plan ok).runEnd x v = .ok e :=
  descV_runEnd sendPOfDecide P plan ok x v e h

/-- **At the link's description.** -/
theorem linkDescV_yes (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (x : TableKey × TableKey) (v : Fmt.View)
    (h : (linkDescV c plan).run x v = true) : (linkDesc c plan).run x v = true :=
  linkDescV_run sendPOfDecide c plan x v h

end Desc.K15

#print axioms Desc.K15.sendPOfDecide
#print axioms Desc.K15.descV_yes
#print axioms Desc.K15.descV_end
#print axioms Desc.K15.linkDescV_yes
