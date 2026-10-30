-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkJoinF.lean: the link verifier's decision accepts the view of the explicit
honest link prover, for every input that satisfies Meant, at the library's full-size parameter set
(link_yes).
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

What this file has. link_yes proves LinkYes 97 (LinkYesStm.lean). Take any instance rr, any pair of
input oracles y and any row polynomials M₀, M₁ of the two tables that satisfy Meant. Then, for every
value C of the prover's free parameters (LCoins) and all verifier challenges ρ, the link's decision
(one of four conditions of the accept: common limit 1) accepts the view of the explicit honest
prover (linkNext, Johnson/Prover/Link/LinkAll.lean). No challenge is excepted and there is no error
term. The theorem holds at every C: nothing is assumed on how C is chosen.
The decision is the one that the protocol description generates, at the two table keys made of rr.
The view is viewOf (Johnson/Prover/Link/LinkFrame.lean): the decision's input, not the library's
disclosed view. What the number 97 is: LinkYesStm.lean.

How it fits. linkYes_of (Johnson/Prover/Link/LinkJoinE.lean) derives LinkYes 97 from three
propositions, which that file states. This file proves each by one call (inv0_full, front0_meets,
groups_meets: see their docstrings) and applies linkYes_of.
  Inv0    the proximity test's front and its batching accept, the batched group fits the first
          stage, the state lT that the prover computes is the verifier's state after them, and the
          invariant of the induction over the stages holds before the first stage, if the six
          sub-protocols before the test accept, the batched claim is true, and five further premises
          hold (two on the keys, three on the verifier's state and its group).
  Front0  the batched claim is true, under Meant, the same acceptance and the same three premises.
  Groups  the prover's algorithm and the verifier list the same groups of columns for the stages.
link_yes is used by link_accLaw (Johnson/Prover/Link/LinkAccept.lean), which adds the other three
conditions of the verifier's accept, and by linkFits_at (Johnson/Goal/Conditions/LinkFitsAt.lean).
Each has its own conditions.

Limits. The common limits 1 to 4 apply. By limit 1 the whole accept is not proved in this file. At
the challenges that pass all proof-of-work checks it is the subject of link_accLaw and of
linkFits_at's field accL, each under its own further conditions, and of link_accLaw_home
(Johnson/Goal/Conditions/LinkAcceptHome.lean), which has no further condition.
That Meant holds of any input is not proved in this file: it is link_yes' one premise. The seven
clauses of Meant are proved by meant_home (Johnson/Goal/Conditions/LinkMeant.lean) at the two
encodings and OOD samples of any one index in homeR b Z, and at the honest row polynomials.
Nothing is proved here at the small parameter set (dsSmall, OnBytes/Flat/LinkSibAt.lean).
C is not tied here to a finite type of coins: no such type is defined in this file or in a file that
it imports. A finite type with a map into LCoins: Kc, coinsFull (Johnson/Prover/Link/LinkCoin.lean).
Nothing on soundness. No distribution is put on the prover's free parameters or on the challenges.
Nothing on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkJoinE
import Johnson.Prover.Link.BodyInv0Meant
import Johnson.Prover.Link.GroupsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link

/-- Inv0 (Johnson/Prover/Link/LinkJoinE.lean), by bodyInv0_full
(Johnson/Prover/Link/BodyInv0Full.lean), which has the same statement. -/
theorem inv0_full : Inv0 := fun X C ρ hi0 hi1 d' G' h6 hS ho hn HF =>
  Full.bodyInv0_full X C ρ hi0 hi1 d' G' h6 hS ho hn HF

/-- Front0 (Johnson/Prover/Link/LinkJoinE.lean), by front0_full
(Johnson/Prover/Link/BodyInv0Meant.lean). -/
theorem front0_meets : Front0 := fun rr y M₀ M₁ hM C ρ d' G' h6 hS ho hn row hrow =>
  Full.front0_full rr y M₀ M₁ hM C ρ d' G' h6 hS ho hn row hrow

/-- Groups (Johnson/Prover/Link/LinkJoinE.lean), by groups_full
(Johnson/Prover/Link/GroupsFull.lean) at the plan's list of stages. -/
theorem groups_meets : Groups := fun X C y ρ =>
  groups_full 97 X C y ρ Full.curF _ Full.stages_two_full

/-- **The main theorem: the link's decision accepts the explicit honest prover's view, at the
full-size parameter set**, for every input that satisfies Meant, every C and all verifier
challenges. The decision is one of four conditions of the verifier's accept (LinkYesStm.lean, common
limit 1): by itself this does not say that the verifier accepts. -/
theorem link_yes : LinkYes 97 := linkYes_of inv0_full front0_meets groups_meets

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.inv0_full
#print axioms Johnson.Prover.Link.front0_meets
#print axioms Johnson.Prover.Link.groups_meets
#print axioms Johnson.Prover.Link.link_yes
