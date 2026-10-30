-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkAccept.lean: if the input satisfies Meant and the symbols of its two oracles
carry their positions, the link's interactive verifier accepts the run of the explicit honest link
prover at all challenges that pass the proof-of-work checks (link_accLaw; at the library's full-size
parameter set).
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

What this file has. link_accLaw. Take any instance rr, any pair of input oracles y and any row
polynomials M₀, M₁ of the two tables that satisfy Meant (LinkYesStm.lean), and suppose that every
symbol of the two oracles carries its position. Then, for every value C of the prover's free
parameters (LCoins, Johnson/Prover/Link/LinkAll.lean) and all K and chal (the two parameters of the
compilation data wqW), AccLaw holds of the strategy stratOf at linkNext, with the set B empty.
AccLaw (Johnson/Prover/Law/Defs.lean) says here: at every transcript that is the strategy's own run
but for nonces, with all proof-of-work checks passed, the whole accept is true. No further challenge
is excepted and there is no error term.

How it fits. link_yes (Johnson/Prover/Link/LinkJoinF.lean) speaks of the decision alone (common
limit 1). This file adds the other three conditions of the accept. The first is AccLaw's own
premise. The second is a fact on the parameters alone (full_full). The third follows from the new
premise and a fact on the parameters alone (fr_opens). The fourth is link_yes. So the proof is one
application of accLaw_link.
Both premises are proved together by accept_met_home (Johnson/Goal/Conditions/LinkAcceptMet.lean).
It does so for all public files Z, every index, all values of the encoding randomness (the encoder's
second argument; a free variable here) and of the seeds, at that index's encodings and OOD samples
in homeR b Z and at the honest row polynomials. link_accLaw_home
(Johnson/Goal/Conditions/LinkAcceptHome.lean) joins the two. AccLaw at this protocol is not vacuous:
accLaw_link_meets (Johnson/Prover/Link/LinkPasses.lean) gives a transcript with AccLaw's three
properties (LinkFrame.lean).

Lemmas used: accLaw_link at carriesX_of (both in Johnson/Prover/Link/LinkFrame.lean), fr_opens
(Johnson/Prover/Link/ChainAtFull.lean), full_full (Johnson/Goal/Conditions/LinkFitsPaid.lean) and
link_yes.
What it uses of the folder Johnson/Goal/: FlashProve.full_full alone (a fact on the parameters
alone: the openings' counts at the full-size parameter set, at every challenge). Nothing else of
that folder is called.

Limits. 1. link_accLaw is conditional on the proof-of-work checks. The strategy sends the nonce 0;
no search for a nonce is here. The proviso is AccLaw's own form: the accept's first condition
(passSL) reads the challenges alone: where these do not pass it is false whatever is sent (by
inspection, not proved). HonFit's fields accT, accL and accB (Johnson/Prover/All/OfHonest.lean) have
the same form. The search is the compiled prover's. The probability that it fails is bounded, at the
empty excepted set and from a random-oracle table that has no entry yet at this run's Fiat-Shamir
queries (FreshFrom, Johnson/Prover/Law/Defs.lean; not a committed table), by the term capFail
(prove_law, Johnson/Prover/Law/Chain.lean, under its other conditions). capFail sums
(1 - 2^-b)^(cap + 1) over the rounds with a check; the bounds cap on attempts are parameters. That
term at the link is a summand of alphaAll (Johnson/Prover/All/Law.lean), and the clause "number" of
LastFits asks alphaAll ≤ α (Johnson/Goal/Conditions/HomeLast.lean).
2. The premise on the positions asks all symbols of both oracles, read or not.
3. The verifier is the protocol of LinkFrame.lean at this decision. That it is the link of homeR b Z
is not said here (see linkFits_at, Johnson/Goal/Conditions/LinkFitsAt.lean), nor that it is what
verify() runs (the compiled verifier: HomeLast.lean).
4. The common limits 3 and 4 apply; and this is the honest prover of one of the three protocols.
No finite type of coins and no distribution occur in this file. Nothing on soundness or any other
property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkJoinF
import Johnson.Goal.Conditions.LinkFitsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb _root_.Run
open _root_.Iop (twoExternalStrings)
open _root_.Run.PQ (SgX)
open _root_.Desc.K15 (frP linkDescriptionAt linkDeclaredRounds linkRoundsMatchPlan)
open OnBytes.Flat (dsFull RecFull linkSkeletonOfRoundData)
open OnBytes.Prover (AccLaw)
open Johnson.RunOne.StrictW (wqW)

/-- **The link's interactive verifier accepts the explicit honest prover's run, at all challenges
that pass the proof-of-work checks**: AccLaw with the set B empty, for every input that satisfies
Meant and whose oracles' symbols carry their positions (hy), and for every C. At the full-size
parameter set. -/
theorem link_accLaw (K : ℕ) (chal : ∀ e k, (Fin K → _root_.Iop.Dig 256) → (ckP .two).Ch e k)
    (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE) (hM : Meant rr y M₀ M₁)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
      ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).1 = x)
    (C : LCoins) :
    AccLaw
      (linkSkeletonOfRoundData (ckP .two) dsFull frS.P.T.a frD.xs
        fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
          (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V).up
      (wqW (ckP .two) dsFull frS.P.T.a frD.xs
        (fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
          (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V) K chal)
      rr y (stratOf (ckP .two) dsFull (linkNext frP frS 97 (linOf rr y M₀ M₁) C)) ∅ :=
  accLaw_link (ckP .two) dsFull frS.P.T.a frD.xs
    (fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
      (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V) K chal
    (linkNext frP frS 97 (linOf rr y M₀ M₁) C) rr y (fun ρ => FlashProve.full_full ρ)
    (fun ρ => carriesX_of dsFull frS.P.T.a frD.xs _ y fr_opens hy)
    (fun ρ _ => link_yes rr y M₀ M₁ hM C ρ)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.link_accLaw
