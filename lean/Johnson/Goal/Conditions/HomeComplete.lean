-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeComplete.lean: A LEMMA AT LETTERS ON "THE HONEST SIDE IS ACCEPTED": for
every argument system and every told record: HomeFits (Johnson/Prover/Home/Letters.lean) gives
CompleteOn (VerifiableInference/Steps.lean) at the number α; and with JoinFits in the place of its
field "yes".

How. completeOn_of_public (Johnson/Goal/Conditions/CompleteOfPublic.lean): the experiment is a mean
over the sampler's and the prover's draws; at fixed draws it has no coins; where the verifier says
no, what the typed runs yield lies in the event (HomeYes); that event's measure over the hash
function is its measure over uniform typed oracles at each fixed reading (pub_overOne_le,
Johnson/Prover/All/PublicOne.lean: the honest side asks no public string: no_allY,
Johnson/Prover/All/NoOther.lean), which allY_law (Johnson/Prover/All/Law.lean) bounds.

Main names.
  completeOn_home       from HomeFits.
  completeOn_home_join  from the measure's premises and JoinFits.

Not said here. α is a letter until the sets' measures are bounded. The strategies are letters: no
strategy is written here. The accept laws are premises. What is public on the files is a premise.
The prover encodes one copy of the committed table for each request. No clause says that the copy's
encoding randomness differs from the first table's or from another copy's; at the idle parameters it
is the first table's (HomeIdle.lean).
Nothing at an argument system that does not meet HomeFits;
THE ONE MEMBER OF HomeFits THAT IS SHOWN IN THIS LIBRARY IS IDLE, WITHOUT TEETH: idle letters at the
goals' input meet completeOn_home_join's premises, of which its proof makes HomeFits, at a number
that is at least 3, where the statement bounds nothing (lastFits_idle,
Johnson/Goal/Conditions/HomeIdle.lean, under its three clauses on the files (paid at the two named
sets' written copies: lastFits_idle_named, AtFullSide/Home/HomeAtNamed.lean), through
endFits_of_last, completeOn_end_of and completeOn_member_of); no theorem states it by that name. (A
toy's, in a file that is not in this repository: Johnson/Goal/Conditions/HomeToy.lean [not in this
library].) At no intended file is an honest strategy or an honest side written that meets it.
HomeFits' field "yes" is the pointwise join whole, and JoinFits' field "printed" ends in the
verifier's yes: what is public on the files, the request, what a printer asks of the strategies, and
the run values live BEHIND that field and are named by no field of their own. No budget: nothing on
the number of the honest side's queries. This file states no goal. A theorem about the goals' own
definition, at letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.CompleteOfPublic
import Johnson.Prover.Home.Yes

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {system : ArgumentSystem} {R : InnerCompilerInput} {T : LayoutsByPublicReading R} (H : HomeLetters system T)

/-- **The honest side is accepted, at letters.** -/
theorem completeOn_home (domain : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞)
    (F : HomeFits H domain α) : CompleteOn system domain α :=
  completeOn_of_public system domain α H.ρOf F.sample H.pd F.prove T.Pub T.m
    (fun w p o t a d => runsAt T H.b₀ H.st H.capT H.capL H.capB d (H.isk w (H.ρOf t) d) (H.xOf p o)
      (H.drawOf d (H.ρOf t) a))
    (fun w p o t a d => EvY (H.Bs w p o t a d)) T.Pt F.pubNoCoin F.pubAsks
    (fun _ _ _ _ _ _ => noCoin_allY _ _ _ _ _ _ _ _ _ _ _ _)
    (fun _ _ _ _ _ d => (asksIn_overOne (T.m d) (NotOther 256 _) _
      (no_allY _ _ _ _ _ _ _ _ _ _ _ _)).mono fun _ s hn hp => hn (F.spare d s hp))
    (fun w p o hd hm t a d => (allY_law _ _ _ _ _ _ _ (freshAll_empty R.queryLayout (T.Sd d)) (F.law d) _ _ _
      (H.Bs w p o t a d) (F.small w p o hd hm t a d)).trans F.number)
    fun w p o hd hm t a hash hn => F.yes w p o hd hm t a hash hn

/-- The same, the join paid by JoinFits: the measure's eight premises, one by one, and JoinFits. -/
theorem completeOn_home_join (domain : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞)
    (sample : system.sampleCommitmentRandomness = .sample H.B fun t => .done (H.ρOf t))
    (prove : ∀ w ρ p o, system.prove w ρ p o = .sample H.N fun a => (H.pd w ρ p o a).toRandomized)
    (law : ∀ d, LawFit R.queryLayout (T.Sd d) H.capT H.capL H.capB) (pubNoCoin : T.Pub.NoCoin)
    (pubAsks : T.Pub.AsksIn fun _ s => T.Pt s) (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (small : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a d,
      SetsSmall R.queryLayout (T.Sd d) (H.Bs w p o t a d) H.ζ₁ H.ζ₂ H.δT H.δL H.δB)
    (number : alphaAll R.queryLayout H.capT H.capL H.capB H.ζ₁ H.ζ₂ H.δT H.δL H.δB ≤ α)
    (J : JoinFits H domain) : CompleteOn system domain α :=
  completeOn_home H domain α
    ⟨sample, prove, law, pubNoCoin, pubAsks, spare, small, number, home_yes H domain J⟩

end OnBytes.Prover
