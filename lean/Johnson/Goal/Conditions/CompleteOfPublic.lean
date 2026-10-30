-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/CompleteOfPublic.lean: CompleteOn (VerifiableInference/Steps.lean) FROM THE
LAW OF A TYPED EXPERIMENT BEHIND PUBLIC READINGS AND ONE POINTWISE HYPOTHESIS: a frame, general in
the argument system: every piece with content is a premise that is named.

In words. Fix the honest side's two drawn numbers (t, a). Let Pub be the public readings off the
hash function, with value d; Y d a typed program without coins (the honest committer's and provers'
runs at d's letters), Ev d an event on its outcome. IF (law) under uniform typed oracles Y d's
outcome lies in Ev d with probability at most α, at every d; (apart) Y d, coded over the one hash
function by m d, asks no string that Pub may ask; (home_yes) AT EVERY HASH FUNCTION: where Y d's
outcome, under the typed oracles that are read out of the hash function through m d, d Pub's value,
lies outside Ev d, the verifier says yes to the honest commitment and proof: THEN CompleteOn at α.

One theorem: completeOn_of_public. It stood in Johnson/Goal/Conditions/WiderComplete.lean; it needs
nothing of theWider, so it has a file of its own: what calls it then stands on far fewer files.

This file states no goal. A theorem about the goals' own definition, at letters. Calls:
completeOn_of_programs (Johnson/Goal/Conditions/CompleteOfCoins.lean); pub_overOne_le,
det_pub_overOne (Johnson/Prover/All/PublicOne.lean); noCoin_overOne (Rom/NoCoinExits.lean).

Limits. home_yes, law AND apart ARE PREMISES: nothing here pays them. α is a letter: at α = 1 the
statement says nothing. The sampler draws one number and asks the hash function nothing; the prover
draws one number and has no coins from there on: premises. No budget on the honest side's queries.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.CompleteOfCoins
import Johnson.Prover.All.PublicOne
import Rom.NoCoinExits

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference
open Rom

/-- **The frame, general in the argument system.** -/
theorem completeOn_of_public (system : ArgumentSystem)
    (domain : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞) {B N : ℕ}
    (ρOf : Fin (B + 1) → system.CommitmentRandomness)
    (hs : system.sampleCommitmentRandomness = .sample B fun t => .done (ρOf t))
    (pd : system.Weights → system.CommitmentRandomness → List Token → List Token → Fin (N + 1) →
      DeterministicAlgorithm system.Proof)
    (hp : ∀ w ρ p o, system.prove w ρ p o = .sample N fun a => (pd w ρ p o a).toRandomized)
    {S : OSpec} {γ D : Type} (Pub : OComp (rom 256) D) (m : D → OracleCoding S 256)
    (Y : system.Weights → List Token → List Token → Fin (B + 1) → Fin (N + 1) → D → OComp S γ)
    (Ev : system.Weights → List Token → List Token → Fin (B + 1) → Fin (N + 1) → D → Set γ)
    (Pt : List Bool → Prop) (hPub : Pub.NoCoin) (hP : Pub.AsksIn fun _ s => Pt s)
    (hYc : ∀ w p o t a d, (Y w p o t a d).NoCoin)
    (apart : ∀ w p o t a d, ((Y w p o t a d).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (law : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a d,
      Rom.Pr (Y w p o t a d) (fun _ => Ev w p o t a d) ≤ α)
    (home_yes : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a (hash : Hash),
      (Y w p o t a (Pub.det (famOf hash))).det
          (readBlocks (m (Pub.det (famOf hash))) (famOf hash)) ∉
        Ev w p o t a (Pub.det (famOf hash)) →
      (system.verify ((system.commit w (ρOf t)).evaluate hash) p o
        ((pd w (ρOf t) p o a).evaluate hash)).evaluate hash = true) :
    CompleteOn system domain α :=
  completeOn_of_programs system domain α ρOf hs pd hp
    (fun w p o t a => Pub.bind fun d => ((Y w p o t a d).overOne (m d)).bind fun y => .pure (d, y))
    (fun w p o t a => {z | z.2 ∈ Ev w p o t a z.1})
    (fun w p o t a => OComp.NoCoin.bind hPub fun d =>
      OComp.NoCoin.bind (noCoin_overOne (m d) _ (hYc w p o t a d)) fun _ => trivial)
    (fun w p o hd hm t a hash hno => by
      rw [OnBytes.Prover.det_pub_overOne]
      by_contra hn
      rw [home_yes w p o hd hm t a hash hn] at hno
      cases hno)
    (fun w p o hd hm t a =>
      OnBytes.Prover.pub_overOne_le Pub m (Y w p o t a) Pt hP (apart w p o t a) (Ev w p o t a)
        (law w p o hd hm t a))

end VerifiableInference

#print axioms VerifiableInference.completeOn_of_public
