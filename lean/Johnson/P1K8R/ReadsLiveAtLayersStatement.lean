-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLiveAtLayersStatement.lean: AT A STATE REACHED IN FRONT OF THE BATCHING OF A
FEED-FORWARD LAYERS' SEGMENT (member 28 g + 9 of the first chain's flat list) THE TEST `readsLive`
(Johnson/Desc/K8/Honest/LinkedFew.lean) SAYS YES, WHERE NO COORDINATE OF THE POINT THAT THE LOOKUP
ON THE SEGMENT's CALLS LEFT READS 0 OR 1. In the goals' scope, at an opening's letters. STATEMENTS
ALONE: one definition of a premise's form and one of a proposition. NOTHING IS PROVED IN THIS FILE,
and it is none of the library's goals: a lemma's statement.

WHAT IT IS NOT. CONDITIONAL, TWICE: ON "REACHED": nothing says that any state is reached; AND ON
`OwnFine`, WHICH IS SHOWN OF NO STATE HERE: it fails at some draws of the lookup's rounds, and how
many is counted nowhere here. hOk, that the description passes its test on the plan, is a premise
too. The layers' segments alone. No draw of the segment's own rounds is spoken of. At the format's
second hash function alone (OnBytes.secondHashFunction). The full size alone.

  `OwnFine s`           THIS FILE's OWN, A PREMISE's FORM: whatever the state holds as the return o
                        of the segment's own rounds: no coordinate of o.H.fo.zx, the point that the
                        lookup on the calls left as these rounds took it, reads 0 or 1
  `ReadsLiveAtLayers`   the title

NEAR. `ReadsLiveAlongFold` (ReadsLiveAlongFoldStatement.lean of this folder): the like at the output
head, along the caller's own fold. `wins_reached` (Johnson/Road/K4/InT/WinsReached.lean): at 28 g +
8 what `S.lookHeard?` answers is o.H.fo. `runAsks_at_batch`
(Johnson/Desc/ProofFile/Honest/K4/Law/RunsAtBatch.lean), `ground_of_hear`, `kept_ground`
(Johnson/Road/K4/W/, a folder that is not in this library), another group of authors': what the
state holds at that border is a return of the own rounds' text; the points, the laying and the list
at such a return; `zt_of_hear` (Johnson/Desc/ProofFile/Honest/K4/Law/W/OneTie.lean, not in this
library), theirs too: the token point at such a return.

Limits. A yes of a test with code, under premises. Nothing on any property.
-/
import Johnson.IMR.SeatOpen
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.K8.Honest.LinkedFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest (readsLive)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- THIS FILE's OWN, A PREMISE's FORM: the lookup's point, as the own rounds took it, has no
coordinate that reads 0 or 1. -/
def OwnFine (s : S) : Prop :=
  ∀ o, s.own? = some o → ∀ w ∈ o.H.fo.zx.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def ReadsLiveAtLayers : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B → F.planOk = true →
    ∀ (g : Nat), g < 12 → ∀ (z : ProofFile.InstPub) (s' : S),
      Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s') → OwnFine s' →
      ∃ tl, s'.tl? = some tl ∧ readsLive tl = true

end P1K8

#print axioms P1K8.OwnFine
#print axioms P1K8.ReadsLiveAtLayers
