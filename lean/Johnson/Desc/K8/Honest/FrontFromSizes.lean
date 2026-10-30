-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FrontFromSizes.lean: THE SMALLNESS TEST: `AllFront`
(Johnson/Desc/K8/Honest/LeftAtLink.lean) AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN
FRONT OF THE BATCHING OF ONE OF THE 24 SEGMENTS IN FRONT OF THE HEAD's, IN THE GOALS' SCOPE, FROM:
ONE PUBLIC TEST WITH CODE AT THE BUILT SEGMENT's DATA · SEVEN SIZES OF WHAT THE DIGITS' LOOKUP HAS
HEARD · ONE OF THE VERIFIER's OWN TESTS IN FRONT (pointsHeld) · THE NAME OF THE DIGITS' ARRAY. An
assembly; none of the library's goals.

  `FrontLeftHeard tl F g` WHAT IS LEFT AT THE STATE: the two points zb0 and zb1 have 5 + (kT + cK)
                   coordinates each · HeardSizes tl g (five: Johnson/Desc/K8/Honest/HeldPublic.lean)
                   · pointsHeld · the digits' array has the name "ZZ"
  `six_of_heard` at a reached state, all 25 segments: the public test at the built segment's data ·
                   FrontLeftHeard tl G g ⊢ FrontLeftSix tl G g
                   (Johnson/Desc/K8/Honest/FrontSharper.lean)
  **`allFront_of_heard`** at the 24: what the lookup heard is there; and the public test ·
                   FrontLeftHeard tl G g at it ⊢ there are nbW, Wn with AllFront tl G g nbW Wn
By: `held_at_batch` (HeldPublic.lean) · `allFront_of_six` (FrontSharper.lean).
Limits. AN IMPLICATION: THE PUBLIC TEST IS A PREMISE HERE; IN SCOPE, UNDER AN OPENING OF THE
DESCRIPTION AND ITS TEST ON ITS PLAN, IT SAYS YES AT EACH OF THE 25 BUILT SEGMENTS' DATA
(`heldPub_at_built`, Johnson/Desc/K8/Honest/HeldOutright.lean); `FrontLeftHeard` IS A PREMISE HERE
(its seven sizes are shown in Johnson/Desc/K8/Honest/HeardAtReach.lean). At the head's segment
nothing is said in the last. IN SCOPE ALONE: the full size's segments; under an opening of the
description and its test on its plan; the first chain; the family of states from the description's
own first state. Nothing says that any
state is reached. No prover stands in it. Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.FrontSharper
import Johnson.Desc.K8.Honest.HeldPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What is left at the state. -/
structure FrontLeftHeard (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Prop where
  zb0 : g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK)
  zb1 : g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK)
  sizes : HeardSizes tl g
  points : tl.pointsHeld g = true
  name : (F.trees.getD tl.ix.ZZ {}).name = "ZZ"

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At a reached state: the six from the public test and what is left. -/
theorem six_of_heard (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hP : heldPubB Xl.tl = true)
    {g : Forest.Heard} (L : FrontLeftHeard tl G g) : FrontLeftSix tl G g :=
  ⟨L.zb0, L.zb1, L.name, (held_at_batch hS hR O hl e3 h ht hP L.sizes).1,
    (held_at_batch hS hR O hl e3 h ht hP L.sizes).2, L.points⟩

/-- **AT THE 24 SEGMENTS IN FRONT OF THE HEAD's.** -/
theorem allFront_of_heard (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (hP : heldPubB Xl.tl = true) :
    ∃ g, tl.heard = some g ∧ (FrontLeftHeard tl G g →
      ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn) := by
  obtain ⟨g, hg, k⟩ := allFront_of_six hS hR O hOk hl e3 h ht hG
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact h
  exact ⟨g, hg, fun L => k (six_of_heard hS hR O (by omega) e3 h' ht hP L)⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.six_of_heard
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_heard
