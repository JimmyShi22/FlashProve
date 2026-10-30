-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/OneSentenceLeft.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: AT EVERY
STATE THAT THE FIRST CHAIN's BLOCKS, EACH WITH THE TEST ON WORDS IN FRONT (`Sound.below`), REACH IN
FRONT OF THE BATCHING OF ONE OF THE 24 SEGMENTS IN FRONT OF THE HEAD's, IN THE GOALS' SCOPE:
`AllFront` (Johnson/Desc/K8/Honest/LeftAtLink.lean) FOLLOWS FROM ONE SENTENCE: THE DIGITS' ARRAY HAS
THE NAME "ZZ". Three joinings; none of the library's goals.

  **`allFront_at_wrap`** what the lookup heard is there; and the name at the state's ledger ⊢ there
                   are nbW, Wn with AllFront tl G g nbW Wn
  `pointsHeld_at_wrap` the verifier's own test pointsHeld says yes there, with no premise on words
  **`heard_at_wrap`** at every piece that the second computation expects: the point of the piece's
                   call has the call's number of coordinates, and the call's weight is the second
                   computation's: with no premise on words
By: `zy0_below_at_wrap` (Johnson/Desc/K8/Honest/ZyBelowAtWrap.lean) · `allFront_of_two`,
`heldPub_at_batch` (HeldInScope.lean) · `pointsHeld_at_batch` (PointsAtReach.lean) · `heard_at_z`
(HeardJoin.lean) · the library's `reach_raw` (Johnson/Top/H0/Walk/Reach.lean).
Limits. AN IMPLICATION STILL in the first: THE NAME IS PAID BY NOBODY HERE: it is shown at the built
segment's planned ledger alone. AT THE WRAPPED FAMILY ALONE. NOTHING AT THE HEAD's SEGMENT. IN SCOPE
ALONE: the full size; under an opening of the description and its test on its plan; the first chain.
Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ZyBelowAtWrap
import Johnson.Desc.K8.Honest.HeardJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`AllFront` FROM ONE SENTENCE.** -/
theorem allFront_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∃ g, tl.heard = some g ∧ ((G.trees.getD tl.ix.ZZ {}).name = "ZZ" →
      ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn) := by
  obtain ⟨g, hg, k⟩ := allFront_of_two hS hR O hOk hl e3 (reach_raw h) ht hG
  exact ⟨g, hg, k (zy0_below_at_wrap hS hR O hOk hl h ht hg 0)⟩

/-- **The verifier's test `pointsHeld`, with no premise on words.** -/
theorem pointsHeld_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : ∃ g, tl.heard = some g ∧ tl.pointsHeld g = true := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact reach_raw h
  obtain ⟨g, hg, k⟩ := pointsHeld_at_batch hS hR O hOk hl e3 (reach_raw h) ht
    (heldPub_at_batch hS hR O hOk (by omega) e3 h' ht)
  exact ⟨g, hg, k (zy0_below_at_wrap hS hR O hOk hl h ht hg 0)⟩

/-- **At every expected piece: the size of its call's point, and its call's weight: no premise on
words.** -/
theorem heard_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∀ tl, s.tl? = some tl → ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W,
      (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
        g.e.getD w.call zeroE = callWeightAgain g w.call :=
  fun _ ht g nbW W hg hW => heard_at_z hS hR O hOk hl e3 (reach_raw h) ht g nbW W hg hW
    (zy0_below_at_wrap hS hR O hOk hl h ht hg 0)

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.pointsHeld_at_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.heard_at_wrap
