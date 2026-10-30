-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/HeardJoin.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF THE BATCHING OF ONE OF THE 24 SEGMENTS IN FRONT OF THE HEAD's, IN THE
GOALS' SCOPE: AT EVERY PIECE THAT THE SECOND COMPUTATION EXPECTS, THE POINT OF THE PIECE's CALL HAS
THE CALL's NUMBER OF COORDINATES AND THE CALL's WEIGHT IS THE SECOND COMPUTATION's, WHERE THE WORDS
OF ONE COORDINATE OF THE LOOKUP's KEY POINT LIE BELOW THE PRIME. The two fields on what the lookup
has heard of `PieceFront` (Johnson/Desc/K8/Honest/PieceWhole.lean). One joining; none of the
library's goals.

  **`heard_at_z`** the scope · the files read · an opening of the description · its test on its plan
                   · l < 24 · the built segment · a reached state that shows tl ⊢ for all g, nbW, W
                   with tl.heard = some g and tl.wants = some (nbW, W), where zy_0's words lie below
                   the prime: for every w in W: (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n
                   and g.e.getD w.call zeroE = callWeightAgain g w.call
By: `heardSizes_at_batch` (Johnson/Desc/K8/Honest/HeardAtReach.lean) · `weights_of_below`
(WeightsAtReach.lean) · `heldPub_at_batch` (HeldInScope.lean) · `left_at_batch` (LeftAtReach.lean) ·
`wants_128` (Johnson/P1K8R/WantAtBatch.lean: at 128 combinations two pieces are expected, one a
call) · `drawn_at_batch` (DrawAtBatch.lean).
Limits. THE SENTENCE ON zy_0's WORDS IS A PREMISE HERE: at the family of states that the bare blocks
reach, of which this file speaks, it can fail (Johnson/Desc/K8/Honest/WeightsAtReach.lean says why);
at the family that the blocks with the test on words in front reach it is paid
(Johnson/Desc/K8/Honest/ZyBelowAtWrap.lean; the join: OneSentenceLeft.lean). NOTHING AT THE HEAD's
SEGMENT. IN SCOPE ALONE: under an opening of the description and its test on its plan; the first
chain; the family of states from the description's own first state. Nothing says that any state is
reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.HeldInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY EXPECTED PIECE: the size of its call's point, and its call's weight.** -/
theorem heard_at_z (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    (ht : s.tl? = some tl) :
    ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) →
      OnBytes.okE (g.zy.getD 0 zeroE) = true → ∀ w ∈ W,
        (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
          g.e.getD w.call zeroE = callWeightAgain g w.call := by
  intro g nbW W hg hW hz w hw
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact h
  have hP := heldPub_at_batch hS hR O hOk (by omega) e3 h' ht
  obtain ⟨v, g₀, F₀, F', rs, hg₀, K⟩ := left_at_batch hS hR O hOk hl e3 h ht
  obtain rfl : g₀ = g := Option.some.inj (hg₀.symm.trans hg)
  have hP' : heldPubB tl = true := by
    rw [pub_heldFields tl, v, ← pub_heldFields Xl.tl]
    exact hP
  have nc : tl.f9.NC = 2 := by
    rw [show tl.f9 = Xl.tl.f9 from congrArg (·.f9) v]
    exact (two_calls_of_tests (_root_.P1K8.tests_at_built hS O (by omega : l < 25) e3)).1
  obtain ⟨g₁, hg₁, ⟨-, -, -, k0, k1⟩, -, -⟩ := heardSizes_at_batch hS hR O hOk hl e3 h ht hP
  obtain rfl : g₁ = g₀ := Option.some.inj (hg₁.symm.trans hg)
  have he := weights_of_below K hP' nc hz
  obtain ⟨t, a, -, hT⟩ := _root_.P1K8.drawn_at_batch hS hR O (by omega : l < 25) h'
  rw [Option.some.inj (a.symm.trans ht)] at hT
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ((_root_.P1K8.wants_128 hT).symm.trans hW))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨k0, he 0 (by omega)⟩
  · exact ⟨k1, he 1 (by omega)⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.heard_at_z
