-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/HeardAtReach.lean: THE SMALLNESS TEST: THE SEVEN SIZES OF WHAT THE DIGITS'
LOOKUP HAS HEARD (the two points zb0 and zb1; `HeardSizes`, Johnson/Desc/K8/Honest/HeldPublic.lean)
AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF THE BATCHING OF ONE OF THE 24
SEGMENTS IN FRONT OF THE HEAD's, IN THE GOALS' SCOPE: off the library's promise `K3Left` at the
state's own f9 (`left_at_batch`, Johnson/Desc/K8/Honest/LeftAtReach.lean), which holds the sizes in
the numbers of the lookup's shape. So `AllFront` there from: one public test with code at the built
segment's data · pointsHeld · the name of the digits' array. Lemmas; none of the library's goals.

  `pub_numbers` the public test ⊢ f9.dT and f9.rK are the numbers that forestHeld's text compares
                   the sizes with
  **`heardSizes_at_batch`** under the public test at the built segment's data: what the lookup heard
                   is there, with the seven sizes
  **`allFront_of_three`** what the lookup heard is there; and pointsHeld · the name "ZZ" at it ⊢
                   there are nbW, Wn with AllFront tl G g nbW Wn
By: `left_at_batch` · `K3Left.zb_size` (Johnson/Top/H/K3LeftPoint.lean) · `tests_at_built`
(Johnson/P1K8R/StaticAtBuilt.lean) · `two_calls_of_tests`
(Johnson/Desc/K8/Honest/BitsPubAtBatch.lean) · `allFront_of_heard`
(Johnson/Desc/K8/Honest/FrontFromSizes.lean).
Limits. AN IMPLICATION: THE PUBLIC TEST IS A PREMISE HERE; IN SCOPE, UNDER AN OPENING OF THE
DESCRIPTION AND ITS TEST ON ITS PLAN, IT SAYS YES AT EACH OF THE 25 BUILT SEGMENTS' DATA
(`heldPub_at_built`, Johnson/Desc/K8/Honest/HeldOutright.lean); pointsHeld AND THE NAME ARE PREMISES
HERE. NOTHING AT THE HEAD's SEGMENT. IN SCOPE ALONE: under an opening of the description and its
test on its plan; the first chain; the family of states from the description's own first state.
Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.FrontFromSizes
import Johnson.Desc.K8.Honest.LeftAtReach
import Johnson.Top.H.K3LeftPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (K3Left)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The public test holds the two numbers of the shape that the sizes are compared with. -/
theorem pub_numbers {tl : HTailF2} (hP : heldPubB tl = true) :
    tl.f9.dT = min tl.z1.call.n tl.lidb ∧
      tl.f9.rK = tl.z1.call.n - min tl.z1.call.n tl.lidb + 1 := by
  unfold heldPubB at hP
  rw [Bool.and_eq_true] at hP
  have p1 := hP.1
  simp only [HTailF2.forestHeld, Bool.and_eq_true, beq_iff_eq] at p1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, q2⟩, -⟩, -⟩, q5⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := p1
  exact ⟨q2, q5⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The seven sizes.** -/
theorem heardSizes_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    (ht : s.tl? = some tl) (hP : heldPubB Xl.tl = true) :
    ∃ g, tl.heard = some g ∧ HeardSizes tl g ∧ g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK) ∧
      g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK) := by
  obtain ⟨v, g, F₀, F', rs, hg, K⟩ := left_at_batch hS hR O hOk hl e3 h ht
  have hP' : heldPubB tl = true := by
    rw [pub_heldFields tl, v, ← pub_heldFields Xl.tl]
    exact hP
  obtain ⟨n1, n2⟩ := pub_numbers hP'
  have T := _root_.P1K8.tests_at_built hS O (by omega : l < 25) e3
  have v9 : tl.f9 = Xl.tl.f9 := congrArg (·.f9) v
  have v1 : tl.z1 = Xl.tl.z1 := congrArg (·.z1) v
  have v2 : tl.z2 = Xl.tl.z2 := congrArg (·.z2) v
  have nc : tl.f9.NC = 2 := by
    rw [v9]
    exact (two_calls_of_tests T).1
  have t4 := T.t4
  unfold _root_.Fo.callsTest at t4
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at t4
  obtain ⟨k0, k1⟩ := t4
  have z0 : (Xl.tl.zOf 0) = Xl.tl.z1 := rfl
  have z1 : (Xl.tl.zOf 1) = Xl.tl.z2 := rfl
  refine ⟨g, hg, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [K.zy, n2]
  · rw [K.zx, n1]
  · rw [K.eRaw, Array.size_map, Array.size_range, nc]
  · rw [K.zkLen 0 (by omega), v9, k0, z0, v1]
  · rw [K.zkLen 1 (by omega), v9, k1, z1, v2]
  · rw [K.zb_size.1]
    omega
  · rw [K.zb_size.2]
    omega

/-- **SO `AllFront` THERE FROM THE PUBLIC TEST AND TWO SENTENCES.** -/
theorem allFront_of_three (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (hP : heldPubB Xl.tl = true) :
    ∃ g, tl.heard = some g ∧ (tl.pointsHeld g = true →
      (G.trees.getD tl.ix.ZZ {}).name = "ZZ" →
      ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn) := by
  obtain ⟨g, hg, hZ, b0, b1⟩ := heardSizes_at_batch hS hR O hOk hl e3 h ht hP
  obtain ⟨g', hg', k⟩ := allFront_of_heard hS hR O hOk hl e3 h ht hG hP
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  exact ⟨g, hg, fun hp hn => k ⟨b0, b1, hZ, hp, hn⟩⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pub_numbers
#print axioms VerifiableInference.Desc.First.K8.Honest.heardSizes_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_three
