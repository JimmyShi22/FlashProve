-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/AtSeat.lean: K9's COUNT FOR ITS "free-slot" TEST, WITH "GOOD" AS A WRITTEN BOOL, AT
THE BATCHING BLOCK THAT THE PROOF FILE's DESCRIPTION SEATS AT A FEED-FORWARD SEGMENT. A lemma ON THE VERIFIER's TEXT;
no prover is in this file, and no goal is stated. An assembly, after part 1's `fall_at_seat`
(Johnson/P1K8R/FallAtSeat.lean), whose road through the sealed library it follows: `IM.k9_of` with `IM.yes_alone` (the
seated batching is K9's own under the seat's guards; the order is the driver's; the tests behind the adding are
`k9Tests`) · `LPFK9.k09_sits` (the block behind) · `LPFK9.layers_ties_at` (which run stands where) ·
`OnPublicFiles.at_objects_is` (the two runs "objects").

The letters are those of an opening of the description (`IM.Open`, Johnson/IMR/SeatOpen.lean): c its first chain.
  **`free_at_seat`**   WHEREVER THE DESCRIPTION CAN BE OPENED IN THE GOALS' SCOPE (the premises hS, hR, O: that they
      can be met together is shown by no known theorem), at each feed-forward segment l there are the
      segment Lk, the batching's numbers p, K4's numbers p4 (`LPFK9.k4ParAt`), the built entry X and K9's numbers w
      off the public parameters (`K9.testsWhere`) such that the block at number 14 l + 9 of the chain's flat list is
      Lk's batching at the frame's own gatherer, the block at the next number is the frame's block behind the
      batching, and
      (1) `Walk` (Honest/K9/LayersFree.lean) holds at every state that stands in a feed-forward segment;
      (2) `RunsLaw` holds there, at the frame's own gatherer: A LAW ON THE YESES OF DRAW AND GATHERER: where they
      never return it holds idly;
      (3) THE COUNT: at every such state s that is good (`GoodLayers p4 s a₀ n`): at most n * (THE STATE's ledger's
      plan's number of claims - 1) READINGS of a chi at which THAT SEATED BLOCK's decision says yes and K9's
      "free-slot" AT n SLOTS, or with it K4's condition at the same n and the same state, speaks at the state behind;
      (4) A FALL, SO A REFUSAL: where K9's share AT THE PUBLIC PARAMETERS' NUMBER OF FILLED SLOTS speaks at a state,
      the block behind the batching refuses at that state. (The other way, for the segment's own tests:
      `SeatedFree.tests`, Honest/K9/AtSeatAll.lean.)
WHAT IS NOT CLAIMED. THAT DRAW AND GATHERER RETURN AT ANY STATE AND CHALLENGE. THAT `GoodLayers` IS TRUE AT A STATE OF
A RUN: no member is shown; where nothing was heard it holds idly, and nothing is counted. THAT THE STATE's PLAN's
NUMBER IS THE PUBLIC PARAMETERS' (w.2.1), or that n is w.2.2.filled: n is free in (3). OF K4's OWN "free-slot": that
its number (p4.hp.used) is w.2.2.filled is shown nowhere, and its run is asked behind another run, at a later state:
(3) speaks of K4's CONDITION at K9's number and state alone. That a state which the chain's own blocks reach stands in
a feed-forward segment. The count is at the block's decision at no column and at the round as `drawnOne` gives it (the
step: Honest/K9/AtStep.lean). Readings, not words; no probability. The full size, the format's second hash function,
feed-forward segments alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LayersFree
import Johnson.LPFK9R.TiesWholeAt
import Johnson.LPFK9R.Sits
import Johnson.Desc.First.Link.Law.SortK3Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **K9's count at the seated block.** -/
theorem free_at_seat {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (Lk : Link S Claim) (p : Desc.K9.Where) (p4 : OnBytes.Desc.First.K4.Par)
      (X : OnBytes.Model.Stages.LinkH) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere),
      c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧ LPFK9.k4ParAt Z Bs.G₀ l = some p4 ∧
      Bs.G₀.built.toList[l]? = some X ∧ Desc.K9.testsWhere Z.p.X l 0 = some w ∧
      c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      (∃ b, c.blocksInOrder[14 * l + 10]? = some b ∧ ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) ∧
      (∀ (s : S) (a₀ : LayOwn), s.here = .lay a₀ → Walk Lk p4 (ProofFile.k8NU Bs.G₀ X) s a₀) ∧
      (∀ (s : S) (a₀ : LayOwn), s.here = .lay a₀ →
        RunsLaw p (claimsInBy Lk.each Lk.hear Lk.order) s) ∧
      (∀ (s : S) (a₀ : LayOwn) (n : ℕ), s.here = .lay a₀ → GoodLayers p4 s a₀ n →
        ∀ k4 : Option ℕ, (k4 = none ∨ k4 = some n) →
        Prob.cnt (fun z : Cb.Gl.E => ∃ x : E, Reading.gl.val x = z ∧
          FallsAt (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s n k4 x) ≤
          n * (a₀.F.planClaimsF - 1)) ∧
      (∀ s₁ : S, (freeSlotShare w.2.2.filled s₁).isSome = true → ∀ t, Lk.runBehind s₁ ≠ .ok t) := by
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, -, hlen, hw, -, -, hT, hLT⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk₂, p₂, Q, -, -, hsit⟩ := LPFK9.k09_sits hS hR O l hl
  obtain rfl : Lk = Lk₂ := Option.some.inj (e1.symm.trans hsit.link)
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', p4, X, e1', hp4, hX, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun']
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun']
    exact LinkJoin.under_refl _
  have walk : ∀ (s : S) (a₀ : LayOwn), s.here = .lay a₀ → Walk Lk p4 (ProofFile.k8NU Bs.G₀ X) s a₀ :=
    fun s a₀ hs => ⟨ties, tC, tD, hord, hs⟩
  have f9 : c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
    rw [h7] at hflat
    exact hflat
  have f10 : c.blocksInOrder[14 * l + 10]? = some Lk.behindB := by
    have h := hsit.flat₂
    rw [h7] at h
    exact h
  refine ⟨Lk, p, p4, X, w, e1, e2, hp4, hX, hw, f9, ⟨Lk.behindB, f10, fun _ _ _ => rfl⟩, walk,
    fun s a₀ hs => runsLaw_layers Lk p4 _ p s a₀ (walk s a₀ hs), ?_, ?_⟩
  · intro s a₀ n hs good k4 hk
    refine free_few_layers Lk p4 _ p s a₀ (walk s a₀ hs) n good k4 hk _ ?_
    intro rs t ht
    have k9ne : KindName.K9 ≠ KindName.K7 := by decide
    exact ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne s t rs []).1 ht).1
  · intro s₁ hq t ht
    unfold Link.runBehind at ht
    rw [hLT] at ht
    cases hts : T s₁ with
    | error m => rw [hts] at ht; exact nomatch ht
    | ok u =>
      obtain ⟨w', hw', _, hfree, _⟩ := (tests_iff Z l T hT s₁).1 hts
      obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
      unfold freeSlotShare at hq
      rw [hfree] at hq
      exact nomatch hq

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.free_at_seat
