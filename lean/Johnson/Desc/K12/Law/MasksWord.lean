-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BeforeLater
import Johnson.Desc.K12.Law.SeatKeeps
import Johnson.Desc.K12.Law.MasksPlan
/-
Johnson/Desc/K12/Law/MasksWord.lean: THE PLAN's HALF OF THE ROW masks_fixed_word, AT A SEAT, FIRST FORM (the sharper second: MasksWord2.lean): from the block's own test on the plan and the file's test beforeAt. One statement and its proof. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  masks_word_seat: (proximityTestKind guardedProximityTestParts p).planOk = true · b keeps that block's «before» and declared rounds (SeatKeeps.lean: the four seats, a guard, another type of claims) · beforeAt's yes at pre ++ b :: post · the place's chain is the list's · the chain's declared rounds are preR ++ (b.rounds ++ postR) with b at preR's end · free = rootsOf preR. THEN
    (A) each tree of nums.first (the members' and the mask's, where it has come earlier) is sent STRICTLY IN FRONT OF "BAT"'s ROUND, the block's first draw, or in an earlier chain; or it is the first fold's own mask's tree (first_sent);
    (B) every tree that a switch or the base case opens is sent in front of the round behind THAT STAGE's first round | in front of the base case's first round (opened_sent);
    (B⁺) at a stage behind the first: STRICTLY IN FRONT OF THAT STAGE's FIRST ROUND (masks_fixed_later, BeforeLater.lean).
  SO, BY (A) · (B⁺) · (B)'s half on the base case, AND BY MasksFixed.made (a theorem of planOk too, NOT A CONJUNCT HERE: what the first switch opens is nums.first and then the own mask's tree): THE ONE TREE THAT IS NOT SENT IN FRONT OF ITS STAGE's FIRST ROUND IS THE FIRST FOLD's OWN MASK's, which is sent in that round, in front of its draw.
  READ (A) AND (B) TOGETHER: at the first stage (B) alone would let a member's tree stand in "BAT"'s round or the fold's first.
Limits, to be said wherever it is told: (α) «before the BLOCK's first draw» holds of nums.first's trees alone; the later stages' trees are sent inside the block, behind "BAT"'s draw: of them: «in front of that STAGE's first draw» · (β) at the FIRST stage (B)'s bound admits a tree sent IN the fold's first round: so it must: the first fold's own mask's tree is sent there; the members' trees have (A) · (γ) trees, not words: nothing on what a tree holds; and ROUNDS' NUMBERS OF THE DECLARED PLAN, not the typed chain's letters: the bridge to the library's «a word fixed before the block» is not shown here · (δ) free = rootsOf preR IS ASKED BY NO TEST ON A PLAN: a yes of the step gives free = the RECORD's count of roots; here there is no yes to spend.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.G.OfPlan (rootsOf)

theorem masks_word_seat {S Cl : Type} (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (b : Block S Cl)
    (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit))
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre post : List (Block S Cl))
    (hc : p.place.chain = c + 1) (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (preR postR : List Fmt.DeclaredRound) (hDs : chainOf D (c + 1) = preR ++ (b.rounds ++ postR))
    (hlen : preR.length = from' + roundsIn pre) (hfree : p.nums.free = rootsOf preR) :
    (∀ o ∈ p.nums.first,
      (∃ n, o.2 = .own n ∧ n < p.nums.free ∧
        ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < from' + roundsIn pre) ∨
      (∃ c' n, o.2 = .taken c' n ∧ c' ≤ c ∧ ∃ i, sendRound (chainOf D (c' + 1)) n = some i ∧
        (c' = c → i < from' + roundsIn pre)) ∨
      (p.nums.ownMask = true ∧ o.2 = .own p.nums.free)) ∧
    (∀ (j : ℕ) (s : Fmt.M1.Stage), j + 1 < p.nums.stages.length → p.nums.stages[j]? = some s →
      ∀ r ∈ (b.rounds.drop (H2K.FixedBefore.foldStart 1 p.nums.stages j + 1 + s.k)).take 2,
      ∀ o ∈ r.opens, SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre + (H2K.FixedBefore.foldStart 1 p.nums.stages j + 1)) o) ∧
    (∀ r ∈ (b.rounds.drop
        (H2K.FixedBefore.foldStart 1 p.nums.stages (p.nums.stages.length - 1))).take 2,
      ∀ o ∈ r.opens, SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre +
          H2K.FixedBefore.foldStart 1 p.nums.stages (p.nums.stages.length - 1)) o) ∧
    (∀ (j : ℕ) (s : Fmt.M1.Stage), 1 ≤ j → j + 1 < p.nums.stages.length →
      p.nums.stages[j]? = some s →
      ∀ r ∈ (b.rounds.drop (H2K.FixedBefore.foldStart 1 p.nums.stages j + 1 + s.k)).take 2,
      ∀ o ∈ r.opens, SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre + H2K.FixedBefore.foldStart 1 p.nums.stages j) o) := by
  obtain ⟨hbef, hr⟩ := seat_pays guardedProximityTestParts p hp b hk
  have hD : (chainOf D (c + 1))[from' + roundsIn pre]? = b.rounds.head? := by
    obtain ⟨_, _, _, R, _, _, e⟩ := rounds_top p.nums b.rounds hr
    rw [hDs, ← hlen, e]
    simp
  obtain ⟨w1, w2⟩ := opened_sent p (H2K.JointK.fixed_of_planOk p hp) b.rounds hr D O c from' pre
    b post hbef rfl hc h preR postR hDs hlen hfree
  exact ⟨first_sent p (masksFixed_of_planOk p hp) b.rounds hr D O c from' pre b post hbef rfl hc h hD,
    w1, w2, fun j s h1 hj hs => masks_fixed_later p (H2K.JointK.fixed_of_planOk p hp) b.rounds hr D O c
      from' pre b post hbef rfl hc h preR postR hDs hlen hfree j s h1 hj hs⟩

end H2K.Made

#print axioms H2K.Made.masks_word_seat
