-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MasksWord
import Johnson.Desc.K12.Law.BeforeSeed
import Johnson.Desc.K12.Law.FirstNe
/-
Johnson/Desc/K12/Law/MasksWord2.lean: THE PLAN's HALF OF THE ROW masks_fixed_word, AT A SEAT, SECOND FORM: sharper at three places than masks_word_seat (MasksWord.lean). Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  (the first) masks_word_seat's (A) had a third arm, «ownMask ∧ the source is own free», which ANY entry of nums.first with that source met: a member's tree could stand behind "BAT"'s draw. HERE firstNe p = true IS A PREMISE (no tree of nums.first has the source own free) and the arm is gone: first_sent_ne. (THE THIRD FORM, seat_word3 in FirstNeBook.lean, has in its place a clause of the file's own test on the plan.)
  (the second) «in front of the stage's first round» admitted the round "CS", behind the seeds' draw. HERE: not later than the round "SEND seed" of the stage before (BeforeSeed.lean).
  (the third) keeps_planOk | keeps_place: a block with another test on the plan, or another place, written into its field keeps «before» and the rounds: the two wrappers that the base lays on a flat list (Chain.blocksInOrder's; the first driver's stamp).
  sendRound_append · own_mask_round: WHERE THE OWN MASK's TREE IS SENT: under ownMask, hDs, hlen, hfree: sendRound ‹the chain› free = some (‹the block's first› + 1): the first fold's first round, and no other.
  seat_word2: planOk · firstNe · Keeps · beforeAt's yes · hc · hDs | hlen · hfree ⇒
    (A') each tree of nums.first: an own tree below free sent STRICTLY IN FRONT OF "BAT"'s ROUND, or one «taken c' n», c' ≤ c, sent in the chain c' + 1 (in front of "BAT"'s round if c' = c);
    (M) under ownMask the tree own free is sent in the round behind "BAT"'s, the first fold's first;
    (B₀) what the first switch opens is sent in front of the round behind that;
    (S) what a later switch opens, (S') what the base case opens: sent not later than "SEND seed" of the stage before.
Limits: firstNe as a Boolean is asked by no running text; under ownMask it follows from BookPlan's clause inOrder (FirstNeBook.lean) · hfree is asked by no test on a plan · for c' < c (A') says «is sent in its chain», NO ORDER: that an earlier chain's rounds all stand in front of a later chain's is the file's order of chains: the reading's · trees and declared rounds' numbers, not words; no bridge to the typed chain's letters · THE ROW ITSELF («an unsampled word … is one word fixed before the block») STAYS OWED.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FixedBefore (foldStart)
open Johnson.G.OfPlan (rootsOf)

theorem keeps_planOk {S Cl : Type} (b : Block S Cl) (x : Bool) : Keeps { b with planOk := x } b :=
  ⟨rfl, rfl⟩

theorem keeps_place {S Cl : Type} (b : Block S Cl) (a : Place) : Keeps { b with place := a } b :=
  ⟨rfl, rfl⟩

theorem sendRound_append : ∀ (l l' : List Fmt.DeclaredRound) (m : ℕ),
    sendRound (l ++ l') (rootsOf l + m) = (sendRound l' m).map (· + l.length)
  | [], l', m => by simp [rootsOf]
  | r :: l, l', m => by
    have hn : ¬ rootsOf (r :: l) + m < r.entry.roots := by
      simp only [rootsOf, List.map_cons, List.sum_cons]
      omega
    have e : rootsOf (r :: l) + m - r.entry.roots = rootsOf l + m := by
      simp only [rootsOf, List.map_cons, List.sum_cons]
      omega
    rw [List.cons_append, sendRound, if_neg hn, e, sendRound_append l l' m, Option.map_map]
    congr 1

/-- Where the first fold's own mask's tree is sent. -/
theorem own_mask_round (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums N = some rds) (hown : N.ownMask = true)
    (preR postR : List Fmt.DeclaredRound) (hfree : N.free = rootsOf preR) :
    sendRound (preR ++ (rds ++ postR)) N.free = some (preR.length + 1) := by
  obtain ⟨s, next, rest, R', _, _, rfl⟩ := rounds_head N rds hr
  have h := sendRound_append preR
    (((⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
      ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s.k
        (⟨(Fmt.M1.rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
      (⟨(Fmt.M1.rSeed next).entry, [], []⟩ :: ⟨(Fmt.M1.rCs N.work s 0 0).entry, [],
        N.first ++ (if N.ownMask then (told N).take 1 else [])⟩ :: R'))) ++ postR) 0
  rw [Nat.add_zero, ← hfree] at h
  rw [h]
  simp [sendRound, epsE_roots, hown]
  exact ⟨1, rfl, Nat.add_comm _ _⟩

theorem first_sent_ne {S Cl : Type} (p : P12) (M : MasksFixed p) (hne : firstNe p = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (hD : (chainOf D (c + 1))[from' + roundsIn pre]? = rds.head?) :
    ∀ o ∈ p.nums.first,
      (∃ n, o.2 = .own n ∧ n < p.nums.free ∧
        ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < from' + roundsIn pre) ∨
      (∃ c' n, o.2 = .taken c' n ∧ c' ≤ c ∧ ∃ i, sendRound (chainOf D (c' + 1)) n = some i ∧
        (c' = c → i < from' + roundsIn pre)) := by
  intro o ho
  rcases first_sent p M rds hr D O c from' pre b post hbef hrd hc h hD o ho with h1 | h2 | h3
  · exact .inl h1
  · exact .inr h2
  · have := List.all_eq_true.1 hne o ho
    exact absurd h3.2 (of_decide_eq_true this)

/-- **The plan's half of the row, at a seat, second form.** -/
theorem seat_word2 {S Cl : Type} (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (hne : firstNe p = true)
    (b : Block S Cl) (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit))
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre post : List (Block S Cl))
    (hc : p.place.chain = c + 1) (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (preR postR : List Fmt.DeclaredRound) (hDs : chainOf D (c + 1) = preR ++ (b.rounds ++ postR))
    (hlen : preR.length = from' + roundsIn pre) (hfree : p.nums.free = rootsOf preR) :
    (∀ o ∈ p.nums.first,
      (∃ n, o.2 = .own n ∧ n < p.nums.free ∧
        ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < from' + roundsIn pre) ∨
      (∃ c' n, o.2 = .taken c' n ∧ c' ≤ c ∧ ∃ i, sendRound (chainOf D (c' + 1)) n = some i ∧
        (c' = c → i < from' + roundsIn pre))) ∧
    (p.nums.ownMask = true →
      sendRound (chainOf D (c + 1)) p.nums.free = some (from' + roundsIn pre + 1)) ∧
    (∀ s : Fmt.M1.Stage, 0 + 1 < p.nums.stages.length → p.nums.stages[0]? = some s →
      ∀ r ∈ (b.rounds.drop (foldStart 1 p.nums.stages 0 + 1 + s.k)).take 2, ∀ o ∈ r.opens,
        SentBy D c (from' + roundsIn pre)
          (from' + roundsIn pre + (foldStart 1 p.nums.stages 0 + 1)) o) ∧
    (∀ (j : ℕ) (s s' : Fmt.M1.Stage), p.nums.stages[j]? = some s →
      j + 1 + 1 < p.nums.stages.length → p.nums.stages[j + 1]? = some s' →
      ∀ r ∈ (b.rounds.drop (foldStart 1 p.nums.stages (j + 1) + 1 + s'.k)).take 2, ∀ o ∈ r.opens,
        SentBy D c (from' + roundsIn pre)
          (from' + roundsIn pre + (foldStart 1 p.nums.stages j + (s.k + 2))) o) ∧
    (∀ (j : ℕ) (s : Fmt.M1.Stage), p.nums.stages[j]? = some s → j + 2 = p.nums.stages.length →
      ∀ r ∈ (b.rounds.drop (foldStart 1 p.nums.stages (j + 1))).take 2, ∀ o ∈ r.opens,
        SentBy D c (from' + roundsIn pre)
          (from' + roundsIn pre + (foldStart 1 p.nums.stages j + (s.k + 2))) o) := by
  obtain ⟨hbef, hr⟩ := seat_pays guardedProximityTestParts p hp b hk
  have hfx := H2K.JointK.fixed_of_planOk p hp
  have hD : (chainOf D (c + 1))[from' + roundsIn pre]? = b.rounds.head? := by
    obtain ⟨_, _, _, R, _, _, e⟩ := rounds_top p.nums b.rounds hr
    rw [hDs, ← hlen, e]
    simp
  refine ⟨first_sent_ne p (masksFixed_of_planOk p hp) hne b.rounds hr D O c from' pre b post hbef rfl
    hc h hD, fun hown => ?_, fun s h0 hs => ?_, fun j s s' hs hj hs' => ?_, fun j s hs hl => ?_⟩
  · rw [hDs, ← hlen]
    exact own_mask_round p.nums b.rounds hr hown preR postR hfree
  · exact (opened_sent p hfx b.rounds hr D O c from' pre b post hbef rfl hc h preR postR hDs
      hlen hfree).1 0 s h0 hs
  · exact sent_seed p hfx b.rounds hr D O c from' pre b post hbef rfl hc h preR postR hDs hlen hfree
      j s s' hs hj hs'
  · exact sent_seed_base p hfx b.rounds hr D O c from' pre b post hbef rfl hc h preR postR hDs hlen
      hfree j s hs hl

end H2K.Made

#print axioms H2K.Made.sendRound_append
#print axioms H2K.Made.own_mask_round
#print axioms H2K.Made.first_sent_ne
#print axioms H2K.Made.seat_word2
