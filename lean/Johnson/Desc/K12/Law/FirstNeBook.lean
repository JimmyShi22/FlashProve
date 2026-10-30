-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MasksWord2
import Johnson.Desc.BookPlanLaws
/-
Johnson/Desc/K12/Law/FirstNeBook.lean: «NO TREE OF nums.first IS THE FIRST FOLD's OWN MASK's» IS A THEOREM OF THE FILE's TEST ON THE PLAN: of BookPlan's eleventh clause inOrder («in every round the opened trees' places rise strictly»; a conjunct of FileDescription.treeSharingOk, so of FileDescription.planOk). Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
WHY: the block's own planOk and beforeAt let a plan through whose nums.first holds a tree with the source own free (said here without a theorem): a member's tree behind "BAT"'s draw. firstNe shut that and was asked by no running text. inOrder is asked: the first switch's round "CS" opens nums.first and THEN the own mask's tree own free: places that rise strictly cannot hold own free twice.
  OVER inOrderIn_round · earlierPlace_ne (Johnson/Desc/BookPlanLaws.lean).
  no_first_own_free: ownMask · MasksFixed p · the declared rounds rds · inOrderIn c ds = true · every round of rds is one of ds ⇒ no o ∈ nums.first has the source own free.
  seat_word3: seat_word2 WITHOUT THE PREMISE firstNe: in its place inOrderIn c (chainOf D (c + 1)) = true. All five conjuncts as there.
Limits: as MasksWord2.lean's, but the one on firstNe. hfree stays asked by no test on a plan.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.BookPlan (earlierPlace treePlace inOrderIn inOrderIn_round earlierPlace_ne)
open H2K.FixedBefore (foldStart)
open Johnson.G.OfPlan (rootsOf)

/-- **No tree of nums.first is the own mask's: from the file's clause inOrder.** -/
theorem no_first_own_free (p : P12) (M : MasksFixed p) (hown : p.nums.ownMask = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds) (c : ℕ)
    (ds : List Fmt.DeclaredRound) (hin : inOrderIn c ds = true) (hsub : ∀ r ∈ rds, r ∈ ds) :
    ∀ o ∈ p.nums.first, o.2 ≠ .own p.nums.free := by
  obtain ⟨x, W, hT⟩ := M.own hown
  obtain ⟨s, next, rest, R', _, _, rfl⟩ := rounds_head p.nums rds hr
  have hmem : (⟨(Fmt.M1.rCs p.nums.work s 0 0).entry, [],
      p.nums.first ++ (if p.nums.ownMask then (told p.nums).take 1 else [])⟩ : Fmt.DeclaredRound) ∈ ds :=
    hsub _ (by simp)
  have h1 := inOrderIn_round hin hmem
  have e : (if p.nums.ownMask then (told p.nums).take 1 else []) = [p.nums.own x W p.nums.free] := hT
  simp only [e, List.map_append, List.map_cons, List.map_nil] at h1
  intro o ho heq
  have h2 := (List.pairwise_append.1 h1).2.2 (treePlace c o.2) (List.mem_map.2 ⟨o, ho, rfl⟩)
    (treePlace c (p.nums.own x W p.nums.free).2) (List.mem_singleton.2 rfl)
  rw [heq] at h2
  exact earlierPlace_ne h2 rfl

/-- **The plan's half of the row, at a seat, third form.** Of its premises h and hin are conjuncts of
the file's test on the plan, hp | hk | hc the seat's, hDs | hlen are paid in FileWord.lean
(word_at_list); hfree is asked by no test on a plan. -/
theorem seat_word3 {S Cl : Type} (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (b : Block S Cl) (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit))
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre post : List (Block S Cl))
    (hc : p.place.chain = c + 1) (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (hin : inOrderIn c (chainOf D (c + 1)) = true)
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
  have M := masksFixed_of_planOk p hp
  have hD : (chainOf D (c + 1))[from' + roundsIn pre]? = b.rounds.head? := by
    obtain ⟨_, _, _, R, _, _, e⟩ := rounds_top p.nums b.rounds hr
    rw [hDs, ← hlen, e]
    simp
  refine ⟨fun o ho => ?_, fun hown => ?_, fun s h0 hs => ?_, fun j s s' hs hj hs' => ?_,
    fun j s hs hl => ?_⟩
  · rcases first_sent p M b.rounds hr D O c from' pre b post hbef rfl hc h hD o ho with h1 | h2 | h3
    · exact .inl h1
    · exact .inr h2
    · exact absurd h3.2 (no_first_own_free p M h3.1 b.rounds hr c _ hin (fun r hr' => by
        rw [hDs]
        simp [hr']) o ho)
  · rw [hDs, ← hlen]
    exact own_mask_round p.nums b.rounds hr hown preR postR hfree
  · exact (opened_sent p hfx b.rounds hr D O c from' pre b post hbef rfl hc h preR postR hDs
      hlen hfree).1 0 s h0 hs
  · exact sent_seed p hfx b.rounds hr D O c from' pre b post hbef rfl hc h preR postR hDs hlen hfree
      j s s' hs hj hs'
  · exact sent_seed_base p hfx b.rounds hr D O c from' pre b post hbef rfl hc h preR postR hDs hlen
      hfree j s hs hl

end H2K.Made

#print axioms H2K.Made.no_first_own_free
#print axioms H2K.Made.seat_word3
