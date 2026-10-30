-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LastStepAtWalk.lean: THE HONEST SIDE's WALK (Johnson/Desc/ProofFile/Honest/Walk.lean):
THE VERIFIER's LAST STEP, OR LAST TWO, IN FRONT OF WHERE THE WALK STANDS, AS A SUB-PROTOCOL's OWN
STEP AT ROUNDS THAT SHOW THE CHALLENGES HEARD. General lemmas: no description, no kind. NONE OF THE
LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `okRounds_at_walk`   the words of the walk's rounds: walk_said
      (Johnson/Desc/ProofFile/Honest/Law/CoverBelow.lean), okWords_of_view
      (Johnson/Desc/Sound/PieceYes.lean)
  **`last_step_at_walk`**, **`last_two_at_walk`**   `fold_at_walk`
      (Johnson/P1K8R/SymbolsAtFrame.lean), `fold_rest` (LiveOfFold.lean), fold_split, step_less
      (Johnson/Top/H0/Walk/Reach.lean), foldBlocks_cons (Johnson/Desc/K15/FoldInv.lean)
Kin. NEAREST, the frame's authors': thr_back_rounds, thr_back_heard
(Johnson/Desc/ProofFile/Honest/Thread/ReachRounds.lean): the same sentence AT THE THREAD, where this
one is at the walk: the fold over the members in front at the rounds seen, the last member's own
step at the tail of these rounds, and that tail's challenges are the tail of the challenges heard;
by the same sealed lemmas. Not callable here: another structure. What stands here and not there: the
words' test on the rounds, the second step, the walk. That file has a `fold_rest` of its own
(ProofFile.Honest.fold_rest), which says the first half of ours (P1K8.fold_rest,
Johnson/P1K8R/LiveOfFold.lean): both stand; where both lie in one tree one should go. Ours:
`reach_last_words` (Johnson/P1K8R/StepOut.lean): the last step out of a reached state of the wrapped
family: there the rounds stand under an ∃ and nothing ties them to any challenges; `frontsOf_step`,
`quiet_in_event` (Johnson/Desc/ProofFile/Honest/K8/FrontsStep.lean): a step between two entries of
`frontsOf`, at a whole run.
Limits. That the walk starts and returns, where it stands, and that the challenges' elements' words
are below the prime are premises. Nothing says that any walk returns.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.SymbolsAtFrame
import Johnson.Top.H.K3LawKind
import Johnson.Desc.Sound.PieceYes
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (okRoundsE)
open VerifiableInference.Desc.Sound (okWords_of_view)
open Johnson.Desc.First.Walk.Tied (StepYes fold_split step_less)
open ProofFile.Honest (Lay ChainProgress Mid Step walk roundsOf start_tied walk_said)

section
variable {T Cl W Y : Type}

/-- The words that a walk's rounds show are below the prime, at every stretch of them, where the
elements of the challenges heard are. -/
theorem okRounds_at_walk (L : Lay) (bs : List (Block T Cl)) {a z : ChainProgress T Cl W Y}
    {m₀ : Option (Mid W Y)} {v₀ : Option T} {ss : List (Step W Y)} {dA : List Fmt.Drawn}
    {front : List Desc.OpenedColumn} (ha : ChainProgress.start L bs m₀ v₀ front = .ok a) (hz : walk L ss dA a = .ok z)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (i n : ℕ) : okRoundsE (((roundsOf z.laid).drop i).take n) = true := by
  obtain ⟨-, -, l0⟩ := start_tied L bs m₀ v₀ ha
  have hR : viewWordsBelowPrime ⟨roundsOf z.laid, []⟩ = true :=
    walk_said L ss dA a z hd (by rw [l0]; rfl) hz
  have hw := okWords_of_view _ hR
  unfold okRoundsE
  rw [List.all_eq_true] at hw ⊢
  exact fun r hr => hw r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

/-- **THE LAST STEP IN FRONT OF WHERE A WALK STANDS, WITH ITS ROUNDS TIED TO THE CHALLENGES HEARD.**
The walk stands in front of b, which has a round; blk is the sub-protocol just in front of b, pre
those in front of blk. Then the verifier's state beside the walk is what blk's own step returns,
from the state sj that the verifier's fold returns over pre, at rounds R: as many as blk has; their
words are below the prime; they show blk's own stretch of the challenges heard. -/
theorem last_step_at_walk (L : Lay) (pre t : List (Block T Cl)) (blk b : Block T Cl)
    {a z : ChainProgress T Cl W Y} {s₀ s' : T} {m₀ : Option (Mid W Y)} {ss : List (Step W Y)}
    {dA : List Fmt.Drawn} (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L (pre ++ blk :: b :: t) m₀ (some s₀) front = .ok a)
    (hpos : 0 < b.rounds.length) (hz : walk L ss dA a = .ok z)
    (hl : ss.length = ((pre ++ [blk]).flatMap (·.rounds)).length)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (hv : z.ver = some s') :
    ∃ (sj : T) (r₁ : List Fmt.RoundView) (c₁ : List Desc.OpenedColumn) (R : List Fmt.RoundView) (c : List Desc.OpenedColumn),
      foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols = .ok (sj, r₁, c₁) ∧
      R.length = blk.rounds.length ∧ blk.step L.firstTree sj R c = .ok (s', c.length) ∧
      okRoundsE R = true ∧
      R.map (·.drawn) = (dA.drop (pre.flatMap (·.rounds)).length).take blk.rounds.length := by
  have ha' : ChainProgress.start L ((pre ++ [blk]) ++ b :: t) m₀ (some s₀) front = .ok a := by
    rw [List.append_assoc]
    exact ha
  obtain ⟨r, c, hf, hdr⟩ := fold_at_walk L (pre ++ [blk]) t b hm ha' hpos hz hl hv
  obtain ⟨sj, r₁, c₁, g1, g2⟩ := fold_split L.firstTree [blk] pre _ _ _ _ hf
  obtain ⟨e1, -⟩ := fold_rest L.firstTree _ _ _ _ _ _ _ g1
  obtain ⟨s₂, k, hlen, g3, g4⟩ := foldBlocks_cons L.firstTree blk [] sj r₁ c₁ _ g2
  unfold foldBlocks at g4
  injection g4 with g4
  obtain ⟨rfl, -⟩ := Prod.mk.inj g4
  refine ⟨sj, r₁, c₁, r₁.take blk.rounds.length, c₁.take k, g1, hlen, step_less g3, ?_, ?_⟩
  · rw [e1]
    exact okRounds_at_walk L _ ha hz hd _ _
  · rw [e1, List.map_take, List.map_drop, hdr]
    rfl

/-- **The like where one more sub-protocol, b₁, stands between**: blk's step as above, into a state
sk; then an accepting step of b₁ from sk into the state beside the walk. -/
theorem last_two_at_walk (L : Lay) (pre t : List (Block T Cl)) (blk b₁ b : Block T Cl)
    {a z : ChainProgress T Cl W Y} {s₀ s' : T} {m₀ : Option (Mid W Y)} {ss : List (Step W Y)}
    {dA : List Fmt.Drawn} (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L (pre ++ blk :: b₁ :: b :: t) m₀ (some s₀) front = .ok a)
    (hpos : 0 < b.rounds.length) (hz : walk L ss dA a = .ok z)
    (hl : ss.length = ((pre ++ [blk, b₁]).flatMap (·.rounds)).length)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (hv : z.ver = some s') :
    ∃ (sj sk : T) (r₁ : List Fmt.RoundView) (c₁ : List Desc.OpenedColumn) (R : List Fmt.RoundView)
      (c : List Desc.OpenedColumn),
      foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols = .ok (sj, r₁, c₁) ∧
      R.length = blk.rounds.length ∧ blk.step L.firstTree sj R c = .ok (sk, c.length) ∧
      okRoundsE R = true ∧
      R.map (·.drawn) = (dA.drop (pre.flatMap (·.rounds)).length).take blk.rounds.length ∧
      StepYes L.firstTree b₁ sk s' := by
  have ha' : ChainProgress.start L ((pre ++ [blk, b₁]) ++ b :: t) m₀ (some s₀) front = .ok a := by
    rw [List.append_assoc]
    exact ha
  obtain ⟨r, c, hf, hdr⟩ := fold_at_walk L (pre ++ [blk, b₁]) t b hm ha' hpos hz hl hv
  obtain ⟨sj, r₁, c₁, g1, g2⟩ := fold_split L.firstTree [blk, b₁] pre _ _ _ _ hf
  obtain ⟨e1, -⟩ := fold_rest L.firstTree _ _ _ _ _ _ _ g1
  obtain ⟨sk, k, hlen, g3, g4⟩ := foldBlocks_cons L.firstTree blk [b₁] sj r₁ c₁ _ g2
  obtain ⟨s₂, k₂, hlen₂, g5, g6⟩ := foldBlocks_cons L.firstTree b₁ [] sk _ _ _ g4
  unfold foldBlocks at g6
  injection g6 with g6
  obtain ⟨rfl, -⟩ := Prod.mk.inj g6
  refine ⟨sj, sk, r₁, c₁, r₁.take blk.rounds.length, c₁.take k, g1, hlen, step_less g3, ?_, ?_,
    ⟨_, _, hlen₂, step_less g5⟩⟩
  · rw [e1]
    exact okRounds_at_walk L _ ha hz hd _ _
  · rw [e1, List.map_take, List.map_drop, hdr]
    rfl

end

end P1K8

#print axioms P1K8.okRounds_at_walk
#print axioms P1K8.last_step_at_walk
#print axioms P1K8.last_two_at_walk
