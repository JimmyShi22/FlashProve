-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MidStepAtWalk.lean: THE HONEST SIDE's WALK (Johnson/Desc/ProofFile/Honest/Walk.lean):
ANY OF THE VERIFIER's STEPS IN FRONT OF WHERE THE WALK STANDS, AS THE SUB-PROTOCOL's OWN STEP
BETWEEN TWO REACHED STATES, AT ROUNDS THAT SHOW THE CHALLENGES HEARD, AT WHICH NO MARK ASKED AT ITS
PLACE SPEAKS. General lemmas: no description, no kind. NONE OF THE LIBRARY's GOALS. A joining.
Nothing on completeness, soundness or hiding.

  **`mid_step_at_walk`**   `last_step_at_walk` and `last_two_at_walk`
      (Johnson/P1K8R/LastStepAtWalk.lean) are the like at no member and at one member between; by
      the same lemmas
  **`mid_handed`**   at what the frame's field hP' hands: `quiet_at_member`
      (Johnson/P1K8R/SymbolsAtFrame.lean), `elems_of_quiet` (LooksAtFrame.lean), reach_of_fold
      (Johnson/Top/H0/Walk/Reach.lean)
Kin. Closest are two lemmas of the frame's authors in
Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean. made_member speaks of a `Thread` where we speak
of a walk: below a made border b it gives, for each j < b, an accepting step of block j whose rounds
carry that block's slice of the challenges heard, and a fold from that step's end to the state at b.
fold_member is the bare fact on `foldBlocks` beneath it. Both leave the state sj from which the step
starts under "there is". `mid_step_at_walk` says which state it is: what the fold returns over pre;
hence `mid_handed` has sj and sk reached; it adds that the rounds' words lie below the prime and
that no mark asked at the place speaks. Neither of the two is called here. Their thr_back_rounds,
thr_back_heard (Johnson/Desc/ProofFile/Honest/Thread/ReachRounds.lean): one step back along the
verifier's fold with the last step's rounds named, AT THE THREAD, where this is at the walk and at
any member in front (more under "Kin" in Johnson/P1K8R/LastStepAtWalk.lean). Ours: `quiet_at_member`
(Johnson/P1K8R/SymbolsAtFrame.lean), whose end is `mid_handed`'s clause on the marks, there at a
list cut in two, here at the step's own rounds; `step_handed`, `two_handed` (LooksAtFrame.lean): the
like at the last member and the last but one, with the two tests of the kind "lookup" in the place
of "no mark speaks".
Limits. That the walk starts and returns, where it stands, which marks are asked and that they have
been silent are premises. What a mark's silence gives is each kind's own matter. Nothing says that
any walk returns.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LooksAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach StepYes fold_split step_less reach_of_fold)
open ProofFile.Honest (Lay ChainProgress Mid Step walk roundsOf Mark markOf marksQuiet walk_len drawsFit)

section
variable {T Cl W Y : Type}

/-- **ANY STEP IN FRONT OF WHERE A WALK STANDS, WITH ITS ROUNDS TIED TO THE CHALLENGES HEARD.** The
walk stands in front of b, which has a round; blk is one of the sub-protocols in front of b, pre
those in front of blk, rest those between blk and b. Then: the verifier's fold over pre returns a
state sj; blk's own step takes sj to a state sk, at rounds R: as many as blk has; their words are
below the prime; they show blk's own stretch of the challenges heard; and the fold over rest takes
sk to the state beside the walk. -/
theorem mid_step_at_walk (L : Lay) (pre rest t : List (Block T Cl)) (blk b : Block T Cl)
    {a z : ChainProgress T Cl W Y} {s₀ s' : T} {m₀ : Option (Mid W Y)} {ss : List (Step W Y)}
    {dA : List Fmt.Drawn} (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L (pre ++ blk :: (rest ++ b :: t)) m₀ (some s₀) front = .ok a)
    (hpos : 0 < b.rounds.length) (hz : walk L ss dA a = .ok z)
    (hl : ss.length = ((pre ++ blk :: rest).flatMap (·.rounds)).length)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (hv : z.ver = some s') :
    ∃ (sj sk : T) (r₁ : List Fmt.RoundView) (c₁ : List Desc.OpenedColumn) (R : List Fmt.RoundView)
      (c : List Desc.OpenedColumn) (r₂ r₃ : List Fmt.RoundView) (c₂ c₃ : List Desc.OpenedColumn),
      foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols = .ok (sj, r₁, c₁) ∧
      R.length = blk.rounds.length ∧ blk.step L.firstTree sj R c = .ok (sk, c.length) ∧
      okRoundsE R = true ∧
      R.map (·.drawn) = (dA.drop (pre.flatMap (·.rounds)).length).take blk.rounds.length ∧
      foldBlocks L.firstTree rest sk r₂ c₂ = .ok (s', r₃, c₃) := by
  have ha' : ChainProgress.start L ((pre ++ blk :: rest) ++ b :: t) m₀ (some s₀) front = .ok a := by
    rw [List.append_assoc]
    exact ha
  obtain ⟨r, c, hf, hdr⟩ := fold_at_walk L (pre ++ blk :: rest) t b hm ha' hpos hz hl hv
  obtain ⟨sj, r₁, c₁, g1, g2⟩ := fold_split L.firstTree (blk :: rest) pre _ _ _ _ hf
  obtain ⟨e1, -⟩ := fold_rest L.firstTree _ _ _ _ _ _ _ g1
  obtain ⟨sk, k, hlen, g3, g4⟩ := foldBlocks_cons L.firstTree blk rest sj r₁ c₁ _ g2
  refine ⟨sj, sk, r₁, c₁, r₁.take blk.rounds.length, c₁.take k, _, _, _, _, g1, hlen,
    step_less g3, ?_, ?_, g4⟩
  · rw [e1]
    exact okRounds_at_walk L _ ha hz hd _ _
  · rw [e1, List.map_take, List.map_drop, hdr]
    rfl

/-- **WHAT THE FRAME's FIELD HANDS, AT ANY MEMBER IN FRONT.** flat: a chain's sub-protocols; A:
those in front of b; blk: the one at number n < A.length. Where the fit's marks at A's members are
among the marks asked, these have been silent at fr, and the walk over A's rounds at fr returns z
with the verifier's state s': blk's own step takes a state sj that is reached at n to a state sk
that is reached at n + 1, at rounds R whose words are below the prime; NO MARK ASKED AT blk's PLACE
SPEAKS AT R's CHALLENGES (in front of them: the challenges heard before); and the fold over the
members between takes sk to s'. -/
theorem mid_handed {P : Type} (flat : List (Block T Cl)) (start : P → T) (zp : P) {n : ℕ}
    {blk : Block T Cl} (hblk : flat[n]? = some blk) (ms : List Mark)
    {A t : List (Block T Cl)} {b : Block T Cl} (hall : flat = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : n < A.length) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress T Cl W Y} {s' : T}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn} {front : List Desc.OpenedColumn}
    (hm : m₀.isSome = true) (ha : ChainProgress.start L flat m₀ (some (start zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ (sj sk : T) (R : List Fmt.RoundView) (c : List Desc.OpenedColumn) (r₂ r₃ : List Fmt.RoundView)
      (c₂ c₃ : List Desc.OpenedColumn), R.length = blk.rounds.length ∧
      blk.step 0 sj R c = .ok (sk, c.length) ∧ okRoundsE R = true ∧
      markOf ms blk.place ([] ++ fr.take ((flat.take n).flatMap (·.rounds)).length)
        (R.map (·.drawn)) = none ∧
      Reach 0 flat start n (zp, sj) ∧ Reach 0 flat start (n + 1) (zp, sk) ∧
      foldBlocks 0 ((flat.take A.length).drop (n + 1)) sk r₂ c₂ = .ok (s', r₃, c₃) := by
  have hA8 : A[n]? = some blk := by
    rw [hall, List.getElem?_append_left hA] at hblk
    exact hblk
  obtain ⟨hi, e8⟩ := List.getElem?_eq_some_iff.1 hA8
  have hsp : A = A.take n ++ blk :: A.drop (n + 1) := by
    conv_lhs => rw [← List.take_append_drop n A, List.drop_eq_getElem_cons hi, e8]
  have htk : A.take n = flat.take n := by
    rw [hall, List.take_append_of_le_length (Nat.le_of_lt hA)]
  have htA : flat.take A.length = A := by
    rw [hall]
    exact List.take_left' rfl
  have hd := elems_of_quiet ms A hfit fr hn hq
  have hl' : ss.length = ((A.take n ++ blk :: A.drop (n + 1)).flatMap (·.rounds)).length := by
    rw [← hsp, ← walk_len L ss fr a z hz]
    exact hn
  have ha' : ChainProgress.start L (A.take n ++ blk :: (A.drop (n + 1) ++ b :: t)) m₀
      (some (start zp)) front = .ok a := by
    have e : A.take n ++ blk :: (A.drop (n + 1) ++ b :: t) = flat := by
      rw [hall]
      conv_rhs => rw [hsp]
      rw [List.append_assoc]
      rfl
    rw [e]
    exact ha
  obtain ⟨sj, sk, r₁, c₁, R, c, r₂, r₃, c₂, c₃, g1, g2, g3, g4, g5, g6⟩ :=
    mid_step_at_walk L _ _ t blk b hm ha' hpos hz hl' hd hv
  rw [hft] at g1 g3 g6
  rw [htk] at g1 g5
  have hq' := hq
  rw [hsp] at hq'
  have hs := Option.isNone_iff_eq_none.1 (quiet_at_member ms _ _ blk [] fr hq')
  rw [htk, ← g5] at hs
  have hle : n ≤ flat.length := by
    rw [hall, List.length_append]
    omega
  have hr := reach_of_fold (start := start) (z := zp) n hle sj _ r₁ _ c₁ g1
  rw [htA]
  exact ⟨sj, sk, R, c, r₂, r₃, c₂, c₃, g2, g3, g4, hs, hr,
    Reach.succ hr hblk ⟨R, c, g2, g3⟩, g6⟩

end

end P1K8

#print axioms P1K8.mid_step_at_walk
#print axioms P1K8.mid_handed
