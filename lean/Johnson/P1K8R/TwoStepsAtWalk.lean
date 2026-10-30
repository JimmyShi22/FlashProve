-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TwoStepsAtWalk.lean: THE HONEST SIDE's WALK (Johnson/Desc/ProofFile/Honest/Walk.lean):
TWO CONSECUTIVE STEPS OF THE VERIFIER's IN FRONT OF WHERE THE WALK STANDS, THE SECOND FROM THE VERY
STATE THAT THE FIRST RETURNS, EACH AT ROUNDS THAT SHOW THE CHALLENGES HEARD AND AT WHICH NO MARK
ASKED AT ITS PLACE SPEAKS. General lemmas: no description, no kind. NONE OF THE LIBRARY's GOALS. A
joining. Nothing on completeness, soundness or hiding.
Why. Two calls of `mid_handed` (Johnson/P1K8R/MidStepAtWalk.lean) at n and n + 1 name two states
behind the first member under two "there is": nothing says that they are one. Where one member's
hearing is read by the next (the lookup on the head's calls, then the head's own rounds) they must
be.

  **`two_steps_at_walk`**   `mid_step_at_walk`'s road with one `foldBlocks_cons` more
  **`pair_handed`**   `mid_handed`'s road; `quiet_at_member` (Johnson/P1K8R/SymbolsAtFrame.lean)
      twice
Kin. THE NEAREST: the frame's authors' made_member, fold_member
(Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean): ONE earlier member's own step on its own
slice of what was heard, and the fold behind it: at the thread, and on the bare fold; neither says
which state the step starts from, so two calls part as two of `mid_handed` do. Further as
Johnson/P1K8R/MidStepAtWalk.lean tells under "Kin"; `last_two_at_walk` (LastStepAtWalk.lean) has two
steps too, the second under the library's `StepYes`, its rounds not tied. THE PROOFS' LINES ARE
`mid_step_at_walk`'s AND `mid_handed`'s, WRITTEN A SECOND TIME WITH ONE MEMBER MORE: these two
follow from the two here by forgetting, but for their last clause, the fold from sk, which wants
blk₂'s step laid in front of the fold from sl again: a lemma, not typed; they are out and kept, and
do not turn for it.
Limits. As in Johnson/P1K8R/MidStepAtWalk.lean: that the walk starts and returns, where it stands,
which marks are asked and that they have been silent are premises. The challenges in front of each
member (f₁, f₂) stand under "there is": no mark of ours reads them. Nothing says that any walk
returns.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.MidStepAtWalk

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

/-- **TWO CONSECUTIVE STEPS IN FRONT OF WHERE A WALK STANDS, EACH WITH ITS ROUNDS TIED TO THE
CHALLENGES HEARD.** As `mid_step_at_walk` (Johnson/P1K8R/MidStepAtWalk.lean), with blk₂ just behind
blk₁: blk₁'s own step takes sj to sk, AND blk₂'s OWN STEP TAKES THAT SAME sk to sl; each at rounds
as many as it has, whose words are below the prime and which show its own stretch of the challenges
heard; the fold over rest takes sl to the state beside the walk. -/
theorem two_steps_at_walk (L : Lay) (pre rest t : List (Block T Cl)) (blk₁ blk₂ b : Block T Cl)
    {a z : ChainProgress T Cl W Y} {s₀ s' : T} {m₀ : Option (Mid W Y)} {ss : List (Step W Y)}
    {dA : List Fmt.Drawn} (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L (pre ++ blk₁ :: blk₂ :: (rest ++ b :: t)) m₀ (some s₀) front = .ok a)
    (hpos : 0 < b.rounds.length) (hz : walk L ss dA a = .ok z)
    (hl : ss.length = ((pre ++ blk₁ :: blk₂ :: rest).flatMap (·.rounds)).length)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (hv : z.ver = some s') :
    ∃ (sj sk sl : T) (r₁ : List Fmt.RoundView) (c₁ : List Desc.OpenedColumn) (R₁ R₂ : List Fmt.RoundView)
      (d₁ d₂ : List Desc.OpenedColumn) (r₂ r₃ : List Fmt.RoundView) (c₂ c₃ : List Desc.OpenedColumn),
      foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols = .ok (sj, r₁, c₁) ∧
      R₁.length = blk₁.rounds.length ∧ blk₁.step L.firstTree sj R₁ d₁ = .ok (sk, d₁.length) ∧
      okRoundsE R₁ = true ∧
      R₁.map (·.drawn) = (dA.drop (pre.flatMap (·.rounds)).length).take blk₁.rounds.length ∧
      R₂.length = blk₂.rounds.length ∧ blk₂.step L.firstTree sk R₂ d₂ = .ok (sl, d₂.length) ∧
      okRoundsE R₂ = true ∧
      R₂.map (·.drawn) = (dA.drop ((pre.flatMap (·.rounds)).length + blk₁.rounds.length)).take
        blk₂.rounds.length ∧
      foldBlocks L.firstTree rest sl r₂ c₂ = .ok (s', r₃, c₃) := by
  have ha' : ChainProgress.start L ((pre ++ blk₁ :: blk₂ :: rest) ++ b :: t) m₀ (some s₀) front = .ok a := by
    rw [List.append_assoc]
    exact ha
  obtain ⟨r, c, hf, hdr⟩ := fold_at_walk L (pre ++ blk₁ :: blk₂ :: rest) t b hm ha' hpos hz hl hv
  obtain ⟨sj, r₁, c₁, g1, g2⟩ := fold_split L.firstTree (blk₁ :: blk₂ :: rest) pre _ _ _ _ hf
  obtain ⟨e1, -⟩ := fold_rest L.firstTree _ _ _ _ _ _ _ g1
  obtain ⟨sk, k, hlen, g3, g4⟩ := foldBlocks_cons L.firstTree blk₁ (blk₂ :: rest) sj r₁ c₁ _ g2
  obtain ⟨sl, k₂, hlen₂, g5, g6⟩ := foldBlocks_cons L.firstTree blk₂ rest sk _ _ _ g4
  refine ⟨sj, sk, sl, r₁, c₁, r₁.take blk₁.rounds.length,
    (r₁.drop blk₁.rounds.length).take blk₂.rounds.length, c₁.take k, (c₁.drop k).take k₂,
    _, _, _, _, g1, hlen, step_less g3, ?_, ?_, hlen₂, step_less g5, ?_, ?_, g6⟩
  · rw [e1]
    exact okRounds_at_walk L _ ha hz hd _ _
  · rw [e1, List.map_take, List.map_drop, hdr]
    rfl
  · rw [e1, List.drop_drop]
    exact okRounds_at_walk L _ ha hz hd _ _
  · rw [e1, List.drop_drop, List.map_take, List.map_drop, hdr]
    rfl

/-- **WHAT THE FRAME's FIELD HANDS, AT TWO CONSECUTIVE MEMBERS IN FRONT.** As `mid_handed`, at the
members blk₁ and blk₂ at numbers n and n + 1 < A.length: sj is reached at n, sk at n + 1, sl at n +
2; blk₁'s own step takes sj to sk and blk₂'s takes THAT sk to sl; at neither's challenges does a
mark asked at its place speak; the fold over the members between takes sl to s'. -/
theorem pair_handed {P : Type} (flat : List (Block T Cl)) (start : P → T) (zp : P) {n : ℕ}
    {blk₁ blk₂ : Block T Cl} (hb₁ : flat[n]? = some blk₁) (hb₂ : flat[n + 1]? = some blk₂)
    (ms : List Mark) {A t : List (Block T Cl)} {b : Block T Cl} (hall : flat = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : n + 1 < A.length) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress T Cl W Y} {s' : T}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn} {front : List Desc.OpenedColumn}
    (hm : m₀.isSome = true) (ha : ChainProgress.start L flat m₀ (some (start zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ (sj sk sl : T) (R₁ R₂ : List Fmt.RoundView) (d₁ d₂ : List Desc.OpenedColumn) (r₂ r₃ : List Fmt.RoundView)
      (c₂ c₃ : List Desc.OpenedColumn) (f₁ f₂ : List Fmt.Drawn),
      R₁.length = blk₁.rounds.length ∧ blk₁.step 0 sj R₁ d₁ = .ok (sk, d₁.length) ∧
      okRoundsE R₁ = true ∧ markOf ms blk₁.place f₁ (R₁.map (·.drawn)) = none ∧
      R₂.length = blk₂.rounds.length ∧ blk₂.step 0 sk R₂ d₂ = .ok (sl, d₂.length) ∧
      okRoundsE R₂ = true ∧ markOf ms blk₂.place f₂ (R₂.map (·.drawn)) = none ∧
      Reach 0 flat start n (zp, sj) ∧ Reach 0 flat start (n + 1) (zp, sk) ∧
      Reach 0 flat start (n + 2) (zp, sl) ∧
      foldBlocks 0 ((flat.take A.length).drop (n + 2)) sl r₂ c₂ = .ok (s', r₃, c₃) := by
  have hA1 : A[n]? = some blk₁ := by
    rw [hall, List.getElem?_append_left (by omega)] at hb₁
    exact hb₁
  have hA2 : A[n + 1]? = some blk₂ := by
    rw [hall, List.getElem?_append_left hA] at hb₂
    exact hb₂
  obtain ⟨hi1, e1⟩ := List.getElem?_eq_some_iff.1 hA1
  obtain ⟨hi2, e2⟩ := List.getElem?_eq_some_iff.1 hA2
  have hsp : A = A.take n ++ blk₁ :: blk₂ :: A.drop (n + 2) := by
    conv_lhs => rw [← List.take_append_drop n A, List.drop_eq_getElem_cons hi1, e1,
      List.drop_eq_getElem_cons hi2, e2]
  have hsp' : A = (A.take n ++ [blk₁]) ++ blk₂ :: A.drop (n + 2) := by
    conv_lhs => rw [hsp]
    rw [List.append_assoc]
    rfl
  have htk : A.take n = flat.take n := by
    rw [hall, List.take_append_of_le_length (by omega)]
  have htA : flat.take A.length = A := by
    rw [hall]
    exact List.take_left' rfl
  have hd := elems_of_quiet ms A hfit fr hn hq
  have hl' : ss.length =
      ((A.take n ++ blk₁ :: blk₂ :: A.drop (n + 2)).flatMap (·.rounds)).length := by
    rw [← hsp, ← walk_len L ss fr a z hz]
    exact hn
  have ha' : ChainProgress.start L (A.take n ++ blk₁ :: blk₂ :: (A.drop (n + 2) ++ b :: t)) m₀
      (some (start zp)) front = .ok a := by
    have e : A.take n ++ blk₁ :: blk₂ :: (A.drop (n + 2) ++ b :: t) = flat := by
      rw [hall]
      conv_rhs => rw [hsp]
      rw [List.append_assoc]
      rfl
    rw [e]
    exact ha
  obtain ⟨sj, sk, sl, r₁, c₁, R₁, R₂, d₁, d₂, r₂, r₃, c₂, c₃, g1, g2, g3, g4, g5, k2, k3, k4,
    k5, g6⟩ := two_steps_at_walk L _ _ t blk₁ blk₂ b hm ha' hpos hz hl' hd hv
  rw [hft] at g1 g3 k3 g6
  rw [htk] at g1
  have hq1 := hq
  rw [hsp] at hq1
  have hs1 := Option.isNone_iff_eq_none.1 (quiet_at_member ms _ _ blk₁ [] fr hq1)
  rw [← g5] at hs1
  have hq2 := hq
  rw [hsp'] at hq2
  have hs2 := Option.isNone_iff_eq_none.1 (quiet_at_member ms _ _ blk₂ [] fr hq2)
  have el : ((A.take n ++ [blk₁]).flatMap (·.rounds)).length =
      ((A.take n).flatMap (·.rounds)).length + blk₁.rounds.length := by
    rw [List.flatMap_append, List.length_append, List.flatMap_singleton]
  rw [el, ← k5] at hs2
  have hle : n ≤ flat.length := by
    rw [hall, List.length_append]
    omega
  have hr := reach_of_fold (start := start) (z := zp) n hle sj _ r₁ _ c₁ g1
  have hr1 := Reach.succ hr hb₁ ⟨R₁, d₁, g2, g3⟩
  rw [htA]
  exact ⟨sj, sk, sl, R₁, R₂, d₁, d₂, r₂, r₃, c₂, c₃, _, _, g2, g3, g4, hs1, k2, k3, k4, hs2, hr,
    hr1, Reach.succ hr1 hb₂ ⟨R₂, d₂, k2, k3⟩, g6⟩

end

end P1K8

#print axioms P1K8.two_steps_at_walk
#print axioms P1K8.pair_handed
