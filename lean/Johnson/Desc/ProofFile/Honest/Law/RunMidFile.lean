-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunMidFile.lean: the state of a run of `runC` before a called
part, at a file. The lemmas of Honest/Law/RunMid.lean and Honest/Law/WalkMid.lean on one chain are
applied to the three chains of a run of `runC` (Honest/Walk.lean). At the address of a part that was
called, `midAtW` or `midSharedAtW` (Honest/MidW.lean: the walk's own state) returns a state, and
what it has seen is what the chain's start had seen and the rounds produced before the part
(`mid_first`, `mid_shared`, `mid_second`). Two more hypotheses: each `Step` of the three chains has
as many oracle messages as its entry counts roots; and the rounds at the address are one consecutive
stretch of the chain's (`hseg`; only that no round before stands at the address is used, and that
holds of `takeWhile` without it: `hseg` is idle).

  1  `told_behind`   a called part has a real round (one that a prover's side made: `told`) after
     the rounds before the address
  2  `mid_first`, `mid_shared`, `mid_second`   the three chains

Limits.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `mid_first`, `mid_shared`, `mid_second`; `FileDescription.placesOk` (the library's executable test):
    `mid_first`, `mid_shared`, `mid_second`.
  * Nothing is said of `midAt` and `midSharedAt` (Honest/Frame.lean), which play the rounds by
    `play` and hand no columns (Honest/GapAt.lean compares the two, where every step before the
    address is blind).
  * Nothing is said on the state's field `opened` (Honest/Gap.lean `midAtW_some`;
    Honest/WalkOpened.lean `ChainProgress.Inv`).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.WalkMid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W Y W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 A real round after the rounds before the address -/

/-- On a run's rounds at an address of one chain: where the part was called, there is a real round
(`told`) among that chain's rounds after the n before the address. -/
theorem told_behind {F : FileDescription Xi} {r : RunC F} {a : Addr} {ch : Nat} {pl : List Played}
    {ss : List (Step W Y)} {ds : List Fmt.Drawn} {n len : Nat} (hA : At r.run a ch pl ss ds)
    (hs : InStretch ss a n len) (hc : r.called a = true)
    (hoth : ∀ p ∈ r.run.played.1 ++ r.run.played.2.1 ++ r.run.played.2.2, p.isAt a = true →
      p ∈ pl) : ∃ p ∈ pl.drop n, p.told = true := by
  obtain ⟨p, hp, e⟩ := List.any_eq_true.1 hc
  rw [Bool.and_assoc, Bool.and_eq_true] at e
  have hat : p.isAt a = true := e.2
  have hpl := hoth p hp hat
  have hsplit : p ∈ pl.take n ++ pl.drop n := by
    rw [List.take_append_drop]
    exact hpl
  rcases List.mem_append.1 hsplit with h1 | h2
  · have M := laidAs_mask hA.laid a
    have m1 : (pl.take n).map (·.isAt a) = (ss.take n).map fun s => s.addr == a := by
      rw [List.map_take, List.map_take, M]
    have h3 := all_of_map m1 hs.front p h1
    rw [hat] at h3
    cases h3
  · exact ⟨p, h2, e.1⟩

/-! ## 2 The three chains -/

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
  (o₁ : ∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots)
  (o₂ : ∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots)
  (o₃ : ∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) (hp : F.placesOk = true)
include h hR o₁ o₂ o₃ hp

/-- **`midAtW` at a called part of the first chain**: it returns a state, which has seen the chain's
rounds before the address. -/
theorem mid_first {a : Addr} (ha : R.first.any (·.addr == a) = true)
    (hseg : (R.first.drop (R.first.takeWhile fun s => s.addr != a).length).take
      (R.first.filter fun s => s.addr == a).length = R.first.filter fun s => s.addr == a)
    (hc : r.called a = true) :
    ∃ m, midAtW F B H w₀ rc x c ρ a = .ok (some m) ∧
      m.seen = roundsOf (r.run.played.1.take (R.first.takeWhile fun s => s.addr != a).length) := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_first h hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA (stretch_of R.first a hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · exact g
      · rw [all_of_map (laidAs_mask l2 a) (off_chain (by decide) c1 c2 ha) p g] at hat
        cases hat
    · rw [all_of_map (laidAs_mask l3 a) (off_chain (by decide) c1 c3 ha) p g] at hat
      cases hat)
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, -, -, -, -, -, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  obtain ⟨y, w1, w2, l1, l2⟩ := walk_cut (start_laid ha₁) hz₁
    (R.first.takeWhile fun s => s.addr != a).length (List.takeWhile_prefix _).length_le
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (told_live _ _ _ y z₁ _ w2 l2 hb)
  refine ⟨m, ?_, ?_⟩
  · unfold midAtW
    simp only [hR, ha₁, Except.bind]
    rw [if_pos ha]
    exact (midInW_of ha w1).trans (by rw [hm])
  · rw [(walk_mid ha₁ w1 hm).2.2, l1]
    rfl

/-- **`midSharedAtW` at a called part of the shared chain**: it returns a state, which has seen the
chain's rounds before the address. -/
theorem mid_shared {a : Addr} (ha : R.shared.any (·.addr == a) = true)
    (hseg : (R.shared.drop (R.shared.takeWhile fun s => s.addr != a).length).take
      (R.shared.filter fun s => s.addr == a).length = R.shared.filter fun s => s.addr == a)
    (hc : r.called a = true) :
    ∃ m, midSharedAtW F B H w₀ rc x c ρ a = .ok (some m) ∧
      m.seen =
        roundsOf (r.run.played.2.1.take (R.shared.takeWhile fun s => s.addr != a).length) := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_shared h hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA (stretch_of R.shared a hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 a) (off_chain (by decide) c2 c1 ha) p g] at hat
        cases hat
      · exact g
    · rw [all_of_map (laidAs_mask l3 a) (off_chain (by decide) c2 c3 ha) p g] at hat
      cases hat)
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', -, -, -, ha₂, hz₂, -, -, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  obtain ⟨y, w1, w2, l1, l2⟩ := walk_cut (start_laid ha₂) hz₂
    (R.shared.takeWhile fun s => s.addr != a).length (List.takeWhile_prefix _).length_le
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (told_live _ _ _ y z₂ _ w2 l2 hb)
  refine ⟨m, ?_, ?_⟩
  · unfold midSharedAtW
    simp only [hR, ha₂, Except.bind]
    exact (midInW_of ha w1).trans (by rw [hm])
  · rw [(walk_mid ha₂ w1 hm).2.2, l1]
    rfl

/-- **`midAtW` at a called part of the second chain**: it returns a state, which has seen all rounds
of the two earlier chains and the second chain's rounds before the address. -/
theorem mid_second {a : Addr} (ha : R.second.any (·.addr == a) = true)
    (hseg : (R.second.drop (R.second.takeWhile fun s => s.addr != a).length).take
      (R.second.filter fun s => s.addr == a).length = R.second.filter fun s => s.addr == a)
    (hc : r.called a = true) :
    ∃ m, midAtW F B H w₀ rc x c ρ a = .ok (some m) ∧
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take (R.second.takeWhile fun s => s.addr != a).length) := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_second h hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA (stretch_of R.second a hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 a) (off_chain (by decide) c3 c1 ha) p g] at hat
        cases hat
      · rw [all_of_map (laidAs_mask l2 a) (off_chain (by decide) c3 c2 ha) p g] at hat
        cases hat
    · exact g)
  have hnot : R.first.any (·.addr == a) = false := by
    rw [List.any_eq_false]
    intro s hs
    rw [off_chain (by decide) c3 c1 ha s hs]
    exact Bool.false_ne_true
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  obtain ⟨y, w1, w2, l1, l2⟩ := walk_cut (start_laid ha₃) hz₃
    (R.second.takeWhile fun s => s.addr != a).length (List.takeWhile_prefix _).length_le
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (told_live _ _ _ y z₃ _ w2 l2 hb)
  -- at the end of the two earlier chains the prover's run was still going on
  obtain ⟨m₀, _, e0, -⟩ := start_live ha₃ (walk_live _ _ _ a₃ y m w1 hm)
  have ha₃₀ := ha₃
  have hno : ¬ R.first.any (·.addr == a) = true := by
    rw [hnot]
    exact Bool.false_ne_true
  cases hm₁ : z₁.mid with
  | none =>
    rw [hm₁] at e0
    cases e0
  | some m₁ =>
    cases hm₂ : z₂.mid with
    | none =>
      rw [hm₁, hm₂] at e0
      cases e0
    | some m₂ =>
      rw [hm₁, hm₂] at e0 ha₃
      have q1 := (walk_mid ha₁ hz₁ hm₁).2.2
      have q2 := (walk_mid ha₂ hz₂ hm₂).2.2
      have ha₃' : ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
          F.second.blocksInOrder (some (R.start₃ H m₁ m₂)) (door₃ F x z₁.ver z₂.ver)
          (z₁.cols ++ z₂.cols) = .ok a₃ := ha₃
      refine ⟨m, ?_, ?_⟩
      · unfold midAtW
        simp only [hR, ha₁, Except.bind]
        rw [if_neg hno]
        simp only [hz₁, hq, ha₂, hz₂, ha₃₀, Bool.not_true, Bool.false_eq_true, if_false]
        exact (midInW_of ha w1).trans (by rw [hm])
      · rw [(walk_mid ha₃' w1 hm).2.2, l1]
        show (m₁.seen ++ m₂.seen) ++ _ = _
        rw [q1, q2]
        rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.told_behind
#print axioms ProofFile.Honest.mid_first
#print axioms ProofFile.Honest.mid_shared
#print axioms ProofFile.Honest.mid_second
