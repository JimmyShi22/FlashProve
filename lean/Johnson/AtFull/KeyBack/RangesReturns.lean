-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/RangesReturns.lean: WHERE `Key.rangesNumbers m` RETURNS, AND WHAT. General in
m: no written value stands here.

IT TAKES A RETURN TO GIVE A RETURN. `Key.rangesNumbers` (Johnson/Desc/Key/Ranges.lean) can refuse at
four places. One of them cannot happen, by the rule's text. The other three stay as premises:
  h₀ `treesSent` returns at the key file's first chain;
  hb the first chain's plan has a round named "BAT", the first of them at i;
  hg `rangesGuard m i`: two stages or more, and the names from i on are those that the stages ask.
None of the three is shown at any m here.

  `rangesFirst ts`, `onceOpens_head`: the head of the rule's list for a key file's first chain: the
    list is a cons by its text, so the second place cannot refuse.
  `rangesGuard m i`: the routine's own last test, at the place i.
  `rangesAt m t₀ i`: the numbers that the routine returns: its own closing text, at the trees t₀ and
    the place i.
  `rangesNumbers_eq`: from h₀, hb, hg: `Key.rangesNumbers m = .ok (rangesAt m t₀ i)`.
  `rangesNumbers_returns`: so it returns. Here h₀ is taken at every words for a refusal, as
    `TreesK.first` (Core.lean) gives it.
  `rangesNumbers_only`: the way back: a return gives h₀ (at the routine's own words), hb, hg and the
    value. So the three premises of `rangesNumbers_eq` ask no more than the routine does.
Limits. No m is shown at which the premises hold. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- The trees that the first round of positions of a key file's first chain opens. -/
def rangesFirst (ts : List (Sent × Nat)) : List Told :=
  (ts.filter fun t => t.1.tag == .multiplicities).map (ownAt 0)

/-- The rule's list for a key file's first chain has a head, whatever the trees. -/
theorem onceOpens_head (ts : List (Sent × Nat)) : (onceOpens ts).head? = some (rangesFirst ts) :=
  rfl

/-- `Key.rangesNumbers`' last test, at the place i. -/
def rangesGuard (m : Made) (i : Nat) : Bool :=
  decide (2 ≤ m.p.chains.made.sized.key.ranges.x.stages.length) &&
    (((plan₀ m).rounds.drop i).take
      (1 + H2U.towerLen m.p.chains.made.sized.key.ranges.x.stages)).map (·.name) ==
      "BAT" :: H2U.towerNames m.p.chains.made.sized.key.ranges.x.stages

/-- The numbers that `Key.rangesNumbers m` returns, at the first chain's trees t₀ and the place i of
its first round named "BAT". -/
def rangesAt (m : Made) (t₀ : List (Sent × Nat)) (i : Nat) : H2U.PlaceNums :=
  { chain := 1, start := i
    nums :=
      { rows := Wf.rowsBatched m.p.chains.made.sized.key.ranges.x
          m.p.chains.made.sized.key.ranges.matrix
        work := m.p.chains.made.sized.set.workOf .query .once
        stages := m.p.chains.made.sized.key.ranges.test.stages.map H2U.stageNums
        ownMask := !m.p.chains.made.sized.key.ranges.x.choice.masksRide
        first := rangesFirst t₀
        free := (((plan₀ m).rounds.take i).map (·.roots)).foldl (· + ·) 0
        firstTree := 0 }
    idx := m.p.chains.made.sized.key.ranges.x.stages.map fun s => (s.code, s.maskCode)
    firstGroup := 1
    answers := m.p.chains.made.sized.set.samples
    early := m.p.chains.made.sized.key.ranges.x.choice.masksRide }

/-- **What `Key.rangesNumbers m` returns**, from the three steps that can refuse. -/
theorem rangesNumbers_eq (m : Made) (t₀ : List (Sent × Nat)) (i : Nat)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (hb : (H2U.batPlaces (plan₀ m).rounds).head? = some i)
    (hg : rangesGuard m i = true) :
    rangesNumbers m = .ok (rangesAt m t₀ i) := by
  unfold rangesNumbers
  dsimp only
  refine bind_of_ok h₀ ?_
  rw [onceOpens_head, hb]
  dsimp only
  refine bind_of_ok (a := rangesFirst t₀) rfl ?_
  refine bind_of_ok (a := i) rfl ?_
  exact (if_pos hg).trans rfl

/-- **r2: `Key.rangesNumbers m` returns**, from these three. -/
theorem rangesNumbers_returns (m : Made) (t₀ : List (Sent × Nat)) (i : Nat)
    (h₀ : ∀ a, treesSent a m.key.1 (plan₀ m) [] = .ok t₀)
    (hb : (H2U.batPlaces (plan₀ m).rounds).head? = some i)
    (hg : (decide (2 ≤ m.p.chains.made.sized.key.ranges.x.stages.length) &&
      (((plan₀ m).rounds.drop i).take
        (1 + H2U.towerLen m.p.chains.made.sized.key.ranges.x.stages)).map (·.name) ==
        "BAT" :: H2U.towerNames m.p.chains.made.sized.key.ranges.x.stages) = true) :
    ∃ N, rangesNumbers m = .ok N :=
  ⟨_, rangesNumbers_eq m t₀ i (h₀ _) hb hg⟩

/-- **The way back**: a return gives the three premises, and the value. -/
theorem rangesNumbers_only (m : Made) (N : H2U.PlaceNums) (h : rangesNumbers m = .ok N) :
    ∃ (t₀ : List (Sent × Nat)) (i : Nat),
      treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀ ∧
      (H2U.batPlaces (plan₀ m).rounds).head? = some i ∧
      rangesGuard m i = true ∧ N = rangesAt m t₀ i := by
  unfold rangesNumbers at h
  dsimp only at h
  obtain ⟨t₀, h₀, h₁⟩ := ok_of_bind h
  rw [onceOpens_head] at h₁
  dsimp only at h₁
  obtain ⟨first, hf, h₂⟩ := ok_of_bind h₁
  obtain rfl : rangesFirst t₀ = first := Except.ok.inj hf
  cases hb : (H2U.batPlaces (plan₀ m).rounds).head? with
  | none =>
    rw [hb] at h₂
    dsimp only at h₂
    obtain ⟨_, hy, _⟩ := ok_of_bind h₂
    exact nomatch hy
  | some i =>
    rw [hb] at h₂
    dsimp only at h₂
    obtain ⟨j, hj, h₃⟩ := ok_of_bind h₂
    obtain rfl : i = j := Except.ok.inj hj
    split at h₃
    · rename_i hg
      obtain ⟨_, _, h₄⟩ := ok_of_bind h₃
      exact ⟨t₀, i, h₀, rfl, hg, (Except.ok.inj h₄).symm⟩
    · obtain ⟨_, hy, _⟩ := ok_of_bind h₃
      exact nomatch hy

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.onceOpens_head
#print axioms Johnson.AtFull.KeyBack.rangesNumbers_eq
#print axioms Johnson.AtFull.KeyBack.rangesNumbers_returns
#print axioms Johnson.AtFull.KeyBack.rangesNumbers_only
