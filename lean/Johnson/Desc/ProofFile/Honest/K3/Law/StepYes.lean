-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/StepYes.lean: the honest side of the kind "lookup" (K3). From a
sub-protocol's decision on the rounds as they were played to the sub-protocol's step; and two facts
on the run's points. Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("decision", "play", "step", "sub-protocol").

What is shown.
  `DecidesBlind b`: b decides on rounds without digests as on the rounds.
  `blind_via`, `blind_quiet`, `blind_andThen`, `blind_of_decide`: the seated lookup's sub-protocol;
    a sub-protocol without a round; two sub-protocols as one; a sub-protocol with another's
    `decide`.
  `step_yes`: for every such sub-protocol: its step on the played rounds accepts, with s', just
    where its decision on the played rounds does; under the five hypotheses of `step_iff_decide`.
  `theta_take`, `alpha_take`: conditional (one part of keys): the shift and alpha, of the challenges
    in front of any stage behind them, are those of the whole list.

Hypotheses that remain.
  `hb`: (in `step_yes`, `blind_of_decide`) `DecidesBlind b`. `hp`, `hq`: (in `blind_andThen`) the
    same of the two sub-protocols. `h`: (in `blind_of_decide`) b' has b's `decide`.
  `hr`, `ho`, `hy`, `hd`, `hc`: (in `step_yes`) the five of `step_iff_decide`: the half has as many
    rounds as the sub-protocol; a list of oracle messages for each round; the play returns; the
    challenges fit the rounds; the columns read are filled.
  `hp`, `hn`: (in `theta_take`, `alpha_take`) one part of keys; the cut lies behind the round of the
    shift, or of alpha.

How the proof goes. A sub-protocol's step shows `decide` the rounds without the sealed digest; the
frame's lemma `step_iff_decide` (Honest/Law/Cut.lean) says when the step is that decision. The
lookup's sub-protocols decide on rounds without digests as they decide on the rounds
(Honest/K3/Law/NoDigest.lean), so their step is their decision on the rounds that the frame's `play`
yields.

Imported. Honest/Law/Cut.lean.

Users. This file is imported by Honest/K3/Law/StatedBlind.lean.

Limits. That a description's member at a lookup's place is made of these sub-protocols is not shown
here. Shown in part: what `step_yes` asks, `DecidesBlind`, is shown in `theStated_blind`
(Honest/K3/Law/StatedBlind.lean), of the lot's sub-protocol, and in `member_blind`
(Honest/K3/Law/StatedMember.lean), of the guard of that sub-protocol under a name; both are
conditional on there being a sub-protocol at the address. That the description's member is that
guard is, by the head of StatedMember.lean, the library's own equation
(Johnson/Desc/First/K9x/RanAtPure.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.NoDigest
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Place noDigest roundlessBlock OpenedColumn groupsOf regroup)
open ProofFile.Honest.K3.NoDigest (decideVia_noDigest)

variable {S Cl V W X : Type}

/-- b decides on rounds without their sealed digests as it decides on the rounds. -/
def DecidesBlind (b : Block S Cl) : Prop :=
  ∀ s rs gs, b.decide s (rs.map noDigest) gs = b.decide s rs gs

/-- The seated lookup's sub-protocol. -/
theorem blind_via (seat : VerifiableInference.Desc.K3.Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : VerifiableInference.Desc.First.Look.P)
    (guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)) :
    DecidesBlind (VerifiableInference.Desc.K3.Law.blockVia seat piece laid before p guests) :=
  fun s rs _ => decideVia_noDigest seat p s rs

/-- A sub-protocol without a round. -/
theorem blind_quiet (name : String) (chain : Nat) (link : Option Nat) (piece : Nat)
    (f : S → Except String S) : DecidesBlind (roundlessBlock (Cl := Cl) name chain link piece f) :=
  fun _ _ _ => rfl

/-- Two sub-protocols as one. -/
theorem blind_andThen (name : String) {p q : Block S Cl} (hp : DecidesBlind p)
    (hq : DecidesBlind q) : DecidesBlind (Block.andThen name p q) := by
  intro s rs gs
  show (p.decide s ((rs.map noDigest).take p.rounds.length) (gs.take p.openings)).bind (fun s' =>
      q.decide s' ((rs.map noDigest).drop p.rounds.length) (gs.drop p.openings)) =
    (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun s' =>
      q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)
  rw [← List.map_take, ← List.map_drop, hp]
  congr 1
  funext s'
  exact hq _ _ _

/-- A sub-protocol that has another's `decide` (other tests on the plan, other runs of claims). -/
theorem blind_of_decide {b b' : Block S Cl} (h : b'.decide = b.decide) (hb : DecidesBlind b) :
    DecidesBlind b' := by
  intro s rs gs
  rw [h]
  exact hb s rs gs

/-- **The step on the played rounds is the decision on the played rounds.** The five hypotheses are
those of `step_iff_decide`. -/
theorem step_yes {g : Placed V W X} {b : Block S Cl} {v : Option V} {c : RowCoins g.parts}
    {ds : List Fmt.Drawn} {m : Mid W X} {y : List Played × Mid W X} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {cols : List OpenedColumn} (s s' : S) (hb : DecidesBlind b)
    (hr : g.rounds = b.rounds.length) (ho : b.oracles.length = b.rounds.length)
    (hy : play (g.steps b v c) ds [] m = .ok y) (hd : drawsFit b.rounds ds = true)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    b.step ft s (roundsOf y.1) cols = .ok (s', cols.length) ↔
      b.decide s (roundsOf y.1) (regroup ((groupsOf ft b.rounds ds).map (·.length)) cols) =
        .ok s' := by
  rw [step_iff_decide s s' hr ho hy hd hc, hb]

/-! ## The shift and alpha, of the challenges in front of a stage -/

theorem theta_take (f : LFace) (v : Nat) (hp : f.parts = [v]) (front ds : List Fmt.Drawn) {n : Nat}
    (hn : oAlpha f ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).theta =
      (ptsOf f front.length (front ++ ds)).theta := by
  show (if f.shifted then elemAt (front ++ ds.take n) (roundAt f front.length .shift) else _) =
    (if f.shifted then elemAt (front ++ ds) (roundAt f front.length .shift) else _)
  by_cases hs : f.shifted = true
  · have h1 : oAlpha f = 1 := by simp [oAlpha, hs]
    simp only [if_pos hs]
    exact elemAt_take front ds n _ (by unfold roundAt; rw [fr_shift f v hp hs]; omega)
  · simp only [if_neg hs]

theorem alpha_take (f : LFace) (v : Nat) (hp : f.parts = [v]) (front ds : List Fmt.Drawn) {n : Nat}
    (hn : oAlpha f + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).alpha =
      (ptsOf f front.length (front ++ ds)).alpha :=
  elemAt_take front ds n _ (by unfold roundAt; rw [fr_alpha f v hp]; omega)

#print axioms ProofFile.Honest.K3.Law.blind_via
#print axioms ProofFile.Honest.K3.Law.blind_quiet
#print axioms ProofFile.Honest.K3.Law.blind_andThen
#print axioms ProofFile.Honest.K3.Law.blind_of_decide
#print axioms ProofFile.Honest.K3.Law.step_yes
#print axioms ProofFile.Honest.K3.Law.theta_take
#print axioms ProofFile.Honest.K3.Law.alpha_take

end ProofFile.Honest.K3.Law
