-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/StepOut.lean: THE LAST STEP OUT OF "REACHED BY THE WRAPPED SUB-PROTOCOLS" (`Reach`
over `below`, Johnson/Top/H0/Walk/Reach.lean, Johnson/Desc/Sound/ChainRule.lean): IT IS AN ACCEPTING
STEP OF THE SUB-PROTOCOL ITSELF AT ROUNDS WHOSE WORDS LIE BELOW THE PRIME. General in the list of
sub-protocols, the state and the start. Two lemmas; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

  **`stepYes_words`**   one step: step_ok_iff (Johnson/Desc/Sound/RunIsDecide.lean), below_yes,
      okWords_of_view (Johnson/Desc/Sound/PieceYes.lean)
  **`reach_last_words`**   the last step of a reached state
Kin. THE NEAREST: seat_yes, reach_last, group_of_reach (Johnson/Loose/H2K12/GroupAt354.lean): at one
seat, at the level of `decide`: the same first lines (step_ok_iff, below_yes with both halves kept),
ending in viewWordsBelowPrime; the case split on "reached"; and a law under this file's very premises. None ends
in the member's own step with `okRoundsE`. The seal's `stepYes_raw` (Reach.lean): the same proof,
the words dropped. reach_pred (Johnson/Road/K4/FunsThirdReached.lean): the last step of any reached
state, as `StepYes`. rchAt_inv_below (Johnson/Top/H0/Walk/ReachInv.lean): an induction along the
wrapped family with such a step in hand. Johnson/Top/H/K3PieceHears.lean: the same two calls
(below_yes, okWords_of_view) at one kind's decide. keepsD_below, prop_of_reach
(Johnson/Top/H0/K2Hands/SampleReach.lean): another road out of the wrapped family: an invariant
carried along. In our own house, beside the seal: Johnson/Desc/K8/Honest/ZyBelowAtWrap.lean takes
the like step at the level of `decide`, for one kind's block.
Limits. WHAT IT IS FOR: laws that take "an accepting step of the member" and "the rounds pass the
test on words" as premises can be called at the states that the frame of the honest side hands.
Nothing says that any state is reached. Of the opened columns' words, which the wrapper tests too,
nothing is kept.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.Walk.Reach
import Johnson.Top.H.K3LawKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn noDigest)
open VerifiableInference.Desc.Sound
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

section
variable {S Cl P : Type}

/-- **An accepting step of `below b` is one of b at rounds whose words lie below the prime.**
`stepYes_raw` (Johnson/Top/H0/Walk/Reach.lean) with what it drops kept. -/
theorem stepYes_words {ft : ℕ} {b : Block S Cl} {s s' : S} (h : StepYes ft (below b) s s') :
    ∃ (R : List Fmt.RoundView) (c : List OpenedColumn), R.length = b.rounds.length ∧
      b.step ft s R c = .ok (s', c.length) ∧ okRoundsE R = true := by
  obtain ⟨R, c, hR, e⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := (step_ok_iff ft (below b) s s' R c c.length).1 e
  obtain ⟨hk, hd⟩ := below_yes b _ _ _ _ h4
  refine ⟨R, c, hR, (step_ok_iff ft b s s' R c c.length).2 ⟨h1, h2, h3, hd⟩, ?_⟩
  have hw : ((R.map noDigest).all fun r =>
      r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)) = true :=
    okWords_of_view _ hk
  unfold okRoundsE
  rw [List.all_eq_true] at hw ⊢
  exact fun r hr => hw (noDigest r) (List.mem_map_of_mem hr)

/-- **THE LAST STEP OUT OF "REACHED BY THE WRAPPED SUB-PROTOCOLS"**: what these reach at k + 1 comes
of what they reach at k by an accepting step of the k-th sub-protocol ITSELF, at as many rounds as
it declares, at columns all of which it reads, AND AT ROUNDS THAT PASS THE LIBRARY's TEST ON WORDS
(`okRoundsE`, Johnson/Top/H/K3LawKind.lean). -/
theorem reach_last_words {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {k : ℕ} {z : P}
    {s' : S} (h : Reach ft (bs.map below) start (k + 1) (z, s')) {b : Block S Cl}
    (hb : bs[k]? = some b) :
    ∃ (s : S) (R : List Fmt.RoundView) (c : List OpenedColumn), Reach ft (bs.map below) start k (z, s) ∧
      R.length = b.rounds.length ∧ b.step ft s R c = .ok (s', c.length) ∧
      okRoundsE R = true := by
  cases h with
  | succ hr hbk hy =>
    rw [List.getElem?_map, hb] at hbk
    obtain rfl := Option.some.inj hbk
    obtain ⟨R, c, h1, h2, h3⟩ := stepYes_words hy
    exact ⟨_, R, c, hr, h1, h2, h3⟩

end

end P1K8

#print axioms P1K8.stepYes_words
#print axioms P1K8.reach_last_words
