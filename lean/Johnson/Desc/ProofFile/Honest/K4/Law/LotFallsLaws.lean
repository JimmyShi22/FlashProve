-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotFallsLaws.lean: CONDITIONAL.

What is here. Four more laws on `k4LotFalls` (Honest/K4/LotFalls.lean), the list of the falls at
the own members of the layers' own rounds (kind K4). A fall: a test with code, on the verifier's
state in front of a place and that place's own challenges, at which the member there may reject an
honest run, with a stated share (`Fall`, Honest/Side.lean). K4's falls in this list read the
challenges alone. For whoever adds shares up: every fall of the list is `k4Fall Q` at a place at
which the lot lays a half, and bears the one stated share. For whoever spends «no fall has spoken»
at a longer list, in which other kinds' falls stand too: where the falls of such a list at the place
of the lot's own sub-protocol say nothing, the test on the sampled element says nothing (it also
says nothing while that round's challenge has not been heard); the same in the form `fallsBy`
(Honest/Law/FallFree.lean), by the member's number. GENERAL IN THE PUBLIC PART Z AND THE SEGMENTS'
DATA G. Statements with their proofs.

  `k4LotFalls_of_mem`   **the converse of `k4Fall_mem`.**
  `k4LotFalls_share`   every fall of the list bears `k4CoinZeroShare`.
  `coin_of_falls`   **where the falls of a list that holds K4's say nothing at (k4Block x).place,
      `k4CoinZero Q` says nothing.**
  `hf_of_falls`   the same at `fallsBy fs bs j`, where member j of bs bears that place.

Limits. `coin_of_falls` and `hf_of_falls` are CONDITIONAL on hs (the list holds K4's list), hx, hQ
and hF (the three hypotheses of `k4HLot_find`, Law/LotFind.lean) and on the falls' saying nothing;
`hf_of_falls` besides on hb and hp (member j of the list bs bears the place of the lot's own
sub-protocol): no law here shows the two; at the full-size member they follow from LaidK4, and
`hf_head` (Law/HalfHead.lean) has the conclusion there. That these hold at any files is not shown
here. THE SHARE IS A STATED NUMBER: no bound is shown, and nothing is added up here (the first
fall's sentence with the bound as a variable: `k4_coinZero_debt`, Law/Falls.lean). That no two falls
of the list stand at one place is not said here. Nothing on soundness, on completeness or on any
other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LotPlace
import Johnson.Desc.ProofFile.Honest.Law.FallFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block)

/-- **Every fall of the list is `k4Fall Q` at a place at which the lot lays a half.** -/
theorem k4LotFalls_of_mem {S : Type} {Z : Pub} {G : Ground} {f : Fall S}
    (hf : f ∈ k4LotFalls Z G) :
    ∃ (x : Bool × OnBytes.Desc.First.K4.Par) (Q : K4Pub),
      x ∈ k4From Z G G.built.toList 0 none ∧ k4PubOf Z x.2 = some Q ∧ k4TableFits Q = true ∧
        f = k4Fall Q := by
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hf
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, hF⟩ := Option.filter_eq_some_iff.1 hQ'
  exact ⟨x, Q, hx, hQ, hF, rfl⟩

/-- Every fall of the list bears the one stated share. -/
theorem k4LotFalls_share {S : Type} {Z : Pub} {G : Ground} {f : Fall S}
    (hf : f ∈ k4LotFalls Z G) : f.share = k4CoinZeroShare := by
  obtain ⟨_, Q, -, -, -, rfl⟩ := k4LotFalls_of_mem hf
  rfl

/-- CONDITIONAL: on hs and the three hypotheses. **Where the falls of a list that holds K4's say
nothing at the place of the lot's own sub-protocol, the test on the sampled element says nothing.**
-/
theorem coin_of_falls {S : Type} {Z : Pub} {G : Ground} {fs : List (Fall S)}
    (hs : ∀ f ∈ k4LotFalls Z G, f ∈ fs) {x : Bool × OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (hx : x ∈ k4From Z G G.built.toList 0 none) (hQ : k4PubOf Z x.2 = some Q)
    (hF : k4TableFits Q = true) {s : S} {ds : List Fmt.Drawn}
    (h : fallOf fs (k4Block x).place s ds = none) : k4CoinZero Q ds = none :=
  coin_of_fallOf (hs _ (k4Fall_mem hx hQ hF)) (by
    rw [k4Place_block hQ]
    exact h)

/-- CONDITIONAL: on hs, the three hypotheses, hb and hp. **The same by the member's number**: in the
form in which the statements on the member's step ask it. -/
theorem hf_of_falls {S Cl : Type} {Z : Pub} {G : Ground} {fs : List (Fall S)}
    (hs : ∀ f ∈ k4LotFalls Z G, f ∈ fs) {x : Bool × OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (hx : x ∈ k4From Z G G.built.toList 0 none) (hQ : k4PubOf Z x.2 = some Q)
    (hF : k4TableFits Q = true) {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    (hb : bs[j]? = some b) (hp : b.place = (k4Block x).place) :
    ∀ s ds, fallsBy fs bs j s ds = none → k4CoinZero Q ds = none := by
  intro s ds hn
  unfold fallsBy at hn
  rw [hb] at hn
  refine coin_of_falls hs hx hQ hF (s := s) ?_
  rw [← hp]
  exact hn

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4LotFalls_of_mem
#print axioms ProofFile.Honest.K4.k4LotFalls_share
#print axioms ProofFile.Honest.K4.coin_of_falls
#print axioms ProofFile.Honest.K4.hf_of_falls
