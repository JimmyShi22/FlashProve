-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotPlace.lean: CONDITIONAL.

What is here. THE PLACE OF A HALF OF THE LOT OF THE LAYERS' OWN ROUNDS (kind K4) IS THE PLACE OF THE
LOT's OWN SUB-PROTOCOL. Law/LotFind.lean finds the lot's half at `k4Place Q`, the place written off
the public data Q; a description's member bears the place of the lot's sub-protocol `k4Block x`
(Johnson/Desc/ProofFile/Lot/K4.lean). Here the two are one place wherever `k4PubOf` returns Q at x's
parameters, and `k4HLot_find` is said again at that place. GENERAL IN THE PUBLIC PART Z AND THE
SEGMENTS' DATA G: nothing here is bound to a size, and nothing here names a hash function. Beside it
one law on lists of falls, general in the fall: where the falls at a fall's own place say nothing,
that fall's test says nothing. Statements with their proofs.

  `k4PubOf_piece`, `k4PubOf_place`   the public data's piece and place are the parameters'.
  `k4Place_block`   **k4Place Q = (k4Block x).place.**
  `k4HLot_find_block`   **the lot's half at the sub-protocol's own place.**
  `test_of_fallOf`   from f ∈ fs and fallOf fs f.place s ds = none: f.test s ds = none.
  `coin_of_lotFalls`   `coin_of_fallOf` (Law/LotFind.lean) at the list `k4LotFalls`. At every list
      that holds that one, and at the sub-protocol's own place: `coin_of_falls`,
      Law/LotFallsLaws.lean.

Limits. CONDITIONAL: `k4Place_block` on hQ (`k4PubOf` returns Q at x's parameters);
`k4HLot_find_block` and `coin_of_lotFalls` on the three hypotheses of `k4HLot_find`: hx (x is among
the places at which the lot lays a sub-protocol), hQ and hF (`k4TableFits` accepts Q). That any of
the three holds at any files is not shown here. That a description's member at that place IS the
lot's sub-protocol is not said here: the makers of a description wrap it. Nothing on what a half
sends. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LotFind
import Johnson.Desc.ProofFile.Honest.K4.LotFalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest

variable {W₀ Rc Tr X : Type}

/-- The public data's piece is the parameters'. -/
theorem k4PubOf_piece {Z : Pub} {p : OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (h : k4PubOf Z p = some Q) : Q.piece = p.piece := by
  unfold k4PubOf at h
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- The public data's place, in the parameters' letters. -/
theorem k4PubOf_place {Z : Pub} {p : OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (h : k4PubOf Z p = some Q) :
    k4Place Q = { chain := 1, link := some p.link, piece := p.piece, kind := .K4 } := by
  unfold k4Place
  rw [k4PubOf_link h, k4PubOf_piece h]

/-- CONDITIONAL: on hQ. **THE HALF's PLACE IS THE PLACE OF THE LOT's OWN SUB-PROTOCOL.** -/
theorem k4Place_block {Z : Pub} {x : Bool × OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (hQ : k4PubOf Z x.2 = some Q) : k4Place Q = (k4Block x).place :=
  (k4PubOf_place hQ).trans (k4Block_place x).symm

/-- CONDITIONAL: on the three hypotheses. **THE LOT's HALF AT THE SUB-PROTOCOL's OWN PLACE.** -/
theorem k4HLot_find_block (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) {Z : Pub}
    {G : Ground} {x : Bool × OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (hx : x ∈ k4From Z G G.built.toList 0 none) (hQ : k4PubOf Z x.2 = some Q)
    (hF : k4TableFits Q = true) :
    ((k4HLot (Rc := Rc) (X := X) cells weights look).halves Z G).find?
      (fun z => z.place == (k4Block x).place) =
      some (k4Half cells weights k4Tokens (look Z G) Q) := by
  rw [← k4Place_block hQ]
  exact k4HLot_find cells weights look hx hQ hF

/-- **Where the falls at a fall's own place say nothing, that fall's test says nothing.** General in
the fall and in the list. -/
theorem test_of_fallOf {S : Type} {fs : List (Fall S)} {f : Fall S} (hm : f ∈ fs) {s : S}
    {ds : List Fmt.Drawn} (h : fallOf fs f.place s ds = none) : f.test s ds = none := by
  unfold fallOf at h
  rw [List.findSome?_eq_none_iff] at h
  exact h f (List.mem_filter.2 ⟨hm, beq_self_eq_true f.place⟩)

/-- CONDITIONAL: on the three hypotheses. **Where the falls of `k4LotFalls`
(Honest/K4/LotFalls.lean) at the place say nothing, the test on the sampled element says nothing.**
-/
theorem coin_of_lotFalls {S : Type} {Z : Pub} {G : Ground}
    {x : Bool × OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (hx : x ∈ k4From Z G G.built.toList 0 none) (hQ : k4PubOf Z x.2 = some Q)
    (hF : k4TableFits Q = true) {s : S} {ds : List Fmt.Drawn}
    (h : fallOf (k4LotFalls Z G) (k4Place Q) s ds = none) : k4CoinZero Q ds = none :=
  coin_of_fallOf (k4Fall_mem hx hQ hF) h

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4PubOf_piece
#print axioms ProofFile.Honest.K4.k4PubOf_place
#print axioms ProofFile.Honest.K4.k4Place_block
#print axioms ProofFile.Honest.K4.k4HLot_find_block
#print axioms ProofFile.Honest.K4.test_of_fallOf
#print axioms ProofFile.Honest.K4.coin_of_lotFalls
