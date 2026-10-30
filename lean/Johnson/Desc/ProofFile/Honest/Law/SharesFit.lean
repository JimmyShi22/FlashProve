-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesFit.lean: `StopsFit` (Honest/Law/SharesStops.lean) is
proved, except for its two executable tests (`stopsFit_of`), from three hypotheses: the first
chain's list ends in e₁ (`cut`), e₁ has one round (`one`) and no prover's side (`bare`). Where
`ready` (Honest/Frame.lean) has returned, each prover's side has exactly as many moves as its
sub-protocol has rounds. And where the challenges of some typed verifier's message, read as
Honest/Frame.lean's lists, pass `Draws.due`, the data's three lists are as long as the chains'
declared rounds, the first without the sealing round.

  1  `rounds_sum`, `halves_fit`   each prover's side has as many moves as its sub-protocol has
     rounds
  2  `stopsFit_of`   the main lemma

Limits.
  * That the first chain's last sub-protocol has one round and no prover's side are hypotheses:
    executable tests.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesStops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 S Cl V W Y : Type}

/-! ## 1 Each prover's side has as many moves as its sub-protocol has rounds -/

theorem rounds_sum : ∀ (ps : List (Part V W Y)) (n : Nat),
    ps.foldl (fun n p => n + p.moves.length) n = n + (ps.map (·.moves.length)).sum
  | [], n => (Nat.add_zero n).symm
  | p :: ps, n => by
    show ps.foldl (fun n p => n + p.moves.length) (n + p.moves.length) = _
    rw [rounds_sum ps (n + p.moves.length), List.map_cons, List.sum_cons, Nat.add_assoc]

theorem halves_fit {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss → HalvesFit hs bs
  | [], _, _ => fun _ hb => by cases hb
  | b :: bs, ss, h => by
    have h' : chainSteps B rows look v ([b] ++ bs) hs = .ok ss := h
    rw [chainSteps_append] at h'
    obtain ⟨l₁, hl₁, h'⟩ := exBind_ok h'
    obtain ⟨l₂, hl₂, -⟩ := exMap_ok h'
    intro c hc g hg
    rcases List.mem_cons.1 hc with rfl | hc'
    · unfold chainSteps at hl₁
      by_cases h0 : (c.oracles.length != c.rounds.length) = true
      · rw [if_pos h0] at hl₁
        cases hl₁
      · rw [if_neg h0, hg] at hl₁
        simp only at hl₁
        by_cases h1 : (g.rounds != c.rounds.length) = true
        · rw [if_pos h1] at hl₁
          cases hl₁
        · have h2 : g.rounds = c.rounds.length := by
            cases hq : (g.rounds != c.rounds.length) with
            | true => exact absurd hq h1
            | false => exact bne_eq_false_iff_eq.1 hq
          unfold Placed.rounds at h2
          rw [rounds_sum, Nat.zero_add] at h2
          exact h2
    · exact halves_fit bs l₂ hl₂ c hc' g hg

/-! ## 2 The main lemma -/

/-- **`StopsFit`, from what `ready` has prepared and from a list of challenges that passes
`Draws.due`.** -/
theorem stopsFit_of (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi}
    {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins B}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F B H w₀ rc x k = .ok R)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hρ : (drawsAt C D tF tJ t3 ρ).due F = true)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    (one : e₁.rounds.length = 1)
    (bare : (H.first.find? fun h => h.place == e₁.place) = none) : StopsFit F H D pre₁ e₁ := by
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, -⟩ := hρ
  have q1 := drawsFit_length _ _ d1
  have q2 := drawsFit_length _ _ d2
  have q3 := drawsFit_length _ _ d3
  have q1' : (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++
      ([⟨[], [], [], none⟩] : List Fmt.Drawn)).length =
      (F.first.blocksInOrder.flatMap (·.rounds)).length := q1
  have q2' : (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)).length =
      (F.shared.blocksInOrder.flatMap (·.rounds)).length := q2
  have q3' : (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)).length =
      (F.second.blocksInOrder.flatMap (·.rounds)).length := q3
  rw [List.length_append, drawnT_len, cut, List.flatMap_append, List.length_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, one] at q1'
  rw [drawnT_len] at q2' q3'
  have f1 := halves_fit _ _ s1
  rw [cut] at f1
  exact
    { cut := cut
      bare := bare
      l₁ := Nat.add_right_cancel q1'
      l₂ := q2'
      l₃ := q3'
      f₁ := fun b hb => f1 b (List.mem_append_left _ hb)
      f₂ := halves_fit _ _ s2
      f₃ := halves_fit _ _ s3 }

end ProofFile.Honest

#print axioms ProofFile.Honest.rounds_sum
#print axioms ProofFile.Honest.halves_fit
#print axioms ProofFile.Honest.stopsFit_of
