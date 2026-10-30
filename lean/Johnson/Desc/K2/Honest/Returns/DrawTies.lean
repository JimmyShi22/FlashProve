-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/DrawTies.lean: OF THE TWO TIES OF THE PLAN's NUMBERS TO THE SENDING's
PUBLIC LETTER UNDER WHICH ROUNDS THAT FIT GIVE WHAT THE LAW ASKS OF THE DRAWS (`rounds_give`,
Returns/DrawFits.lean), THE SECOND FOLLOWS FROM THE FIRST ENTRY's TEST ON THE PLAN (`planOk1`,
Johnson/Desc/Sending/Send.lean), WHICH THE LAW's PREMISES HOLD ALREADY. Statements and proofs.

  `max_skips` a greatest count of answers, taken from 0 on, does not feel the shapes without an
                    answer
  `answersMax_seeds` so the greatest count of answers among the announced messages is the letter's
                    number of seeds
  `nonZero_of_entry` the entry's test says that the plan marks as many draws "never 0" as that:
                    p.nonZero = seeds
  `call_draws` SO, AT A FRONT: rounds that fit the kind's rounds, the entry's test and ONE tie
                    (p.seeds = seeds * (coordinates + 1)) give the five: the positions' range · the
                    count of the first round's elements · no position and no matrix entry there · no
                    seed's factor is spelt by three words 0

Limits. THE ONE TIE THAT IS LEFT IS A PREMISE: no test of the kind gives it. The kind's own decision
runs no `roundsFit`: `Block.step` does, in front of it: so the structures of premises on the
decision (`LinkPlain`, `SwitchPlain`) keep the five. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.DrawFits
import Johnson.Desc.K2.Honest.Returns.LinkSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit)
open VerifiableInference.Desc.First.K2 (P2 rounds par9)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Desc.Plain (answersMax)
open _root_.Tw.K2 (Front switchNotices)

theorem max_skips : ∀ (l : List OracleNotice) (a : Nat),
    ((l.map (·.shape)).filter (·.answers != 0)).foldl (fun a s => max a s.answers) a =
      l.foldl (fun a n => max a n.shape.answers) a
  | [], _ => rfl
  | n :: l, a => by
    by_cases h : n.shape.answers = 0
    · have hf : ((n :: l).map (·.shape)).filter (·.answers != 0) =
          (l.map (·.shape)).filter (·.answers != 0) := by
        rw [List.map_cons, List.filter_cons_of_neg (by simp [h])]
      rw [hf, List.foldl_cons, h, Nat.max_zero]
      exact max_skips l a
    · have hf : ((n :: l).map (·.shape)).filter (·.answers != 0) =
          n.shape :: (l.map (·.shape)).filter (·.answers != 0) := by
        rw [List.map_cons, List.filter_cons_of_pos (by simp [h])]
      rw [hf, List.foldl_cons, List.foldl_cons]
      exact max_skips l _

theorem answersMax_seeds (Z : K1.Par) : answersMax Z.sent = Z.seeds := by
  unfold answersMax K1.Par.seeds K1.Par.tuple
  rw [← Array.foldl_toList, max_skips]

theorem nonZero_of_entry (p : P2) (Z : K1.Par) (sent : Array OracleNotice) (hs : Z.sent = sent)
    (h : planOk1 none sent (par9 p).eSeed = true) : p.nonZero = Z.seeds := by
  simp only [planOk1, Bool.and_eq_true, beq_iff_eq] at h
  rw [← answersMax_seeds, hs]
  exact h.1.2

/-- **At a front: rounds that fit, the entry's test and one tie give what the law asks of the
draws.** -/
theorem call_draws (p : P2) (x : Front) (r₁ r₂ : Fmt.RoundView)
    (hE : p.seeds = (sendingAt p x).seeds * ((sendingAt p x).coordinates + 1))
    (he : planOk1 none (switchNotices x.T x.others) (par9 p).eSeed = true)
    (h : roundsFit (rounds p) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length =
        (sendingAt p x).seeds * ((sendingAt p x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ z ∈ K1.seedsOf (sendingAt p x) r₁, isZeroE z.2 = false :=
  rounds_give p (sendingAt p x) r₁ r₂ hE
    (nonZero_of_entry p _ _ (sendingAt_sent p x) he) h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.max_skips
#print axioms VerifiableInference.Desc.K2.Honest.Returns.answersMax_seeds
#print axioms VerifiableInference.Desc.K2.Honest.Returns.nonZero_of_entry
#print axioms VerifiableInference.Desc.K2.Honest.Returns.call_draws
