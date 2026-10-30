-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GoOnTest.lean: **"THE PLAN's NUMBERS AND LISTS GO ON WITH THE PROXIMITY TEST's
SENDINGS": A TEST WITH CODE ON THE PLAN.** Definitions, statements and proofs. `GoOn`
(K12Grows.lean) speaks of the verifier's state: its table of codes and the two counts of its book of
commitment trees. Where the state's codes are the plan's and the table's clause `bookAt` holds of
the state, these three are numbers of the plan: so `GoOn` comes down to a Bool that reads no state.
  `goOnB N p p' π L codes`: the test: the sendings behind the first stage, laid at `codes` with
    their trees counted from `N.treesAt (some p)` on, add just as many trees and messages as the
    plan's two numbers grow from p to p', and the plan's two lists L go on with what is laid. FALSE
    where the place has no stage, or a sending cannot be laid: it fails shut.
  `goOn_of_B`: the test's yes, "the state's codes are `codes`" and `bookAt N (some p) s` give
    `GoOn N p p' π L s`.
  `goOnB_noStage`, `goOnB_notLaid`: it fails shut. `goOnB_one`: it bites, in all four conjuncts: two
    fillings (numbers and lists) that agree in the two numbers in front of the block and both pass
    agree in the two numbers behind it and, on the stretch that is laid, in both lists.
Limits. The test has run nowhere. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.K12Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (Numbers bookAt)

/-- **The test on the plan.** -/
def goOnB (N : Numbers) (p p' : Place) (π : P12) (L : Laid) (codes : Codes) : Bool :=
  match π.nums.stages with
  | [] => false
  | _ :: rest =>
    match laidFrom codes (N.treesAt (some p)) (sendsFrom π 0 rest) with
    | none => false
    | some A =>
      N.treesAt (some p') == N.treesAt (some p) + A.shapes.length &&
        N.msgsAt (some p') == N.msgsAt (some p) + A.places.length &&
        (L.places.drop (N.msgsAt (some p))).take A.places.length == A.places &&
        (L.shapes.drop (N.treesAt (some p))).take A.shapes.length == A.shapes

/-- **Its yes gives `GoOn`** at every state with these codes of which `bookAt` holds. -/
theorem goOn_of_B {N : Numbers} {p p' : Place} {π : P12} {L : Laid} {codes : Codes}
    (h : goOnB N p p' π L codes = true) (s : First.S) (hc : s.st.codes = codes)
    (hb : bookAt N (some p) s = true) : GoOn N p p' π L s := by
  intro first rest A hs hA
  simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨b1, b2⟩, b3⟩ := hb
  unfold goOnB at h
  rw [hs] at h
  rw [hc, b1] at hA
  simp only [hA, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h
  rw [b1, b2, b3]
  exact ⟨g1, g2, g3, g4⟩

/-- It fails shut: no stage. -/
theorem goOnB_noStage (N : Numbers) (p p' : Place) (π : P12) (L : Laid) (codes : Codes)
    (h : π.nums.stages = []) : goOnB N p p' π L codes = false := by
  unfold goOnB
  rw [h]

/-- It fails shut: a sending that cannot be laid. -/
theorem goOnB_notLaid (N : Numbers) (p p' : Place) (π : P12) (L : Laid) (codes : Codes)
    (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : π.nums.stages = first :: rest)
    (h : laidFrom codes (N.treesAt (some p)) (sendsFrom π 0 rest) = none) :
    goOnB N p p' π L codes = false := by
  unfold goOnB
  rw [hs]
  simp only [h]

/-- **It bites, in all four conjuncts**: two fillings (numbers and lists) that agree in the two
numbers in front of the block and both pass agree in the two numbers behind it, and their lists
agree on the stretch that the sendings lay: the test leaves none of the four a choice. -/
theorem goOnB_one {N N' : Numbers} {p p' : Place} {π : P12} {L L' : Laid} {codes : Codes}
    (h : goOnB N p p' π L codes = true) (h' : goOnB N' p p' π L' codes = true)
    (e : N'.treesAt (some p) = N.treesAt (some p)) (f : N'.msgsAt (some p) = N.msgsAt (some p)) :
    N'.treesAt (some p') = N.treesAt (some p') ∧ N'.msgsAt (some p') = N.msgsAt (some p') ∧
    ∃ A : Laid,
      (L'.places.drop (N.msgsAt (some p))).take A.places.length =
        (L.places.drop (N.msgsAt (some p))).take A.places.length ∧
      (L'.shapes.drop (N.treesAt (some p))).take A.shapes.length =
        (L.shapes.drop (N.treesAt (some p))).take A.shapes.length ∧
      N.treesAt (some p') = N.treesAt (some p) + A.shapes.length ∧
      N.msgsAt (some p') = N.msgsAt (some p) + A.places.length := by
  unfold goOnB at h h'
  rw [e, f] at h'
  cases hs : π.nums.stages with
  | nil => rw [hs] at h; cases h
  | cons first rest =>
    rw [hs] at h h'
    cases hA : laidFrom codes (N.treesAt (some p)) (sendsFrom π 0 rest) with
    | none => simp only [hA] at h; cases h
    | some A =>
      simp only [hA, Bool.and_eq_true, beq_iff_eq] at h h'
      obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h
      obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h'
      exact ⟨by rw [a1, b1], by rw [a2, b2], A, by rw [a3, b3], by rw [a4, b4], a1, a2⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.goOn_of_B
#print axioms VerifiableInference.Desc.K12.Coin.goOnB_noStage
#print axioms VerifiableInference.Desc.K12.Coin.goOnB_notLaid
#print axioms VerifiableInference.Desc.K12.Coin.goOnB_one
