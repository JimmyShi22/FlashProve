-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Live/Behind.lean: the proof of `HeadMergeLiveBehind`
(Johnson/Desc/K11/Live/BehindStatement.lean), to the letter. Lemmas; none of the library's goals.

How. All by the library's own laws on the merge (Johnson/Top/H0/MergeLaw/). What the decision's yes
holds: `decide_inv` (Says.lean). What the hearing's yes holds: `hear_ended` (Said.lean): the tape
written out, and the sumcheck's state behind the rounds (`Ended`,
OnBytes/Tie/Pv/Psc/Run/PscSeam.lean): its challenges are those on the tape. The tape is the rounds,
one for one (`tapeIs`, Law.lean), and holds what they drew (`tape_drawn`, Beta.lean).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Live.BehindStatement
import Johnson.Desc.K11.Returns.Decide
import Johnson.Top.H0.MergeLaw.Beta
import Johnson.Top.H0.MergeLaw.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Live
open OnBytes (E)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (decide_inv hear_ended rd tapeIs tape_drawn)
open Johnson.Desc.First.ForkMerge.Returns (powers_one)

/-- The flattening of a list of lists of one member each. -/
theorem flat_one {α β : Type} (g : α → β) : ∀ l : List α,
    (l.map fun a => [g a]).flatten = l.map g
  | [] => rfl
  | a :: l => by
    show g a :: ((l.map fun a => [g a]).flatten) = _
    rw [flat_one g l]
    rfl

/-- The start of the merge's sumcheck at one claim: one pair. -/
theorem start_pair (sv : Nat) (x : E) :
    (OnBytes.Model.wsForkStart #[sv] (OnBytes.Model.powers x 1)).slots.toList =
      [(sv, OnBytes.mulE OnBytes.oneE OnBytes.oneE)] := by
  rw [powers_one]
  simp [OnBytes.Model.wsForkStart, OnBytes.Model.Aff.addMul, OnBytes.Model.Aff.slot]

/-- **The condition behind the decision's yes.** -/
theorem headMergeLiveBehind : HeadMergeLiveBehind := by
  intro P s s' rs a x h ha hx hsv hz
  obtain ⟨a0, a', tp, F, claim, x0, wo, ha0, ha', _, hx0, hwo, htp, hm, _, _, _, _⟩ := decide_inv h
  obtain rfl : a0 = a := by
    rw [ha] at ha0
    cases ha0
    rfl
  obtain rfl : x0 = x := Option.some.inj (hx0.symm.trans hx)
  obtain ⟨xs, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, ht, _, hE, _, _, hF, _, _, _⟩ :=
    hear_ended hm
  obtain ⟨hlen, hzip⟩ := tapeIs rs _ tp htp
  have hD := tape_drawn hlen
  rw [← hzip, ht] at hD
  have hl : laterDraws rs = wo.p.eps :: (qs.map (·.2.2) ++ [beta]) := by
    have e2 := congrArg (fun l => (l.drop 1).flatten) hD
    dsimp only at e2
    unfold laterDraws
    rw [List.flatMap_def, List.map_drop]
    rw [← e2]
    simp [rd, Function.comp_def, List.flatten_append, flat_one]
  refine ⟨a', wo, OnBytes.mulE OnBytes.oneE OnBytes.oneE, ha', hwo, hE.first, hE.vars, ?_, ?_, ?_,
    hsv, by rw [hF]; omega, ?_, ?_⟩
  · have := congrArg List.length hE.r
    simpa [hn] using this
  · rw [hE.start]
    exact start_pair x0.sV xs
  · rw [Reading.gl.mul, Reading.gl.one, one_mul]
    exact one_ne_zero
  · exact hz _ (by
      rw [hl]
      exact List.mem_cons_self)
  · intro e he
    rw [hE.r, List.map_map] at he
    exact hz e (by
      rw [hl]
      exact List.mem_cons_of_mem _ (by simpa [Function.comp_def] using he))

end Johnson.Desc.First.ForkMerge.Live

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Live.headMergeLiveBehind
#print axioms Johnson.Desc.First.ForkMerge.Live.flat_one
#print axioms Johnson.Desc.First.ForkMerge.Live.start_pair
