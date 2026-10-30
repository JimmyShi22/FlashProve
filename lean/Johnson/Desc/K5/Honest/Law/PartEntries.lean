-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PartEntries.lean: WHAT THE PLAN DECLARES AT EACH ROUND OF A MASKED
SUMCHECK THAT IS A PART OF AN ATTENTION SEGMENT's OWN ROUNDS (kind K5): the entry number i of the
sumcheck's own list of entries stands in the segment's list at the part's first round + i. On the
verifier's own list of entries (`entriesOf`, Johnson/Desc/First/Att/K5AttentionKind.lean); no prover, no state
in it.

Why. Johnson/Desc/K5/Honest/Law/ReadEntries.lean has this for a variable's round. The rounds of the
element that scales the claimed sum ("PSC epsilon") and of the further variable ("PSC Y") are wanted
too: the first may draw 0; at the second the entry counts the element as never 0.

Main names:
  `entries_part`: **general in the list of stages, in the part and in i.**
  `entries_eps`, `entries_Y`: entry number 0, and entry number 1 + the variables, of a sumcheck with
    ends.
  `varsAt_shape`: a part's number of variables, off its shape.
  `sumParts_sum`: each part of `sumParts` (Johnson/Desc/K5/Honest/Law/LiveCount.lean) is a sumcheck
    with ends.
  `beta_entry`: **at each round of `betaRounds` the list holds an entry "PSC Y" … 1 1**: one
    element, never 0.

Limits. Nothing on how an element is drawn, and no probability. The one round "BAT-sigma" of
`liveRounds` is not spoken of.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadEntries
import Johnson.Desc.K5.Honest.Law.LiveCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends)
open VerifiableInference.Desc.First.Att.P (Stage script entriesOf)

/-- **Entry number i of the masked sumcheck that is part q stands at the part's first round + i.**
General in the list of stages and in the scalars that wait. Conditional: h: part q is that sumcheck;
he: its entry number i. -/
theorem entries_part : ∀ (st : List Stage) (lead q : ℕ) (k : Call),
    (shapesOf lead st)[q]? = some (.sum k) → ∀ (i : ℕ) (e : Fmt.Entry),
      (MaskedSum.entries k)[i]? = some e →
      (entriesOf lead st)[(((shapesOf lead st).take q).map (·.rounds)).sum + i]? = some e
  | [], _, _, _, h, _, _, _ => nomatch h
  | .scalars n :: st, lead, q, k, h, i, e, he => entries_part st (lead + n) q k h i e he
  | .sum vs en :: st, lead, 0, k, h, i, e, he => by
    have hk : (PartShape.sum ⟨lead, vs, some en⟩) = .sum k := Option.some.inj h
    injection hk with hk
    subst hk
    show (MaskedSum.entries ⟨lead, vs, some en⟩ ++ entriesOf 0 st)[0 + i]? = _
    rw [Nat.zero_add, List.getElem?_append_left (List.getElem?_eq_some_iff.1 he).1]
    exact he
  | .sum vs en :: st, lead, q + 1, k, h, i, e, he => by
    have ih := entries_part st 0 q k h i e he
    show (MaskedSum.entries ⟨lead, vs, some en⟩ ++ entriesOf 0 st)[
      (((PartShape.sum ⟨lead, vs, some en⟩ :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum +
        i]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem?_append_right (by
        rw [entries_len]
        show vs.length + 3 ≤ vs.length + 3 + _ + i
        omega), entries_len]
    rw [show PartShape.rounds (.sum ⟨lead, vs, some en⟩) +
        (((shapesOf 0 st).take q).map (·.rounds)).sum + i - (vs.length + 3) =
        (((shapesOf 0 st).take q).map (·.rounds)).sum + i by
      show vs.length + 3 + _ + i - (vs.length + 3) = _
      omega]
    exact ih
  | .batch _ :: _, _, 0, _, h, _, _, _ => nomatch (Option.some.inj h)
  | .batch rows :: st, lead, q + 1, k, h, i, e, he => by
    have ih := entries_part st 0 q k h i e he
    show (_ :: entriesOf 0 st)[
      (((PartShape.one lead :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum + i]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      show PartShape.rounds (.one lead) + (((shapesOf 0 st).take q).map (·.rounds)).sum + i =
        ((((shapesOf 0 st).take q).map (·.rounds)).sum + i) + 1 by
      show 1 + _ + i = _
      omega, List.getElem?_cons_succ]
    exact ih
  | .point _ :: _, _, 0, _, h, _, _, _ => nomatch (Option.some.inj h)
  | .point n :: st, lead, q + 1, k, h, i, e, he => by
    have ih := entries_part st 0 q k h i e he
    show (_ :: entriesOf 0 st)[
      (((PartShape.one lead :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum + i]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      show PartShape.rounds (.one lead) + (((shapesOf 0 st).take q).map (·.rounds)).sum + i =
        ((((shapesOf 0 st).take q).map (·.rounds)).sum + i) + 1 by
      show 1 + _ + i = _
      omega, List.getElem?_cons_succ]
    exact ih

/-- A sumcheck's entry number 0. -/
theorem entries_eps (k : Call) :
    (MaskedSum.entries k)[0]? = some (MaskedSum.entry "PSC epsilon" (k.lead + 1) 1 0) := rfl

/-- Entry number 1 + the variables of a sumcheck with ends. -/
theorem entries_Y (lead : ℕ) (vs : List Var) (en : Ends) :
    (MaskedSum.entries ⟨lead, vs, some en⟩)[1 + vs.length]? =
      some (MaskedSum.entry "PSC Y" en.dY 1 1) := by
  unfold MaskedSum.entries
  rw [List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_right (by simp)]
  simp

/-- A part's number of variables, off its shape. -/
theorem varsAt_shape (x : OnBytes.Params.AttentionRounds) {p : ℕ} {k : Call}
    (h : (shapes x)[p]? = some (.sum k)) : varsAt x p = k.vs.length := by
  unfold varsAt
  rw [cut_of_shape x p 3 _ h]
  show k.vs.length + 3 - 3 = k.vs.length
  omega

/-- Each part of the list is a sumcheck with ends. -/
theorem sumParts_sum (x : OnBytes.Params.AttentionRounds) : ∀ s ∈ sumParts x,
    ∃ lead vs en, (shapes x)[s.1]? = some (.sum ⟨lead, vs, some en⟩) := by
  intro s hs
  unfold sumParts at hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
    have hi' : i < x.score.length := List.mem_range.1 hi
    exact ⟨_, _, _, shape_unit x i _ (List.getElem?_eq_getElem hi')⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, _, _, shape_iSE x⟩
    · exact ⟨_, _, _, shape_iVM x⟩
    · exact ⟨_, _, _, shape_iVD x⟩
    · exact ⟨_, _, _, shape_iSF x⟩
    · exact ⟨_, _, _, shape_iSD x⟩
    · exact ⟨_, _, _, shape_iHB x⟩

/-- **The entry at each round of the further variables**: one element is drawn, never 0. dY: the
number of scalars that the round sends. No premise. -/
theorem beta_entry (x : OnBytes.Params.AttentionRounds) : ∀ n ∈ betaRounds x,
    ∃ dY, (entriesOf 0 (script x))[n]? = some (MaskedSum.entry "PSC Y" dY 1 1) := by
  intro n hn
  unfold betaRounds at hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hn
  obtain ⟨lead, vs, en, hq⟩ := sumParts_sum x s hs
  refine ⟨en.dY, ?_⟩
  rw [varsAt_shape x hq, firstOf_eq, Nat.add_assoc]
  exact entries_part (script x) 0 s.1 _ hq (1 + vs.length) _ (entries_Y lead vs en)

end H2K5.Honest

#print axioms H2K5.Honest.entries_part
#print axioms H2K5.Honest.entries_eps
#print axioms H2K5.Honest.entries_Y
#print axioms H2K5.Honest.varsAt_shape
#print axioms H2K5.Honest.sumParts_sum
#print axioms H2K5.Honest.beta_entry
