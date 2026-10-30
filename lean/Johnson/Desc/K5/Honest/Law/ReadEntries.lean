-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadEntries.lean: CONDITIONAL: WHAT THE PLAN DECLARES AT THE ROUNDS OF
`readRounds` (Johnson/Desc/K5/Honest/Law/ReadRounds.lean): each is a round "PSC round" of a masked
sumcheck of products: three scalars are sent, ONE element is drawn, which may be 0. On the
verifier's own list of rounds of an attention segment's own rounds (`rounds`,
Johnson/Desc/First/Att/K5AttentionKind.lean); no prover, no state in it.

Why. Whoever counts the draws at which the test `k5Reads` says no wants, for each listed round, the
declared entry as a term.

Main names:
  `entries_at`: general in the list of stages: round number 1 + l of the masked sumcheck that is
    part q is the entry "PSC round" of its variable number l.
  `read_entry`: at each number of `readRounds` the list of entries holds
    `MaskedSum.entry` "PSC round" 3 1 0.
  `read_round`: **the declared round there, as a term**: that entry with the policy's bits of work.
  `read_round_plan`: the same under two structures of facts on public numbers.

That ONE element is drawn WHICH MAY BE 0 is why an event "it is 0 or 1" has to be counted at these
rounds: the format does not shut it out, as it does at the round of a sumcheck's further variable.

Limits. In `read_entry` and `read_round` h1, h2 (the two sumchecks have variables enough) are
premises on public numbers; `reads_fit` (ReadRounds.lean) pays them. Nothing on how an element is
drawn, and no probability.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadRounds
import Johnson.Desc.K5.Honest.Law.Named
import Johnson.Desc.K5.Honest.Law.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var)
open VerifiableInference.Desc.First.Att.P (Geo Stage script entriesOf Par rounds)

/-- A masked sumcheck with ends has its variables' number of rounds and three more. -/
theorem entries_len (lead : ℕ) (vs : List Var) (e : MaskedSum.Ends) :
    (MaskedSum.entries ⟨lead, vs, some e⟩).length = vs.length + 3 := by
  unfold MaskedSum.entries
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
  omega

/-- **Round number 1 + l of the masked sumcheck that is part q is the entry of its variable number
l.** General in the list of stages and in the scalars that wait. Conditional: h: part q is that
sumcheck; hv: its variable number l. -/
theorem entries_at : ∀ (st : List Stage) (lead q : ℕ) (k : Call),
    (shapesOf lead st)[q]? = some (.sum k) → ∀ (l : ℕ) (v : Var), k.vs[l]? = some v →
      (entriesOf lead st)[(((shapesOf lead st).take q).map (·.rounds)).sum + 1 + l]? =
        some (MaskedSum.entry "PSC round" (v.d - 1) 1 0)
  | [], _, _, _, h, _, _, _ => nomatch h
  | .scalars n :: st, lead, q, k, h, l, v, hv => entries_at st (lead + n) q k h l v hv
  | .sum vs e :: st, lead, 0, k, h, l, v, hv => by
    have hk : (PartShape.sum ⟨lead, vs, some e⟩) = .sum k := Option.some.inj h
    injection hk with hk
    subst hk
    have hl : l < vs.length := (List.getElem?_eq_some_iff.1 hv).1
    show (MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 st)[0 + 1 + l]? = _
    rw [List.getElem?_append_left (by rw [entries_len]; omega)]
    unfold MaskedSum.entries
    rw [List.append_assoc, List.getElem?_append_right (by simp),
      List.getElem?_append_left (by simp; omega)]
    simp only [List.length_cons, List.length_nil, List.getElem?_map]
    rw [show 0 + 1 + l - (0 + 1) = l by omega]
    show (vs[l]?).map _ = _
    rw [hv]
    rfl
  | .sum vs e :: st, lead, q + 1, k, h, l, v, hv => by
    have ih := entries_at st 0 q k h l v hv
    show (MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 st)[
      (((PartShape.sum ⟨lead, vs, some e⟩ :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum +
        1 + l]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem?_append_right (by
        rw [entries_len]
        show vs.length + 3 ≤ vs.length + 3 + _ + 1 + l
        omega), entries_len]
    rw [show PartShape.rounds (.sum ⟨lead, vs, some e⟩) +
        (((shapesOf 0 st).take q).map (·.rounds)).sum + 1 + l - (vs.length + 3) =
        (((shapesOf 0 st).take q).map (·.rounds)).sum + 1 + l by
      show vs.length + 3 + _ + 1 + l - (vs.length + 3) = _
      omega]
    exact ih
  | .batch _ :: _, _, 0, _, h, _, _, _ => nomatch (Option.some.inj h)
  | .batch rows :: st, lead, q + 1, k, h, l, v, hv => by
    have ih := entries_at st 0 q k h l v hv
    show (_ :: entriesOf 0 st)[
      (((PartShape.one lead :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum + 1 + l]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      show PartShape.rounds (.one lead) + (((shapesOf 0 st).take q).map (·.rounds)).sum + 1 + l =
        ((((shapesOf 0 st).take q).map (·.rounds)).sum + 1 + l) + 1 by
      show 1 + _ + 1 + l = _
      omega, List.getElem?_cons_succ]
    exact ih
  | .point _ :: _, _, 0, _, h, _, _, _ => nomatch (Option.some.inj h)
  | .point n :: st, lead, q + 1, k, h, l, v, hv => by
    have ih := entries_at st 0 q k h l v hv
    show (_ :: entriesOf 0 st)[
      (((PartShape.one lead :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum + 1 + l]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      show PartShape.rounds (.one lead) + (((shapesOf 0 st).take q).map (·.rounds)).sum + 1 + l =
        ((((shapesOf 0 st).take q).map (·.rounds)).sum + 1 + l) + 1 by
      show 1 + _ + 1 + l = _
      omega, List.getElem?_cons_succ]
    exact ih

/-- A variable's round of a sumcheck of products, by the part's number. Conditional: hq: part q is a
sumcheck of products of n variables; hl. -/
theorem products_entry (x : OnBytes.Params.AttentionRounds) {q lead n m l : ℕ}
    (hq : (shapes x)[q]? = some (productsShape lead n m)) (hl : l < n) :
    (entriesOf 0 (script x))[firstOf x q + 1 + l]? = some (MaskedSum.entry "PSC round" 3 1 0) := by
  rw [firstOf_eq]
  exact entries_at (script x) 0 q _ hq l (.plain 4) (by
    show (List.replicate n (Var.plain 4))[l]? = _
    rw [List.getElem?_replicate, if_pos hl])

/-- **The entry at each listed round.** Conditional: h1, h2: the two sumchecks have variables
enough. -/
theorem read_entry (x : OnBytes.Params.AttentionRounds) (g : Geo) (h1 : g.lgk + g.lt ≤ x.e)
    (h2 : g.lt + g.lgk + g.ls ≤ x.attained) : ∀ n ∈ readRounds x g,
    (entriesOf 0 (script x))[n]? = some (MaskedSum.entry "PSC round" 3 1 0) := by
  intro n hn
  unfold readRounds at hn
  simp only [List.mem_append, List.mem_map, List.mem_range] at hn
  rcases hn with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact products_entry x (shape_iSE x) (by omega)
  · exact products_entry x (shape_iSF x) (by omega)
  · exact products_entry x (shape_iSF x) (by omega)

/-- **THE DECLARED ROUND AT EACH LISTED NUMBER, AS A TERM**: three scalars are sent; one element is
drawn, which may be 0; the policy's bits of work. Conditional: h1, h2. -/
theorem read_round (p : Par) (g : Geo) (h1 : g.lgk + g.lt ≤ p.own.e)
    (h2 : g.lt + g.lgk + g.ls ≤ p.own.attained) : ∀ n ∈ readRounds p.own g,
    (rounds p)[n]? =
      some { entry := { MaskedSum.entry "PSC round" 3 1 0 with work := p.work } } := by
  intro n hn
  unfold rounds
  rw [List.getElem?_map, read_entry p.own g h1 h2 n hn]
  rfl

/-- **The same with the two premises paid** from two structures of facts on public numbers. S: the
segment's shape. Conditional: H, Pl. -/
theorem read_round_plan (p : Par) (S : OnBytes.Attention.Shape) (H : Sized ⟨S, p.own⟩)
    (Pl : Planned ⟨S, p.own⟩) : ∀ n ∈ readRounds p.own (Pub5.g ⟨S, p.own⟩),
    (rounds p)[n]? =
      some { entry := { MaskedSum.entry "PSC round" 3 1 0 with work := p.work } } :=
  read_round p _ (reads_fit H Pl).1 (reads_fit H Pl).2

end H2K5.Honest

#print axioms H2K5.Honest.entries_len
#print axioms H2K5.Honest.entries_at
#print axioms H2K5.Honest.products_entry
#print axioms H2K5.Honest.read_entry
#print axioms H2K5.Honest.read_round
#print axioms H2K5.Honest.read_round_plan
