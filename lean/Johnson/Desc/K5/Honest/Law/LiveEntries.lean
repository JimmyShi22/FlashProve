-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveEntries.lean: WHAT THE PLAN DECLARES AT EACH ROUND OF `liveRounds`
(Johnson/Desc/K5/Honest/Law/LiveCount.lean: the rounds of an attention segment's own whose one drawn
element must not be 0, and can be): an entry that draws ONE element, which may be 0. On the
verifier's own list of entries (`entriesOf`, Johnson/Desc/First/Att/K5AttentionKind.lean); no prover, no state
in it.

Why. Whoever counts how often a mark on these rounds speaks asks of each listed round that it draws
one field element and nothing else. That no entry of the list draws a position or a matrix entry,
and that each name's kind is neither "sealed" nor "seeds", the library has of EVERY entry
(`entriesOf_ok`, Johnson/Desc/First/Att/K05Plain.lean; `kind_entriesOf`, K05KindsPlain.lean beside
it). What hangs on the place in the list is shown here: drawE = 1 and drawNZ = 0.

Main names:
  `marksOf`: for each stage that is a part: the rows, if it is a batching draw; else none.
  `entries_batch`: **a part that is a batching draw has the entry "BAT-sigma" at its one round.**
    General in the list of stages.
  `marks_iOm4`: the part number iOm4 of the segment's script is a batching draw.
  `live_entry`: **at each round of `liveRounds` the list holds an entry with drawE = 1 and
    drawNZ = 0.**
  `live_draws`: the same joined with the library's two laws: the round's draws are one element and
    no matrix entry. `live_round`: the declared round, with the bits of work.

Limits. Nothing on how an element is drawn, and no probability.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PartEntries
import Johnson.Desc.First.Att.K05Plain
import Johnson.Desc.First.Att.K05KindsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends)
open VerifiableInference.Desc.First.Att.P (Stage script entriesOf products tailStages script_eq
  entriesOf_ok kind_entriesOf KindGood rounds Par)

/-- For each stage that is a part: the rows, if it is a batching draw; else none. -/
def marksOf : List Stage → List (Option ℕ)
  | [] => []
  | .scalars _ :: l => marksOf l
  | .sum _ _ :: l => none :: marksOf l
  | .batch r :: l => some r :: marksOf l
  | .point _ :: l => none :: marksOf l

theorem marksOf_append : ∀ (a b : List Stage), marksOf (a ++ b) = marksOf a ++ marksOf b
  | [], _ => rfl
  | .scalars _ :: a, b => marksOf_append a b
  | .sum _ _ :: a, b => congrArg (none :: ·) (marksOf_append a b)
  | .batch r :: a, b => congrArg (some r :: ·) (marksOf_append a b)
  | .point _ :: a, b => congrArg (none :: ·) (marksOf_append a b)

theorem marksOf_scalars (n : ℕ) : ∀ k : ℕ, marksOf (List.replicate k (.scalars n)) = []
  | 0 => rfl
  | k + 1 => marksOf_scalars n k

theorem marksOf_units : ∀ us : List (ℕ × ℕ),
    marksOf (us.flatMap fun u => [.scalars 7, products u.1 u.2]) = List.replicate us.length none
  | [] => rfl
  | _ :: us => congrArg (none :: ·) (marksOf_units us)

/-- **The part number iOm4 of the segment's script is a batching draw**, of as many rows as there
are pairs. No premise. -/
theorem marks_iOm4 (x : OnBytes.Params.AttentionRounds) :
    (marksOf (script x))[iOm4 x]? = some (some x.pairs) := by
  rw [script_eq, marksOf_append, marksOf_append, marksOf_scalars, marksOf_units, List.nil_append,
    List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_right _ _),
    List.length_replicate]
  show (marksOf (tailStages x))[x.score.length + 7 - x.score.length]? = _
  rw [Nat.add_sub_cancel_left]
  rfl

/-- **A part that is a batching draw has the entry "BAT-sigma" at its one round.** General in the
list of stages and in the scalars that wait. Conditional: h: part q is of one round, n scalars in
front; hm: it is a batching draw of so many rows. -/
theorem entries_batch : ∀ (st : List Stage) (lead q n rows : ℕ),
    (shapesOf lead st)[q]? = some (.one n) → (marksOf st)[q]? = some (some rows) →
      (entriesOf lead st)[(((shapesOf lead st).take q).map (·.rounds)).sum]? =
        some { name := "BAT-sigma", msg := 24 * n, drawE := 1, rows := rows }
  | [], _, _, _, _, h, _ => nomatch h
  | .scalars m :: st, lead, q, n, rows, h, hm => entries_batch st (lead + m) q n rows h hm
  | .sum _ _ :: _, _, 0, _, _, h, _ => nomatch (Option.some.inj h)
  | .sum vs en :: st, lead, q + 1, n, rows, h, hm => by
    have ih := entries_batch st 0 q n rows h hm
    show (MaskedSum.entries ⟨lead, vs, some en⟩ ++ entriesOf 0 st)[
      (((PartShape.sum ⟨lead, vs, some en⟩ :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum]? =
        _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem?_append_right (by
        rw [entries_len]
        show vs.length + 3 ≤ vs.length + 3 + _
        omega), entries_len]
    rw [show PartShape.rounds (.sum ⟨lead, vs, some en⟩) +
        (((shapesOf 0 st).take q).map (·.rounds)).sum - (vs.length + 3) =
        (((shapesOf 0 st).take q).map (·.rounds)).sum by
      show vs.length + 3 + _ - (vs.length + 3) = _
      omega]
    exact ih
  | .batch r :: st, lead, 0, n, rows, h, hm => by
    have e1 : PartShape.one lead = .one n := Option.some.inj h
    injection e1 with e1
    have e2 : (some r : Option ℕ) = some rows := Option.some.inj hm
    injection e2 with e2
    subst e1
    subst e2
    rfl
  | .batch r :: st, lead, q + 1, n, rows, h, hm => by
    have ih := entries_batch st 0 q n rows h hm
    show (_ :: entriesOf 0 st)[
      (((PartShape.one lead :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      show PartShape.rounds (.one lead) + (((shapesOf 0 st).take q).map (·.rounds)).sum =
        (((shapesOf 0 st).take q).map (·.rounds)).sum + 1 by
      show 1 + _ = _
      omega, List.getElem?_cons_succ]
    exact ih
  | .point _ :: _, _, 0, _, _, _, hm => nomatch (Option.some.inj hm)
  | .point m :: st, lead, q + 1, n, rows, h, hm => by
    have ih := entries_batch st 0 q n rows h hm
    show (_ :: entriesOf 0 st)[
      (((PartShape.one lead :: shapesOf 0 st).take (q + 1)).map (·.rounds)).sum]? = _
    rw [List.take_succ_cons, List.map_cons, List.sum_cons,
      show PartShape.rounds (.one lead) + (((shapesOf 0 st).take q).map (·.rounds)).sum =
        (((shapesOf 0 st).take q).map (·.rounds)).sum + 1 by
      show 1 + _ = _
      omega, List.getElem?_cons_succ]
    exact ih

/-- **THE ENTRY AT EACH LISTED ROUND DRAWS ONE ELEMENT, WHICH MAY BE 0.** No premise. -/
theorem live_entry (x : OnBytes.Params.AttentionRounds) : ∀ n ∈ liveRounds x,
    ∃ e, (entriesOf 0 (script x))[n]? = some e ∧ e.drawE = 1 ∧ e.drawNZ = 0 := by
  intro n hn
  unfold liveRounds at hn
  rcases List.mem_append.1 hn with hn | hn
  · obtain ⟨s, hs, hn⟩ := List.mem_flatMap.1 hn
    obtain ⟨lead, vs, en, hq⟩ := sumParts_sum x s hs
    unfold partRounds at hn
    rcases List.mem_append.1 hn with hn | hn
    · have e0 : n = firstOf x s.1 := by
        split at hn
        · exact List.mem_singleton.1 hn
        · exact nomatch hn
      refine ⟨MaskedSum.entry "PSC epsilon" (lead + 1) 1 0, ?_, rfl, rfl⟩
      · rw [e0, firstOf_eq, ← Nat.add_zero (List.sum _)]
        exact entries_part (script x) 0 s.1 _ hq 0 _ (entries_eps _)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
      rw [varsAt_shape x hq] at ht
      have ht' : t < vs.length := List.mem_range.1 ht
      refine ⟨MaskedSum.entry "PSC round" ((vs[t]).d - 1) 1 0, ?_, rfl, rfl⟩
      · rw [firstOf_eq]
        exact entries_at (script x) 0 s.1 _ hq t _ (List.getElem?_eq_getElem ht')
  · obtain rfl := List.mem_singleton.1 hn
    refine ⟨{ name := "BAT-sigma", msg := 24 * 0, drawE := 1, rows := x.pairs }, ?_, rfl, rfl⟩
    · rw [firstOf_eq]
      exact entries_batch (script x) 0 (iOm4 x) 0 x.pairs (shape_iOm4 x) (marks_iOm4 x)

/-- **A LISTED ROUND's DRAWS, JOINED WITH WHAT THE LIBRARY HAS OF EVERY ENTRY**: one element, which
may be 0; no position; no matrix entry; the entry's word on positions is 0; the format knows the
name, and its kind is neither "sealed" nor "seeds". w: any bits of work. No premise. -/
theorem live_draws (x : OnBytes.Params.AttentionRounds) : ∀ n ∈ liveRounds x,
    ∃ e, (entriesOf 0 (script x))[n]? = some e ∧ e.drawE = 1 ∧ e.logN = 0 ∧ KindGood e.name ∧
      ∀ (w : ℕ) (k : Fmt.Kind), k ≠ .seeds → k ≠ .sealed →
        Fmt.dsOf { e with work := w } k = [.elem, .trits 0] := by
  intro n hn
  obtain ⟨e, he, h1, h0⟩ := live_entry x n hn
  have hm : e ∈ entriesOf 0 (script x) := List.mem_of_getElem? he
  obtain ⟨p0, l0, t0, _⟩ := entriesOf_ok _ _ e hm
  refine ⟨e, he, h1, l0, kind_entriesOf _ _ e hm, fun w k k1 k2 => ?_⟩
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg k1, if_neg k2]
  show List.replicate e.poss (Fmt.Draw.pos e.logN) ++
    (List.replicate (e.drawE - e.drawNZ) Fmt.Draw.elem ++ List.replicate e.drawNZ Fmt.Draw.elemNZ ++
      [Fmt.Draw.trits e.trits]) = _
  rw [p0, h1, h0, t0]
  rfl

/-- **The declared round at a listed number**: the entry, with the policy's bits of work. p: the
kind's parameters. No premise. -/
theorem live_round (p : Par) : ∀ n ∈ liveRounds p.own,
    ∃ e, (entriesOf 0 (script p.own))[n]? = some e ∧
      (rounds p)[n]? = some { entry := { e with work := p.work } } := by
  intro n hn
  obtain ⟨e, he, h1, _⟩ := live_entry p.own n hn
  refine ⟨e, he, ?_⟩
  unfold rounds
  rw [List.getElem?_map, he]
  show some ({ entry := if e.drawE == 0 then e else { e with work := p.work } } :
    Fmt.DeclaredRound) = _
  rw [h1]
  rfl

end H2K5.Honest

#print axioms H2K5.Honest.marksOf_append
#print axioms H2K5.Honest.marksOf_scalars
#print axioms H2K5.Honest.marksOf_units
#print axioms H2K5.Honest.marks_iOm4
#print axioms H2K5.Honest.entries_batch
#print axioms H2K5.Honest.live_entry
#print axioms H2K5.Honest.live_draws
#print axioms H2K5.Honest.live_round
