-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/Tape.lean: THE KIND's MAKER OF THE TAPE RETURNS on rounds of the merge's
form: `mergeTapeE` (Johnson/Desc/First/Fork/MergeKind.lean) at `MergeRoundsForm`
(Johnson/Desc/K11/Returns/Statement.lean), and which tape it hands back. Lemmas; none of the
library's goals. The text is the verifier's; no prover is named.

The chief names:
  `roundS_of_sent`     one round, as the strict maker lays it
  `tapeS_two`          the rounds in the column bits
  `mergeTape_of_form`  the whole: the tape is `mergeTapeOf` (FlatEnd.lean of this folder) at some
                       elements

Limits. Nothing on soundness, on an honest prover or on any property.
-/
import Johnson.Desc.K11.Returns.Statement
import Johnson.Desc.K11.Returns.FlatEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E)
open OnBytes.Model (RoundName)
open OnBytes.K.Kc (Tape flatOf)
open OnBytes.Desc.First.P1 (rd)
open VerifiableInference.Desc (need named)
open VerifiableInference.Desc.First.Look (elemsOf roundS tapeS kindAsked)
open VerifiableInference.Desc.First.Door (batchEntryB batchRoundB)
open VerifiableInference.Desc.Part.MaskedSum (scalars Sent)

/-- The strict maker's function on a message's items is the part's. -/
theorem elemsOf_scalars : ∀ l : List Fmt.ItemValue, elemsOf l = scalars l
  | [] => rfl
  | .e x :: l => by
    show (elemsOf l).map _ = (scalars l).map _
    rw [elemsOf_scalars l]
  | .f _ :: _ => rfl
  | .word _ :: _ => rfl
  | .root _ :: _ => rfl
  | .answer _ :: _ => rfl

/-- A round that holds just these scalars and drew just these elements, and elements alone, under an
entry that states as many draws, no position, no matrix entry and no row. -/
theorem roundS_of_sent {r : Fmt.RoundView} {n k : Nat} {s d : List E} (h : Sent r n k s d)
    (hp : r.drawn.poss = []) (ht : r.drawn.trits = []) (e : Fmt.Entry) (h1 : e.drawE = k)
    (h2 : e.poss = 0) (h3 : e.trits = 0) (h4 : e.rows = 0)
    (h5 : (e.name != RoundName.batSigma.name) = true)
    (h6 : (OnBytes.Params.kindOf e.name == some (kindAsked e.name)) = true) :
    roundS r e = some ⟨some e.name, e.drawNZ, 0, s, d⟩ := by
  obtain ⟨a1, _, a3, a4⟩ := h
  subst a4
  unfold roundS
  rw [elemsOf_scalars, a1]
  simp [a3, h1, hp, ht, h2, h3, h4, h5, h6]

/-- The name of the sumcheck's first round is not that of the round that batches rows. -/
theorem name_eps_ne : (RoundName.pscEpsilon.name != RoundName.batSigma.name) = true := by decide
/-- The like of a round in a variable. -/
theorem name_round_ne : (RoundName.pscRound.name != RoundName.batSigma.name) = true := by decide
/-- The like of the round in the further variable. -/
theorem name_y_ne : (RoundName.pscY.name != RoundName.batSigma.name) = true := by decide
/-- The like of the round of the end values. -/
theorem name_values_ne : (RoundName.pscValues.name != RoundName.batSigma.name) = true := by decide
/-- The format gives the first round's name the kind under which the program closes it. -/
theorem kind_eps_asked : (OnBytes.Params.kindOf RoundName.pscEpsilon.name ==
    some (kindAsked RoundName.pscEpsilon.name)) = true := by decide
/-- The like of a round in a variable. -/
theorem kind_round_asked : (OnBytes.Params.kindOf RoundName.pscRound.name ==
    some (kindAsked RoundName.pscRound.name)) = true := by decide
/-- The like of the round in the further variable. -/
theorem kind_y_asked : (OnBytes.Params.kindOf RoundName.pscY.name ==
    some (kindAsked RoundName.pscY.name)) = true := by decide
/-- The like of the round of the end values. -/
theorem kind_values_asked : (OnBytes.Params.kindOf RoundName.pscValues.name ==
    some (kindAsked RoundName.pscValues.name)) = true := by decide
/-- The format's kind of the round that batches rows: elements are drawn. -/
theorem kind_batch_elems :
    (OnBytes.Params.kindOf RoundName.batSigma.name == some .elems) = true := by decide

/-- One drawn element, by name. -/
theorem sent_one {r : Fmt.RoundView} {n : Nat} {s d : List E} (h : Sent r n 1 s d) : ∃ g, d = [g] := by
  obtain ⟨_, _, a3, a4⟩ := h
  have e : d.length = 1 := by rw [a4, List.length_map, a3]
  exact List.length_eq_one_iff.1 e

/-- The rounds in the column bits, as the strict maker lays them. -/
theorem tapeS_two (work : Nat) : ∀ (u rest : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    (∀ r ∈ u, ∃ s d, Sent r 2 1 s d) → (∀ r ∈ u, r.drawn.poss = [] ∧ r.drawn.trits = []) →
    tapeS rest es = some t →
    ∃ xs : List (Nat × List E × E), xs.length = u.length ∧ (∀ y ∈ xs, y.2.1.length = 2) ∧
      tapeS (u ++ rest)
        (List.replicate u.length
            { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } ++ es) =
        some (xs.map rd ++ t)
  | [], rest, es, t, _, _, ht =>
    ⟨[], rfl, fun _ h => (List.not_mem_nil h).elim, by simpa using ht⟩
  | r :: u, rest, es, t, hs, hp, ht => by
    obtain ⟨xs, h1, h2, h3⟩ := tapeS_two work u rest es t
      (fun r' h' => hs r' (List.mem_cons_of_mem _ h'))
      (fun r' h' => hp r' (List.mem_cons_of_mem _ h')) ht
    obtain ⟨s, d, hsd⟩ := hs r List.mem_cons_self
    obtain ⟨g, rfl⟩ := sent_one hsd
    have hr := roundS_of_sent hsd (hp r List.mem_cons_self).1 (hp r List.mem_cons_self).2
      { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } rfl rfl rfl rfl
      name_round_ne kind_round_asked
    refine ⟨(0, s, g) :: xs, by rw [List.length_cons, List.length_cons, h1], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hsd.2.1
      · exact h2 y hy
    · show tapeS (r :: (u ++ rest)) (_ :: (List.replicate u.length _ ++ es)) = _
      unfold tapeS
      rw [hr, h3]
      rfl

/-- **The kind's maker of the tape returns on rounds of the merge's form.** n: the number of claims
that the batching round's entry states. -/
theorem mergeTape_of_form (lk n work : Nat) (rs : List Fmt.RoundView) (h : MergeRoundsForm lk rs) :
    ∃ (x mu eps c beta v : E) (xs : List (Nat × List E × E)), xs.length = lk ∧
      (∀ y ∈ xs, y.2.1.length = 2) ∧
      mergeTapeE rs (mergeEntries lk n work) = .ok (mergeTapeOf n x mu eps 0 xs 0 c beta 0 v) := by
  obtain ⟨hq, r₀, r1, rY, rv, u, rfl, hu, hv0, he0, ⟨s1, d1, a1⟩, hU, ⟨sY, dY, aY⟩, ⟨sV, aV⟩⟩ := h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 he0
  obtain ⟨eps, rfl⟩ := sent_one a1
  obtain ⟨beta, rfl⟩ := sent_one aY
  obtain ⟨mu, rfl⟩ := List.length_eq_one_iff.1 a1.2.1
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 aY.2.1
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.1 aV.2.1
  have q0 := hq r₀ List.mem_cons_self
  have q1 := hq r1 (by simp)
  have qY := hq rY (by simp)
  have qV := hq rv (by simp)
  have b1 := roundS_of_sent a1 q1.1 q1.2
    { name := RoundName.pscEpsilon.name, work := work, msg := 24, drawE := 1 } rfl rfl rfl rfl
    name_eps_ne kind_eps_asked
  have bY := roundS_of_sent aY qY.1 qY.2
    { name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 } rfl rfl rfl
    rfl name_y_ne kind_y_asked
  have bV := roundS_of_sent aV qV.1 qV.2 { name := RoundName.pscValues.name, msg := 24 } rfl rfl
    rfl rfl name_values_ne kind_values_asked
  have tEnd : tapeS [rY, rv]
      [{ name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 },
       { name := RoundName.pscValues.name, msg := 24 }] =
      some [⟨some RoundName.pscY.name, 1, 0, [c], [beta]⟩,
        ⟨some RoundName.pscValues.name, 0, 0, [v], []⟩] := by
    simp only [tapeS, bY, bV]
  obtain ⟨xs, h1, h2, tMid⟩ := tapeS_two work u [rY, rv] _ _ hU
    (fun r hr => hq r (by simp [hr])) tEnd
  rw [hu] at tMid
  have tAll : tapeS (r1 :: (u ++ [rY, rv]))
      ({ name := RoundName.pscEpsilon.name, work := work, msg := 24, drawE := 1 } ::
        (List.replicate lk
            { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } ++
          [{ name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 },
           { name := RoundName.pscValues.name, msg := 24 }])) =
      some (⟨some RoundName.pscEpsilon.name, 0, 0, [mu], [eps]⟩ ::
        (xs.map rd ++
          [⟨some RoundName.pscY.name, 1, 0, [c], [beta]⟩,
            ⟨some RoundName.pscValues.name, 0, 0, [v], []⟩])) := by
    unfold tapeS
    rw [b1, tMid]
  have c1 : batchEntryB
      { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n } = true := by
    show (OnBytes.Params.kindOf RoundName.batSigma.name == some .elems && (1 : Nat) == 1 &&
      (0 : Nat) == 0 && (0 : Nat) == 0) = true
    rw [kind_batch_elems]
    rfl
  have c2 : batchRoundB
      { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n } r₀ = true := by
    simp [batchRoundB, hv0, hx, q0.1, q0.2]
  have fl : flatOf r₀
      (some { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n }) =
      ⟨some RoundName.batSigma.name, 0, n, [], [E.ofTriple x]⟩ := by
    unfold flatOf
    rw [hv0, hx]
    rfl
  refine ⟨E.ofTriple x, mu, eps, c, beta, v, xs, h1.trans hu, h2, ?_⟩
  unfold mergeEntries mergeTapeE
  simp only [need, named, c1, c2, tAll, fl, bind, Except.bind, pure, Except.pure, if_true]
  rfl

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.elemsOf_scalars
#print axioms Johnson.Desc.First.ForkMerge.Returns.roundS_of_sent
#print axioms Johnson.Desc.First.ForkMerge.Returns.name_eps_ne
#print axioms Johnson.Desc.First.ForkMerge.Returns.name_round_ne
#print axioms Johnson.Desc.First.ForkMerge.Returns.name_y_ne
#print axioms Johnson.Desc.First.ForkMerge.Returns.name_values_ne
#print axioms Johnson.Desc.First.ForkMerge.Returns.kind_eps_asked
#print axioms Johnson.Desc.First.ForkMerge.Returns.kind_round_asked
#print axioms Johnson.Desc.First.ForkMerge.Returns.kind_y_asked
#print axioms Johnson.Desc.First.ForkMerge.Returns.kind_values_asked
#print axioms Johnson.Desc.First.ForkMerge.Returns.kind_batch_elems
#print axioms Johnson.Desc.First.ForkMerge.Returns.sent_one
#print axioms Johnson.Desc.First.ForkMerge.Returns.tapeS_two
#print axioms Johnson.Desc.First.ForkMerge.Returns.mergeTape_of_form
