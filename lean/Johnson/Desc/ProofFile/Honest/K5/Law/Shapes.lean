-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Shapes.lean: the row of parts into which the honest side of an
attention segment's own rounds is cut (`shapes`, Johnson/Desc/K5/Honest/Faces.lean) against the
verifier's own rounds (`entriesOf`, `script`, `rounds`, Johnson/Desc/First/Att/K5AttentionKind.lean): at every
set of the planner's numbers. Definitions of propositions, and statements with their proofs.

  `OneEntry`, `EntriesAre`   what it says that a list of entries is the parts' entries in a row: a
      masked sumcheck's are the call's own (`MaskedSum.entries`); a round by itself has the
      verifier's entry: a batching element's or a point's
  `shapesOf_are`, `shapes_are_script`   **the parts' entries in a row are the verifier's**: at
      every list of stages and every number of waiting scalars; at the script
  `sentOf`, `sentOf_length`   how many scalars each round of a part sends; as many rounds as
      `PartShape.rounds` counts
  `sum_of_stage`, `script_two`, `shapes_two`   every variable of every sumcheck of the script has at
      least two coefficients
  `entriesAre_nums`, `rounds_nums`, `rounds_length`, `rounds_stated`   the declared rounds state
      just these scalars and no oracle message (`StatedBy`, Honest/SumLaw/Fits.lean)
  `statedBy_length`, `statedBy_split`   names that stand for the laws of the same spelling in
      Honest/Small/Stated.lean (one line `export`): no declarations here
  `rounds_read_nothing`, `rounds_plain`   no round reads a column; no entry has a root or an answer,
      and each message is whole scalars
  `cut_sum`, `firstOf_zero`, `firstOf_succ`   the cut adds up to the verifier's number of rounds; a
      part's first round

Limits. The facts are on public numbers alone: no run, no coin and no value is in them. Nothing is
asked of the planner's numbers: the statements hold at numbers that the verifier's test on the plan
refuses too. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.RowOf
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits
import Johnson.Desc.ProofFile.Honest.Small.Stated
import Johnson.Desc.ProofFile.Honest.Law.Steps
import Johnson.Desc.First.Att.K5AttentionKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part (MaskedSum.entries MaskedSum.entry)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.First.Att.P (Stage products script entriesOf Par rounds)
open H2K5.Honest (PartShape shapesOf shapes cut)
open ProofFile.Honest.SumLaw (StatedBy statedBy_nums entries_nums)

export ProofFile.Honest.Small (statedBy_length statedBy_split)

/-! ## 1 The parts' entries are the verifier's -/

/-- The verifier's entry of a round by itself in front of which n scalars wait: a batching
element's, or a point's. -/
def OneEntry (n : Nat) (e : Fmt.Entry) : Prop :=
  (∃ rows, e = { name := "BAT-sigma", msg := 24 * n, drawE := 1, rows := rows }) ∨
    ∃ k, e = MaskedSum.entry "ZERO" n k 0

/-- The entries are the parts' entries, in a row: a masked sumcheck's are the call's own; a round by
itself has the verifier's entry. -/
def EntriesAre : List PartShape → List Fmt.Entry → Prop
  | [], es => es = []
  | .sum k :: l, es => ∃ es', es = MaskedSum.entries k ++ es' ∧ EntriesAre l es'
  | .one n :: l, es => ∃ e es', es = e :: es' ∧ OneEntry n e ∧ EntriesAre l es'

/-- **The parts' entries in a row are the stages' entries**, at every list of stages and every
number of scalars that wait. No premise. -/
theorem shapesOf_are : ∀ (st : List Stage) (lead : Nat),
    EntriesAre (shapesOf lead st) (entriesOf lead st)
  | [], _ => rfl
  | .scalars n :: l, lead => shapesOf_are l (lead + n)
  | .sum _ _ :: l, _ => ⟨_, rfl, shapesOf_are l 0⟩
  | .batch rows :: l, _ => ⟨_, _, rfl, Or.inl ⟨rows, rfl⟩, shapesOf_are l 0⟩
  | .point n :: l, _ => ⟨_, _, rfl, Or.inr ⟨n, rfl⟩, shapesOf_are l 0⟩

/-- **The row's entries are the verifier's**, at every set of the planner's numbers. No premise. -/
theorem shapes_are_script (x : OnBytes.Params.AttentionRounds) :
    EntriesAre (shapes x) (entriesOf 0 (script x)) := shapesOf_are _ 0

/-! ## 2 The counts -/

/-- How many scalars each round of a part sends. -/
def sentOf : PartShape → List Nat
  | .sum k => scalarsOf k
  | .one n => [n]

theorem sentOf_length_of : ∀ (st : List Stage) (lead : Nat), ∀ s ∈ shapesOf lead st,
    (sentOf s).length = s.rounds
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, s, h => sentOf_length_of l (lead + n) s h
  | .sum vs e :: l, lead, s, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [sentOf, scalarsOf, PartShape.rounds, List.length_append, List.length_cons,
        List.length_nil, List.length_map]
      omega
    · exact sentOf_length_of l 0 s h
  | .batch _ :: l, lead, s, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact sentOf_length_of l 0 s h
  | .point _ :: l, lead, s, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact sentOf_length_of l 0 s h

/-- A part of the row sends in as many rounds as `PartShape.rounds` counts. Stated of the row's
parts alone: each sumcheck among them has ends. Of a sumcheck without ends it is false: such a call
sends in two rounds fewer than `PartShape.rounds` counts. -/
theorem sentOf_length (x : OnBytes.Params.AttentionRounds) :
    ∀ s ∈ shapes x, (sentOf s).length = s.rounds := sentOf_length_of _ 0

/-- A sumcheck among the parts has the variables of a sumcheck among the stages. -/
theorem sum_of_stage : ∀ (st : List Stage) (lead : Nat) (k : Call),
    PartShape.sum k ∈ shapesOf lead st → ∃ e, Stage.sum k.vs e ∈ st
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, k, h =>
    (sum_of_stage l (lead + n) k h).imp fun _ h => List.mem_cons_of_mem _ h
  | .sum vs e :: l, lead, k, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
      exact ⟨e, List.mem_cons_self⟩
    · exact (sum_of_stage l 0 k h).imp fun _ h => List.mem_cons_of_mem _ h
  | .batch _ :: l, lead, k, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact (sum_of_stage l 0 k h).imp fun _ h => List.mem_cons_of_mem _ h
  | .point _ :: l, lead, k, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact (sum_of_stage l 0 k h).imp fun _ h => List.mem_cons_of_mem _ h

/-- Every variable of a stage that is a sumcheck has at least two coefficients. -/
def Stage.Two : Stage → Prop
  | .sum vs _ => ∀ v ∈ vs, 2 ≤ v.d
  | _ => True

theorem products_two (n m : Nat) : Stage.Two (products n m) := by
  intro v hv
  rw [List.eq_of_mem_replicate hv]
  exact Nat.le.step (Nat.le.step Nat.le.refl)

theorem script_two (x : OnBytes.Params.AttentionRounds) : ∀ st ∈ script x, Stage.Two st := by
  intro st h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · rw [List.eq_of_mem_replicate h]
      trivial
    · obtain ⟨u, _, hu⟩ := List.mem_flatMap.1 h
      rcases List.mem_cons.1 hu with rfl | hu
      · trivial
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact products_two _ _
        · cases hu
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals first
      | trivial
      | exact products_two _ _
      | (intro v hv
         obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
         show 2 ≤ d
         rcases List.mem_append.1 hd with hd | hd
         · rcases List.mem_append.1 hd with hd | hd
           · rw [List.eq_of_mem_replicate hd]
             omega
           · rw [List.eq_of_mem_replicate hd]
             omega
         · rw [List.eq_of_mem_replicate hd]
           omega)

/-- **Every variable of every sumcheck of the row has at least two coefficients**, at every set of
the planner's numbers. No premise. -/
theorem shapes_two (x : OnBytes.Params.AttentionRounds) :
    ∀ k, PartShape.sum k ∈ shapes x → ∀ v ∈ k.vs, 2 ≤ v.d := by
  intro k hk
  obtain ⟨e, he⟩ := sum_of_stage _ 0 k hk
  exact script_two x _ he

/-! ## 3 What the declared rounds state -/

/-- Of each entry: the message's bytes, the answers, the roots. -/
theorem entriesAre_nums : ∀ (L : List PartShape) (es : List Fmt.Entry), EntriesAre L es →
    es.map (fun e => (e.msg, e.answers, e.roots)) =
      (L.flatMap sentOf).map fun n => (24 * n, 0, 0)
  | [], _, h => by
    rw [show _ = [] from h]
    rfl
  | .sum k :: L, _, ⟨es', h, h'⟩ => by
    rw [h, List.map_append, entries_nums, entriesAre_nums L es' h', List.flatMap_cons,
      List.map_append]
    rfl
  | .one n :: L, _, ⟨e, es', h, ho, h'⟩ => by
    rw [h, List.map_cons, entriesAre_nums L es' h', List.flatMap_cons]
    rcases ho with ⟨rows, rfl⟩ | ⟨k, rfl⟩ <;> rfl

/-- The same of the verifier's declared rounds: the work bits are no part of it. -/
theorem rounds_nums (p : Par) :
    (rounds p).map (fun r => (r.entry.msg, r.entry.answers, r.entry.roots)) =
      ((shapes p.own).flatMap sentOf).map fun n => (24 * n, 0, 0) := by
  rw [← entriesAre_nums _ _ (shapes_are_script p.own)]
  unfold rounds
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  show ((if e.drawE == 0 then e else { e with work := p.work }).msg,
    (if e.drawE == 0 then e else { e with work := p.work }).answers,
    (if e.drawE == 0 then e else { e with work := p.work }).roots) = _
  split <;> rfl

/-- The verifier declares one round for each of the parts' rounds. -/
theorem rounds_length (p : Par) : (rounds p).length = ((shapes p.own).flatMap sentOf).length := by
  have h := congrArg List.length (rounds_nums p)
  rwa [List.length_map, List.length_map] at h

/-- **The declared rounds state just the parts' scalars, round by round, and no oracle message.**
No premise. -/
theorem rounds_stated (p : Par) :
    StatedBy ((shapes p.own).flatMap sentOf) ((rounds p).zip ((rounds p).map fun _ => [])) := by
  refine statedBy_nums _ _ ?_ fun r hr => ?_
  · rw [← rounds_nums p]
    exact map_zip_fst (fun r : Fmt.DeclaredRound => (r.entry.msg, r.entry.answers, r.entry.roots)) _ _
      (by rw [List.length_map])
  · obtain ⟨_, h⟩ := List.of_mem_zip hr
    obtain ⟨_, _, h⟩ := List.mem_map.1 h
    exact h.symm

/-- No round reads a stored table or opens a tree. -/
theorem rounds_read_nothing (p : Par) : ∀ r ∈ rounds p, r.stored = [] ∧ r.opens = [] := by
  intro r hr
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr
  exact ⟨rfl, rfl⟩

/-- No entry has a root or an answer, and each message is whole scalars. -/
theorem rounds_plain (p : Par) :
    ∀ r ∈ rounds p, r.entry.roots = 0 ∧ r.entry.answers = 0 ∧ 24 ∣ r.entry.msg := by
  intro r hr
  have h : (r.entry.msg, r.entry.answers, r.entry.roots) ∈
      (rounds p).map (fun r => (r.entry.msg, r.entry.answers, r.entry.roots)) :=
    List.mem_map.2 ⟨r, hr, rfl⟩
  rw [rounds_nums] at h
  obtain ⟨n, _, hn⟩ := List.mem_map.1 h
  rw [Prod.mk.injEq, Prod.mk.injEq] at hn
  exact ⟨hn.2.2.symm, hn.2.1.symm, ⟨n, hn.1.symm⟩⟩

/-! ## 4 The cut -/

/-- **The cut adds up to the verifier's number of rounds.** No premise. -/
theorem cut_sum (p : Par) : (cut p.own).sum = (rounds p).length := by
  rw [rounds_length, List.length_flatMap]
  unfold cut
  exact congrArg List.sum
    (List.map_congr_left fun s hs => (sentOf_length p.own s hs).symm)

theorem firstOf_zero (x : OnBytes.Params.AttentionRounds) : H2K5.Honest.firstOf x 0 = 0 := rfl

/-- A part's first round stands behind the part in front of it. Beyond the row the number stays. -/
theorem firstOf_succ (x : OnBytes.Params.AttentionRounds) (q : Nat) :
    H2K5.Honest.firstOf x (q + 1) = H2K5.Honest.firstOf x q + (cut x).getD q 0 := by
  unfold H2K5.Honest.firstOf
  rw [List.take_add_one, List.foldl_append, List.getD_eq_getElem?_getD]
  cases (cut x)[q]? <;> rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.shapesOf_are
#print axioms ProofFile.Honest.K5.shapes_are_script
#print axioms ProofFile.Honest.K5.sentOf_length_of
#print axioms ProofFile.Honest.K5.sentOf_length
#print axioms ProofFile.Honest.K5.sum_of_stage
#print axioms ProofFile.Honest.K5.products_two
#print axioms ProofFile.Honest.K5.script_two
#print axioms ProofFile.Honest.K5.shapes_two
#print axioms ProofFile.Honest.K5.entriesAre_nums
#print axioms ProofFile.Honest.K5.rounds_nums
#print axioms ProofFile.Honest.K5.rounds_length
#print axioms ProofFile.Honest.K5.rounds_stated
#print axioms ProofFile.Honest.K5.rounds_read_nothing
#print axioms ProofFile.Honest.K5.rounds_plain
#print axioms ProofFile.Honest.K5.cut_sum
#print axioms ProofFile.Honest.K5.firstOf_zero
#print axioms ProofFile.Honest.K5.firstOf_succ
