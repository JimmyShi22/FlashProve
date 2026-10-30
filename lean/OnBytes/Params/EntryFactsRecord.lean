-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryFactsRecord.lean: closed facts on the rounds typed for an entry's chain at the
setting "record with work", at both sizes; and each count's share, with its round's work, on these
very rounds.

`recordRounds` (OnBytes/Params/EntryDryRecord.lean) and `smallRecordRounds`
(OnBytes/Params/EntryDryRecordSmall.lean) are the rounds that the dry run of the link's block notes,
each with the stored trees that it opens. By evaluations in Lean's kernel: the first stored tree has
the depth of the typed table's code, 32 or 23 (`record_depth`, `small_record_depth`); all stored
trees have that depth and salts of the typed table's length (`record_stored_all`,
`small_record_stored_all`); within a round all stored openings have one shape and one length of salt
(`record_pair_shapes`); there are two in all, of the statement's items 0 and 1, both in the fourth
round, each with its own part of that round's 124 or 102 draws (`record_pair_places`,
`record_pair_round`); the chain's own trees 0 to 4, at the small size 0 to 2, are opened once each,
and a round's own list of openings holds no other tree (`record_opens_own`, `record_opens_all_own`);
no round is sealed (`record_no_seal`); no round sends more than one root, and five or three are sent
in all (`record_roots`); the typed plans are over the second field (`record_field`); no round has
more than 64 bits of work (`record_work`); and the rounds' entries are the typed plans' entries but
for the first, in order (`record_rounds_entries`). The last ties the plan's rounds, of which
OnBytes/Params/HoldsLaws.lean speaks, to the dry run's. So, for any bias (1 + x) ^ b of the record's
seeds with 0 ≤ x and 52 b x ≤ 1 (at the small lines 228 b x ≤ 1): each number of `recordCounts b x`
but the first, divided by 2 to the work of its round in `recordRounds`, is at most 2 ^ -128, place
by place, 41 rounds; the like for `smallRecordCounts` and `smallRecordRounds`, 24 rounds
(`forall₂_tail`, `record_rounds_share`, `small_record_rounds_share`). The bias stands in the first
number alone, so the same holds at every b and x (`record_rounds_share_any`,
`small_record_rounds_share_any`).

Main theorems: `record_depth`, `small_record_depth`, `record_stored_all`, `small_record_stored_all`,
`record_pair_shapes`, `record_pair_places`, `record_pair_round`, `record_opens_own`,
`record_opens_all_own`, `record_no_seal`, `record_roots`, `record_field`, `record_work`,
`record_rounds_entries`, `forall₂_tail`, `record_rounds_share`, `small_record_rounds_share`,
`record_rounds_share_any`, `small_record_rounds_share_any`.
What is not claimed: what the heads of OnBytes/Params/HoldsLaws.lean,
OnBytes/Params/EntryCoveredRecord.lean and the two files of typed rounds do not claim: above all
that a number of the two lists bounds a prover's chance, and that work is worth its bits. That a
count in whole numbers of a round's bad values is at most the number here times the number of the
round's values: no set of values is named here. That the rounds are the same at another digest: both
lists are the dry run's under parameter bytes with the typed digests `recordCfg` and
`smallRecordCfg`, and no law here carries them to the digest of other public files. For proofs only;
the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryBlocksRecord
import OnBytes.Params.HoldsLaws

set_option autoImplicit false

namespace OnBytes.Params

/-- At the full-size typed rounds the first stored tree that a round opens has the depth of the
typed table's code, 32. -/
theorem record_depth :
    ((recordRounds.map (·.2)).flatten.head?.map (·.sh.a)).getD 0 = recordLink.table.code.logN ∧
      recordLink.table.code.logN = 32 := by decide +kernel

/-- The like at the small typed rounds: 23. -/
theorem small_record_depth :
    ((smallRecordRounds.map (·.2)).flatten.head?.map (·.sh.a)).getD 0 =
        smallRecordLink.table.code.logN ∧
      smallRecordLink.table.code.logN = 23 := by decide +kernel

/-- All stored trees that the full-size rounds open have the depth 32, and salts of the typed
table's length. -/
theorem record_stored_all : ((recordRounds.map (·.2)).flatten.all fun x =>
    decide (x.sh.a = 32) && decide (x.salt = recordLink.table.saltBytes)) = true := by
  decide +kernel

/-- The like at the small typed rounds. -/
theorem small_record_stored_all : ((smallRecordRounds.map (·.2)).flatten.all fun x =>
    decide (x.sh.a = 23) && decide (x.salt = smallRecordLink.table.saltBytes)) = true := by
  decide +kernel

/-- Within a round, at both sizes, all stored openings have one shape and one length of salt. Of a
round with fewer than two stored openings this says nothing. -/
theorem record_pair_shapes :
    (recordRounds.all fun r => r.2.all fun x => r.2.all fun y =>
      decide (x.sh = y.sh) && decide (x.salt = y.salt)) = true ∧
    (smallRecordRounds.all fun r => r.2.all fun x => r.2.all fun y =>
      decide (x.sh = y.sh) && decide (x.salt = y.salt)) = true := by decide +kernel

/-- One typed round at each size opens stored trees: two openings, of the statement's items 0 and 1,
with 62 and 62 draws from the draws 0 and 62 on; at the small size 51 and 51, from 0 and 51 on. -/
theorem record_pair_places :
    (recordRounds.map (·.2)).flatten.map (fun x => (x.item, x.lo, x.count)) =
        [(0, 0, 62), (1, 62, 62)] ∧
      (smallRecordRounds.map (·.2)).flatten.map (fun x => (x.item, x.lo, x.count)) =
        [(0, 0, 51), (1, 51, 51)] := by decide +kernel

/-- The stored openings round by round: two in the fourth round, none elsewhere; that round draws
124 positions, at the small size 102. -/
theorem record_pair_round :
    recordRounds.map (·.2.length) = List.replicate 3 0 ++ 2 :: List.replicate 37 0 ∧
      (recordRounds.map (·.1.entry.poss))[3]? = some 124 ∧
      smallRecordRounds.map (·.2.length) = List.replicate 3 0 ++ 2 :: List.replicate 20 0 ∧
      (smallRecordRounds.map (·.1.entry.poss))[3]? = some 102 := by decide +kernel

/-- The chain's own trees that the typed rounds open, in order: each number once. -/
theorem record_opens_own :
    (recordRounds.flatMap fun r => r.1.opens.filterMap Run.PQ.ownNo) = [0, 1, 2, 3, 4] ∧
      (smallRecordRounds.flatMap fun r => r.1.opens.filterMap Run.PQ.ownNo) = [0, 1, 2] := by
  decide +kernel

/-- Every opening in a typed round's own list is of a tree of the chain's own. -/
theorem record_opens_all_own :
    (recordRounds.all fun r => r.1.opens.all fun o => (Run.PQ.ownNo o).isSome) = true ∧
      (smallRecordRounds.all fun r => r.1.opens.all fun o => (Run.PQ.ownNo o).isSome) = true := by
  decide +kernel

/-- No typed round is sealed. -/
theorem record_no_seal :
    (recordRounds.all fun r => decide (r.1.kind ≠ .sealed)) = true ∧
      (smallRecordRounds.all fun r => decide (r.1.kind ≠ .sealed)) = true := by decide +kernel

/-- No typed round sends more than one root; five and three roots are sent in all. -/
theorem record_roots :
    (recordRounds.all fun r => decide (r.1.entry.roots ≤ 1)) = true ∧
      (recordRounds.map (·.1.entry.roots)).sum = 5 ∧
      (smallRecordRounds.all fun r => decide (r.1.entry.roots ≤ 1)) = true ∧
      (smallRecordRounds.map (·.1.entry.roots)).sum = 3 := by decide +kernel

/-- The typed plans are over the second field. -/
theorem record_field : recordPlan.field = .two ∧ smallRecordPlan.field = .two := ⟨rfl, rfl⟩

/-- No typed round has more than 64 bits of work. -/
theorem record_work : ((recordRounds.map (·.1)).all fun r => decide (r.entry.work ≤ 64)) = true ∧
    ((smallRecordRounds.map (·.1)).all fun r => decide (r.entry.work ≤ 64)) = true := by
  decide +kernel

/-- The entries of the typed rounds are the typed plans' entries but for the first, in order. -/
theorem record_rounds_entries : recordRounds.map (·.1.entry) = recordPlan.entries.tail ∧
    smallRecordRounds.map (·.1.entry) = smallRecordPlan.entries.tail := by decide +kernel

/-- A relation that holds place by place holds so of the tails. -/
theorem forall₂_tail {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → List.Forall₂ R a.tail b.tail
  | _, _, .nil => .nil
  | _, _, .cons _ t => t

/-- **At the full-size lines each count but the record's, divided by 2 to the work of its round as
the dry run notes it, is at most 2 ^ -128**: the 41 rounds of the entry's chain, in order. For any
bias of the record's seeds with 0 ≤ x and 52 b x ≤ 1. -/
theorem record_rounds_share {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 52 * (b : ℝ) * x ≤ 1) :
    List.Forall₂ (fun (c : ℝ) (r : Fmt.Round × List Fmt.Stored) =>
        ENNReal.ofReal c / 2 ^ r.1.entry.work ≤ ((2 : ENNReal) ^ 128)⁻¹)
      (recordCounts b x).tail recordRounds := by
  obtain ⟨P, hP, h⟩ := record_entry_share hx hx1
  obtain ⟨P', hP', hp, _⟩ := record_sized
  have e : P' = P := by
    have h' := hP'.symm.trans hP
    simpa using h'
  subst e
  have he : P'.rounds.map (·.entry) = recordPlan.entries := congrArg Fmt.Plan.entries hp
  have h1 : List.Forall₂ (fun (c : ℝ) (y : Fmt.Entry) =>
      ENNReal.ofReal c / 2 ^ y.work ≤ ((2 : ENNReal) ^ 128)⁻¹) (recordCounts b x)
      (P'.rounds.map (·.entry)) :=
    (List.forall₂_map_right_iff (f := fun r : PlanRound => r.entry)
      (R := fun (c : ℝ) (y : Fmt.Entry) =>
        ENNReal.ofReal c / 2 ^ y.work ≤ ((2 : ENNReal) ^ 128)⁻¹)).mpr h
  rw [he] at h1
  have h2 := forall₂_tail h1
  rw [← record_rounds_entries.1] at h2
  exact (List.forall₂_map_right_iff (f := fun r : Fmt.Round × List Fmt.Stored => r.1.entry)
    (R := fun (c : ℝ) (y : Fmt.Entry) =>
      ENNReal.ofReal c / 2 ^ y.work ≤ ((2 : ENNReal) ^ 128)⁻¹)).mp h2

/-- **At the small lines each count but the record's, divided by 2 to the work of its round as the
dry run notes it, is at most 2 ^ -128**: the 24 rounds of the entry's chain, in order. For any bias
of the record's seeds with 0 ≤ x and 228 b x ≤ 1. -/
theorem small_record_rounds_share {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 228 * (b : ℝ) * x ≤ 1) :
    List.Forall₂ (fun (c : ℝ) (r : Fmt.Round × List Fmt.Stored) =>
        ENNReal.ofReal c / 2 ^ r.1.entry.work ≤ ((2 : ENNReal) ^ 128)⁻¹)
      (smallRecordCounts b x).tail smallRecordRounds := by
  obtain ⟨P, hP, h⟩ := small_record_entry_share hx hx1
  obtain ⟨P', hP', hp, _⟩ := small_record_sized
  have e : P' = P := by
    have h' := hP'.symm.trans hP
    simpa using h'
  subst e
  have he : P'.rounds.map (·.entry) = smallRecordPlan.entries := congrArg Fmt.Plan.entries hp
  have h1 : List.Forall₂ (fun (c : ℝ) (y : Fmt.Entry) =>
      ENNReal.ofReal c / 2 ^ y.work ≤ ((2 : ENNReal) ^ 128)⁻¹) (smallRecordCounts b x)
      (P'.rounds.map (·.entry)) :=
    (List.forall₂_map_right_iff (f := fun r : PlanRound => r.entry)
      (R := fun (c : ℝ) (y : Fmt.Entry) =>
        ENNReal.ofReal c / 2 ^ y.work ≤ ((2 : ENNReal) ^ 128)⁻¹)).mpr h
  rw [he] at h1
  have h2 := forall₂_tail h1
  rw [← record_rounds_entries.2] at h2
  exact (List.forall₂_map_right_iff (f := fun r : Fmt.Round × List Fmt.Stored => r.1.entry)
    (R := fun (c : ℝ) (y : Fmt.Entry) =>
      ENNReal.ofReal c / 2 ^ y.work ≤ ((2 : ENNReal) ^ 128)⁻¹)).mp h2

/-- The same without the hypotheses on the bias, which stands in the first number alone. -/
theorem record_rounds_share_any (b : ℕ) (x : ℝ) :
    List.Forall₂ (fun (c : ℝ) (r : Fmt.Round × List Fmt.Stored) =>
        ENNReal.ofReal c / 2 ^ r.1.entry.work ≤ ((2 : ENNReal) ^ 128)⁻¹)
      (recordCounts b x).tail recordRounds :=
  record_rounds_share (b := 0) (x := 0) le_rfl (by norm_num)

/-- The like at the small lines. -/
theorem small_record_rounds_share_any (b : ℕ) (x : ℝ) :
    List.Forall₂ (fun (c : ℝ) (r : Fmt.Round × List Fmt.Stored) =>
        ENNReal.ofReal c / 2 ^ r.1.entry.work ≤ ((2 : ENNReal) ^ 128)⁻¹)
      (smallRecordCounts b x).tail smallRecordRounds :=
  small_record_rounds_share (b := 0) (x := 0) le_rfl (by norm_num)

end OnBytes.Params

#print axioms OnBytes.Params.record_pair_round
#print axioms OnBytes.Params.record_rounds_share_any
#print axioms OnBytes.Params.small_record_rounds_share_any
#print axioms OnBytes.Params.forall₂_tail
#print axioms OnBytes.Params.record_rounds_share
#print axioms OnBytes.Params.small_record_rounds_share
#print axioms OnBytes.Params.record_depth
#print axioms OnBytes.Params.small_record_depth
#print axioms OnBytes.Params.record_stored_all
#print axioms OnBytes.Params.small_record_stored_all
#print axioms OnBytes.Params.record_pair_shapes
#print axioms OnBytes.Params.record_pair_places
#print axioms OnBytes.Params.record_opens_own
#print axioms OnBytes.Params.record_opens_all_own
#print axioms OnBytes.Params.record_no_seal
#print axioms OnBytes.Params.record_roots
#print axioms OnBytes.Params.record_field
#print axioms OnBytes.Params.record_work
#print axioms OnBytes.Params.record_rounds_entries
