-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryBlocksRecord.lean: the proof library's number of blocks of a verifier's message
at the descriptions typed for an entry's chain at the setting "record with work": 140 at full size,
99 at the small files.

The library makes a protocol from a description of a chain; `Run.PQ.kOf S` is the greatest number of
hash blocks from which a round's verifier's message is drawn (Run/PlanQRun.lean). `blocksMost` is
the same maximum by the format's own count, `Fmt.blocksFor` of `Fmt.wordsAtMost`, over a list of
rounds. The library's data of the rounds keep each round's entry and kind (`foldl_rdsFrom`), and by
the library's `Run.planDraws_law` a round's sampler reads that many blocks where its positions are
drawn in a length of at most 2 ^ 64; so `Run.PQ.kOf S` is `blocksMost S.rounds` (`foldl_max_congr`,
`kOf_eq`). By evaluations in Lean's kernel at the typed rounds `recordRounds`
(OnBytes/Params/EntryDryRecord.lean) and `smallRecordRounds`
(OnBytes/Params/EntryDryRecordSmall.lean): all lengths are at most 2 ^ 64, and the most blocks are
140 and 99 (`record_blocks`, `small_record_blocks`). So at the description of an entry's chain, at
every statement, the library's number is 140 at full size and 99 at the small files (`record_kOf`,
`small_record_kOf`). The same round by round: the library's data keep the rounds' entries and kinds
as lists (`rdsFrom_map`), a member is at most the fold of maxima (`le_foldl_max`), so every round's
sampler reads at most `blocksMost` blocks (`blocks_le_most`): at most 140 and 99
(`record_blocks_le`, `small_record_blocks_le`). Two values of `Fmt.blocksFor` stand beside them
(`record_seed_blocks`): 140 and 95; their arguments have the form of the right side of `seedBS_b`
(OnBytes/Slice/SeedBias.lean, which this file does not import) at one answer and the cubes 29 and
19.

Main definition: `blocksMost`.
Main theorems: `foldl_rdsFrom`, `foldl_max_congr`, `kOf_eq`, `rdsFrom_map`, `le_foldl_max`,
`blocks_le_most`, `record_blocks`, `small_record_blocks`, `record_kOf`, `small_record_kOf`,
`record_blocks_le`, `small_record_blocks_le`, `record_seed_blocks`.
What is not claimed: that the seeds of a table's record are drawn from 140 or 95 blocks: no sampler
of seeds is named here. Which round has the most blocks. Nothing on a key's or a proof's chains.
What the heads of the two files of typed rounds do not claim. For proofs only; the program, that is
the Lean port built from OnBytes/, does not import this file.

-/
import Run.PlanQRun
import OnBytes.Tie.Limits
import OnBytes.Params.EntryDryRecord
import OnBytes.Params.EntryDryRecordSmall

set_option autoImplicit false

namespace OnBytes.Params

/-- The greatest number of blocks that a round of the list draws, by the format's count of words. -/
def blocksMost (rs : List Fmt.Round) : ℕ :=
  rs.foldl (fun a r => max a (Fmt.blocksFor (Fmt.wordsAtMost r.entry r.kind))) 0

/-- A fold over the library's data of the rounds that reads entry and kind alone is the fold over
the rounds. -/
theorem foldl_rdsFrom (S : Fmt.Spec) (f : Fmt.Entry → Fmt.Kind → ℕ) :
    ∀ (rs : List Fmt.Round) (sent a : ℕ),
      (Run.PQ.rdsFrom S sent rs).foldl (fun a d => max a (f d.entry d.kind)) a =
        rs.foldl (fun a r => max a (f r.entry r.kind)) a
  | [], _, _ => rfl
  | r :: rs, sent, a => by
    show (Run.PQ.rdsFrom S (sent + r.entry.roots) rs).foldl _ (max a (f r.entry r.kind)) = _
    exact foldl_rdsFrom S f rs _ _

/-- Two folds of maxima agree if the functions agree on the list's members. -/
theorem foldl_max_congr {f g : Fmt.Round → ℕ} :
    ∀ (rs : List Fmt.Round) (a : ℕ), (∀ r ∈ rs, f r = g r) →
      rs.foldl (fun a r => max a (f r)) a = rs.foldl (fun a r => max a (g r)) a
  | [], _, _ => rfl
  | r :: rs, a, h => by
    show rs.foldl _ (max a (f r)) = rs.foldl _ (max a (g r))
    rw [h r (List.mem_cons_self ..)]
    exact foldl_max_congr rs _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **The library's number of blocks of a verifier's message, for a description whose rounds draw
positions in lengths of at most 2 ^ 64, is `blocksMost` of its rounds.** -/
theorem kOf_eq (S : Fmt.Spec) (h : ∀ r ∈ S.rounds, r.entry.logN ≤ 64) :
    Run.PQ.kOf S = blocksMost S.rounds := by
  unfold Run.PQ.kOf Run.PQ.kMax Run.PQ.rds blocksMost
  rw [foldl_rdsFrom S (fun e k => (Run.bsRound S.plan.field e k).b)]
  exact foldl_max_congr S.rounds 0 fun r hr =>
    (Run.planDraws_law S.plan.field r.entry r.kind (h r hr)).2

/-- The library's data of the rounds keep the rounds' entries and kinds, as lists. -/
theorem rdsFrom_map (S : Fmt.Spec) : ∀ (rs : List Fmt.Round) (sent : ℕ),
    (Run.PQ.rdsFrom S sent rs).map (fun d => (d.entry, d.kind)) =
      rs.map fun r => (r.entry, r.kind)
  | [], _ => rfl
  | r :: rs, sent => by
    show (r.entry, r.kind) :: (Run.PQ.rdsFrom S (sent + r.entry.roots) rs).map _ = _
    rw [rdsFrom_map S rs]
    rfl

/-- The start and every member's value are at most the fold of maxima. -/
theorem le_foldl_max {f : Fmt.Round → ℕ} : ∀ (rs : List Fmt.Round) (a : ℕ),
    a ≤ rs.foldl (fun a r => max a (f r)) a ∧
      ∀ r ∈ rs, f r ≤ rs.foldl (fun a r => max a (f r)) a
  | [], a => ⟨le_rfl, fun _ h => by cases h⟩
  | x :: rs, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max rs (max a (f x))
    refine ⟨(le_max_left _ _).trans h1, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (le_max_right _ _).trans h1
    · exact h2 r hr

/-- **Every round's sampler reads at most `blocksMost` blocks**, for a description whose rounds draw
positions in lengths of at most 2 ^ 64. -/
theorem blocks_le_most (S : Fmt.Spec) (h : ∀ r ∈ S.rounds, r.entry.logN ≤ 64) :
    ∀ d ∈ Run.PQ.rds S, (Run.bsRound S.plan.field d.entry d.kind).b ≤ blocksMost S.rounds := by
  intro d hd
  have hm : (d.entry, d.kind) ∈ S.rounds.map fun r => (r.entry, r.kind) := by
    rw [← rdsFrom_map S S.rounds 0]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨r, hr, e⟩ := List.mem_map.mp hm
  have e1 : r.entry = d.entry := congrArg Prod.fst e
  have e2 : r.kind = d.kind := congrArg Prod.snd e
  rw [← e1, ← e2, (Run.planDraws_law S.plan.field r.entry r.kind (h r hr)).2]
  exact (le_foldl_max (f := fun r => Fmt.blocksFor (Fmt.wordsAtMost r.entry r.kind))
    S.rounds 0).2 r hr

/-- At the full-size typed rounds: every length is at most 2 ^ 64, and the most blocks are 140. -/
theorem record_blocks : ((recordRounds.map (·.1)).all fun r => decide (r.entry.logN ≤ 64)) = true ∧
    blocksMost (recordRounds.map (·.1)) = 140 := by decide +kernel

/-- At the small typed rounds: every length is at most 2 ^ 64, and the most blocks are 99. -/
theorem small_record_blocks :
    ((smallRecordRounds.map (·.1)).all fun r => decide (r.entry.logN ≤ 64)) = true ∧
      blocksMost (smallRecordRounds.map (·.1)) = 99 := by decide +kernel

/-- **The library's number of blocks at the full-size description of an entry's chain, at every
statement, is 140.** -/
theorem record_kOf (st : ByteArray) :
    Run.PQ.kOf (Tie.inFile (entrySpecOf recordRead recordRounds st).base) = 140 := by
  rw [kOf_eq _ (fun r hr => by
    have := List.all_eq_true.mp record_blocks.1 r hr
    simpa using this)]
  exact record_blocks.2

/-- **The like at the small description: 99.** -/
theorem small_record_kOf (st : ByteArray) :
    Run.PQ.kOf (Tie.inFile (entrySpecOf smallRecordRead smallRecordRounds st).base) = 99 := by
  rw [kOf_eq _ (fun r hr => by
    have := List.all_eq_true.mp small_record_blocks.1 r hr
    simpa using this)]
  exact small_record_blocks.2

/-- **At the full-size description every round's sampler reads at most 140 blocks**, at every
statement. -/
theorem record_blocks_le (st : ByteArray) :
    ∀ d ∈ Run.PQ.rds (Tie.inFile (entrySpecOf recordRead recordRounds st).base),
      (Run.bsRound .two d.entry d.kind).b ≤ 140 := by
  intro d hd
  have h := blocks_le_most (Tie.inFile (entrySpecOf recordRead recordRounds st).base)
    (fun r hr => by
      have := List.all_eq_true.mp record_blocks.1 r hr
      simpa using this) d hd
  exact h.trans (le_of_eq record_blocks.2)

/-- **The like at the small description: 99.** -/
theorem small_record_blocks_le (st : ByteArray) :
    ∀ d ∈ Run.PQ.rds (Tie.inFile (entrySpecOf smallRecordRead smallRecordRounds st).base),
      (Run.bsRound .two d.entry d.kind).b ≤ 99 := by
  intro d hd
  have h := blocks_le_most (Tie.inFile (entrySpecOf smallRecordRead smallRecordRounds st).base)
    (fun r hr => by
      have := List.all_eq_true.mp small_record_blocks.1 r hr
      simpa using this) d hd
  exact h.trans (le_of_eq small_record_blocks.2)

/-- Two values of the format's count of blocks: at 1 * (29 * 18 + 36) words 140, at
1 * (19 * 18 + 36) words 95. -/
theorem record_seed_blocks :
    Fmt.blocksFor (1 * (29 * 18 + 36)) = 140 ∧ Fmt.blocksFor (1 * (19 * 18 + 36)) = 95 := by
  decide

end OnBytes.Params

#print axioms OnBytes.Params.foldl_rdsFrom
#print axioms OnBytes.Params.foldl_max_congr
#print axioms OnBytes.Params.kOf_eq
#print axioms OnBytes.Params.rdsFrom_map
#print axioms OnBytes.Params.le_foldl_max
#print axioms OnBytes.Params.blocks_le_most
#print axioms OnBytes.Params.record_blocks_le
#print axioms OnBytes.Params.small_record_blocks_le
#print axioms OnBytes.Params.record_blocks
#print axioms OnBytes.Params.small_record_blocks
#print axioms OnBytes.Params.record_kOf
#print axioms OnBytes.Params.small_record_kOf
#print axioms OnBytes.Params.record_seed_blocks
