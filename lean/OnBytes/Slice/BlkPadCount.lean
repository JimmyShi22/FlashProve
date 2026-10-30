-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkPadCount.lean: the numbers of keys of a lookup of a key file's first chain: all, at
places of padding, at covered places.

The block of OnBytes/Iop/Lkp.lean counts: the counts that the prover sends add up to the number of
all keys less the number of keys at places of padding (`Lkp.Public.allKeys`, `Lkp.paddingCount`),
and the public factor has the second number as its exponent. `Wf.lookupOf` (OnBytes/Iop/Wf.lean)
makes the padding from the parts' runs: every place that no run covers. This file says what these
numbers are for such a lookup, from the program's public tests (`Wf.lookupOk`, `Wf.fitsMatrix`).

A place is 2 ^ kCol keys. In a part of 2 ^ logPlaces places whose runs rise without overlap, the
places in the gaps between the runs and the places of the runs are all places (`gaps_add_runs`). So
the keys at places of padding and the keys at covered places are all keys (`padding_add_covered`).
All keys are fewer than 2 to the number of real planes, which is at most 62 (`allKeys_lt`); so the
number that the program writes as the target of the counts' row is read as itself
(`read_countTarget`), and it is below the field's prime.

Main definitions: `gapPlaces`, `runPlaces`, `coveredKeys`.
Main theorems: `gaps_add_runs`, `paddingCount_eq`, `allKeys_eq`, `padding_add_covered`,
`paddingCount_le`, `allKeys_sub`, `allKeys_lt`, `allKeys_lt_p`, `read_countTarget`, `paddingKey_lt`,
`rows_planes_le`.

Not claimed. Nothing on which keys stand at which places (OnBytes/Slice/KeyLeavesRuns.lean has
that). Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkTableRead

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Slice.Leaves (gaps runsOk_cons paddingFrom_eq runsOk_of read_natE)

/-- The number of places in the gaps between the runs, from the place u on, below N. -/
def gapPlaces (N u : ℕ) (rs : List WfRun) : ℕ := ((gaps N u rs).map fun g => g.2 - g.1).sum

/-- The number of places that the runs cover. -/
def runPlaces (rs : List WfRun) : ℕ := (rs.map (·.places)).sum

/-- The number of keys at covered places. -/
def coveredKeys (kCol : ℕ) (l : WfLookup) : ℕ :=
  (l.parts.map fun p => runPlaces p.runs * 2 ^ kCol).sum

/-- The places in the gaps and the places of the runs are all places from u on. -/
theorem gaps_add_runs (lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ), u ≤ 2 ^ lp →
    Wf.runsOk lp u rs = true → gapPlaces (2 ^ lp) u rs + runPlaces rs = 2 ^ lp - u
  | [], u, _, _ => by simp [gapPlaces, runPlaces, gaps]
  | r :: rs, u, _, h => by
    obtain ⟨_, h2, h3, h4⟩ := runsOk_cons h
    have ih := gaps_add_runs lp rs (r.firstPlace + r.places) h3 h4
    unfold gapPlaces runPlaces at ih ⊢
    simp only [gaps, List.map_cons, List.sum_cons]
    omega

/-- The keys of the runs of padding that are made from a list of gaps. -/
theorem stretch_lengths (kCol number row : ℕ) : ∀ gs : List (ℕ × ℕ),
    (((gs.flatMap fun g => Wf.stretch kCol number row g.1 g.2).map fun q =>
      (q.length, q.row)).map (·.1)).sum = (gs.map fun g => g.2 - g.1).sum * 2 ^ kCol
  | [] => by simp
  | g :: gs => by
    rw [List.flatMap_cons, List.map_append, List.map_append, List.sum_append,
      stretch_lengths kCol number row gs, List.map_cons, List.sum_cons, Nat.add_mul]
    congr 1
    unfold Wf.stretch
    by_cases hg : g.1 < g.2
    · rw [if_pos hg]
      simp
    · rw [if_neg hg, show g.2 - g.1 = 0 by omega]
      simp

/-- The keys of the padding of the parts from the number k on. -/
theorem padding_parts (kCol row : ℕ) : ∀ (ps : List WfPart) (k : ℕ),
    ((((ps.zipIdx k).flatMap fun x =>
      (Wf.paddingFrom kCol x.2 row x.1.logPlaces 0 x.1.runs #[]).toList).map fun q =>
        (q.length, q.row)).map (·.1)).sum =
      (ps.map fun p => gapPlaces (2 ^ p.logPlaces) 0 p.runs * 2 ^ kCol).sum
  | [], _ => rfl
  | p :: ps, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append, List.map_append, List.sum_append,
      padding_parts kCol row ps (k + 1), List.map_cons, List.sum_cons, paddingFrom_eq]
    congr 1
    exact stretch_lengths kCol k row _

/-- The number of keys at places of padding: the places in the gaps of all parts, 2 ^ kCol keys
each. -/
theorem paddingCount_eq (id : ℕ) (m : Wf.Matrix) (l : WfLookup) :
    Lkp.paddingCount (Wf.lookupOf id m l) =
      (l.parts.map fun p => gapPlaces (2 ^ p.logPlaces) 0 p.runs * 2 ^ m.kCol).sum := by
  unfold Lkp.paddingCount Lkp.paddingList
  have hn : (Wf.lookupOf id m l).keys.filter (·.function.isNone) = [] := rfl
  rw [hn, List.map_nil, List.append_nil]
  exact padding_parts m.kCol l.paddingKey.toNat l.parts 0

/-- The number of all keys: 2 ^ (logPlaces + kCol) for each part. -/
theorem allKeys_eq (id : ℕ) (m : Wf.Matrix) (l : WfLookup) :
    (Wf.lookupOf id m l).allKeys = (l.parts.map fun p => 2 ^ (p.logPlaces + m.kCol)).sum := by
  unfold Lkp.Public.allKeys
  show ((l.parts.map fun p => p.logPlaces + m.kCol).map fun x => 2 ^ x).sum = _
  rw [List.map_map]
  rfl

/-- The keys at places of padding and the keys at covered places are all keys. -/
theorem padding_add_covered (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (hl : Wf.lookupOk Wf.fBits l = true) :
    Lkp.paddingCount (Wf.lookupOf id m l) + coveredKeys m.kCol l =
      (Wf.lookupOf id m l).allKeys := by
  rw [paddingCount_eq, allKeys_eq]
  unfold coveredKeys
  have gen : ∀ ps : List WfPart, (∀ p ∈ ps, Wf.runsOk p.logPlaces 0 p.runs = true) →
      (ps.map fun p => gapPlaces (2 ^ p.logPlaces) 0 p.runs * 2 ^ m.kCol).sum +
        (ps.map fun p => runPlaces p.runs * 2 ^ m.kCol).sum =
        (ps.map fun p => 2 ^ (p.logPlaces + m.kCol)).sum := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      have h1 := gaps_add_runs p.logPlaces p.runs 0 (Nat.zero_le _) (h p List.mem_cons_self)
      have h2 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [Nat.sub_zero] at h1
      have h3 : 2 ^ (p.logPlaces + m.kCol) =
          gapPlaces (2 ^ p.logPlaces) 0 p.runs * 2 ^ m.kCol + runPlaces p.runs * 2 ^ m.kCol := by
        rw [pow_add, ← Nat.add_mul, h1]
      simp only [List.map_cons, List.sum_cons]
      rw [h3]
      omega
  exact gen l.parts fun p hp => runsOk_of hl hp

/-- There are at most as many keys at places of padding as keys. -/
theorem paddingCount_le (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (hl : Wf.lookupOk Wf.fBits l = true) :
    Lkp.paddingCount (Wf.lookupOf id m l) ≤ (Wf.lookupOf id m l).allKeys := by
  have := padding_add_covered id m l hl
  omega

/-- All keys less those at places of padding are the keys at covered places. -/
theorem allKeys_sub (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (hl : Wf.lookupOk Wf.fBits l = true) :
    (Wf.lookupOf id m l).allKeys - Lkp.paddingCount (Wf.lookupOf id m l) =
      coveredKeys m.kCol l := by
  have := padding_add_covered id m l hl
  omega

/-- The keys so far and those of the parts to come can be counted in the planes. -/
theorem partsFit_sum (m : Wf.Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (keys : ℕ),
    keys < 2 ^ Wf.planesOf l → Wf.partsFit m l keys ps = true →
    keys + (ps.map fun p => 2 ^ (p.logPlaces + m.kCol)).sum < 2 ^ Wf.planesOf l
  | [], keys, h, _ => by simpa using h
  | p :: ps, keys, _, h => by
    simp only [Wf.partsFit, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := partsFit_sum m l ps _ h.1.2 h.2
    rw [List.map_cons, List.sum_cons]
    omega

/-- All keys are fewer than 2 to the number of real planes. -/
theorem allKeys_lt (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (hm : Wf.fitsMatrix m l = true) :
    (Wf.lookupOf id m l).allKeys < 2 ^ Wf.planesOf l := by
  rw [allKeys_eq]
  have := partsFit_sum m l l.parts 0 (Nat.two_pow_pos _) hm
  omega

/-- What the program's test on a lookup says of its sizes. -/
theorem lookupOk_sizes {l : WfLookup} (hl : Wf.lookupOk Wf.fBits l = true) :
    Wf.planesOf l ≤ 62 ∧ l.d + Wf.planesOf l < 64 ∧ l.paddingKey.toNat < 2 ^ l.d := by
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1.1.1.1.1.1.1.1.2, hl.1.1.1.1.1.1.1.2, hl.1.1.2⟩

/-- All keys are fewer than 2 ^ 62. -/
theorem allKeys_lt_two (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true) :
    (Wf.lookupOf id m l).allKeys < 2 ^ 62 :=
  lt_of_lt_of_le (allKeys_lt id m l hm)
    (Nat.pow_le_pow_right (by decide) (lookupOk_sizes hl).1)

/-- All keys are fewer than the field's prime. -/
theorem allKeys_lt_p (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (hl : Wf.lookupOk Wf.fBits l = true)
    (hm : Wf.fitsMatrix m l = true) : (Wf.lookupOf id m l).allKeys < Cb.Gl.p :=
  lt_trans (allKeys_lt_two id m l hl hm) (by decide)

/-- The target of the counts' row is read as the number of keys at covered places. -/
theorem read_countTarget (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true) :
    readE (Lkp.natE ((Wf.lookupOf id m l).allKeys - Lkp.paddingCount (Wf.lookupOf id m l))) =
      ((coveredKeys m.kCol l : ℕ) : GE) := by
  have h1 := allKeys_lt_two id m l hl hm
  rw [read_natE _ (by
    have : (2 : ℕ) ^ 62 < 2 ^ 64 := by decide
    omega), allKeys_sub id m l hl]

/-- A place of padding holds a row of the table. -/
theorem paddingKey_lt {l : WfLookup} (hl : Wf.lookupOk Wf.fBits l = true) :
    l.paddingKey.toNat < 2 ^ l.d := (lookupOk_sizes hl).2.2

/-- The table's rows times 2 to the number of real planes are at most the field's prime. -/
theorem rows_planes_le {l : WfLookup} (hl : Wf.lookupOk Wf.fBits l = true) :
    2 ^ l.d * 2 ^ Wf.planesOf l ≤ Cb.Gl.p := by
  rw [← pow_add]
  exact le_trans (Nat.pow_le_pow_right (by decide)
    (by have := (lookupOk_sizes hl).2.1; omega : l.d + Wf.planesOf l ≤ 63)) (by decide)

end OnBytes.Slice.Planes
